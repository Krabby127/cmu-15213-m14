/*
 * mm.c
 * hbovik - Harry Bovik
 *
            --> block ptr
            | 
--┌---------┬----------┬---------┬------
  |         |          |         |
  |  header |   data   |  footer | header ...
  | 8 bytes |          | 8 bytes |
--┴---------┴----------┴---------┴-----

  <-------------size------------->


*/

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <unistd.h>
#include "contracts.h"

#include "mm.h"
#include "memlib.h"


// Create aliases for driver tests
// DO NOT CHANGE THE FOLLOWING!
#ifdef DRIVER
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif

/*
 *  Logging Functions
 *  -----------------
 *  - dbg_printf acts like printf, but will not be run in a release build.
 *  - checkheap acts like mm_checkheap, but prints the line it failed on and
 *    exits if it fails.
 */

#ifndef NDEBUG
#define dbg_printf(...) printf(__VA_ARGS__)
#define checkheap(verbose) do {if (mm_checkheap(verbose)) {  \
                             printf("Checkheap failed on line %d\n", __LINE__);\
                             exit(-1);  \
                        }}while(0)
#else
#define dbg_printf(...)
#define checkheap(...)
#endif

// Macros

/* Word size in bytes */
#define WSIZE       8
/* Memory allignmnet in bytes */
#define ALIGNMENT   WSIZE       
/* expand heap by this, in bytes */
#define CHUNKSIZE   (1<<12)

/* lower bit of header/footer */
#define FREE        0
#define ALLOCED     1

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

/* cast pointer to size_t* */
#define PTR(p) ((size_t*)(p))

/* max value */
#define MAX(x, y)   ((x) > (y) ? (x) : (y))

/*
 *  Helper functions
 *  ----------------
 */

// Get 8 bytes by the pointer
static inline size_t get(const char* ptr) {
    return *PTR(ptr);
}

// Set 8 bytes by the pointer
static inline size_t put(char* ptr, size_t val) {
    return *PTR(ptr) = val;
}

// Align p to a multiple of w bytes
static inline void* align(const void const* p, unsigned char w) {
    return (void*)(((uintptr_t)(p) + (w-1)) & ~(w-1));
}

// Check if the given pointer is 8-byte aligned
static inline int aligned(const void const* p) {
    return align(p, 8) == p;
}

// Return whether the pointer is in the heap.
static int in_heap(const void* p) {
    return p <= mem_heap_hi() && p >= mem_heap_lo();
}


/*
 *  Block Functions
 *  ---------------
 *  TODO: Add your comment describing block functions here.
 *  The functions below act similar to the macros in the book, but calculate
 *  size in multiples of 4 bytes.
 */

// Return the size of the given block bytes
static inline size_t block_size(const char* block) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));
    return get(block - WSIZE) & ~0x7;
}

// Return true if the block is free, false otherwise
static inline size_t is_block_free(const char* block) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));

    return !(get(block - WSIZE) & 0x1);
}

// Mark the given block as free(1)/alloced(0) by marking the header and footer.
static inline void mark_block(char* block, int free, size_t size) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap    (block));

    size_t val = size | free;
    put(block - WSIZE, val);
    put(block + size , val);
}


// Return the header to the previous block
static inline char* block_prev(char* const block) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));

    return block - block_size(block) - 2*WSIZE;
}

// Return the header to the next block
static inline char* block_next(char* const block) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));

    return block + block_size(block) + WSIZE;
}


/*
 *  Malloc Implementation
 *  ---------------------
 *  The following functions deal with the user-facing malloc implementation.
 */

/*
 * Global vars
 */
static char *heap_listp;

/*
 * My helper function headers
 */

static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t bp);
static void put_block(void* bp, size_t size);
/*
 * Initialize: return -1 on error, 0 on success.
 */
int mm_init(void) {
    char* prologue;
    heap_listp = mem_sbrk(4*WSIZE);
    if (heap_listp == (void *)-1) return -1;

    /* allignemnt, size: WSIZE */
    put(heap_listp, 0);

    /* put prologue, size: 2*WSIZE */
    prologue = heap_listp + WSIZE;
    mark_block(prologue, 2*WSIZE, 1);

    /* epilogue, size: WSIZE, alloced*/
    put(prologue + 2*WSIZE, 0x1);

    /* point to the footer of prologue */
    heap_listp += 2*WSIZE;

    if (extend_heap(CHUNKSIZE/ WSIZE) == NULL)
        return -1;
    return 0;
}

/*
 * Extend heap by CHUNKSIZE
 */
static void *extend_heap(size_t words) {
    char *bp;
    size_t size;

    size = words*WSIZE; 
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;
    mark_block(bp, size, FREE);
    put(block_next(bp), 0x1);
    return coalesce(bp);

}

static void *coalesce(void *bp){
    size_t prev_alloc = is_block_free(block_prev(bp));
    size_t next_alloc = is_block_free(block_next(bp));
    size_t size = block_size(bp);

    if (prev_alloc && next_alloc) {
        return bp;
    }

    else if (prev_alloc && !next_alloc) {
        size += block_size(block_next(bp));
        mark_block(bp, size, FREE);
    }

    else if (!prev_alloc && next_alloc) {
        size += block_size(block_prev(bp));
        bp = block_prev(bp);
        mark_block(bp, size, FREE);
    }

    else {
        size += block_size(block_prev(bp)) + 
            block_size(block_next(bp));
        bp = block_prev(bp);
        mark_block(bp, size, FREE);
    }
    return bp;
}

static void* find_fit(size_t size) {
    char* ptr = heap_listp + WSIZE;
    while (ptr != NULL)  {
        if (is_block_free(ptr) && block_size(ptr) >= size) break;
        ptr = block_next(ptr);
    }
    return ptr;
}

static void put_block(void* bp, size_t size){
    size_t old_size = block_size(bp);
    if (size < old_size) {
        char* free = (char*)bp + size + WSIZE;
        mark_block(free, old_size - size, FREE);
    } 
    mark_block(bp, size, ALLOCED);
    checkheap(1);  // Let's make sure the heap is ok!
}
/*
 * malloc
 */
void *malloc (size_t size) {
    checkheap(1);  // Let's make sure the heap is ok!
    size_t asize;
    size_t extendsize;
    char *bp;
    if (size == 0)
        return NULL;

    if (size <= WSIZE)
        asize = 3*WSIZE;
    else
        asize = ALIGN(size + 2*WSIZE); 

    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {
        put_block(bp, asize);
        return bp;
    }

    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;
    put_block(bp, asize);
    checkheap(1);  // Let's make sure the heap is ok!
    return bp;
}

/*
 * free
 */
void free (void *bp) {
    size_t size = block_size(bp);
    mark_block(bp, size, FREE);
    coalesce(bp);
    checkheap(1);  // Let's make sure the heap is ok!
}

/*
 * realloc - you may want to look at mm-naive.c
 */
void *realloc(void *oldptr, size_t size) {
    size_t oldsize;
    void *newptr;

    if (size == 0) {
        free(oldptr);
        return NULL;
    }

    if (oldptr == NULL) {
        return malloc(size);
    }

    newptr = malloc(size);

    if (!newptr) {
        return 0;
    }

    oldsize = block_size(oldptr);
    if (size < oldsize) oldsize = size;
    memcpy(newptr, oldptr, oldsize);

    free(oldptr);

    return newptr;
}

/*
 * calloc - you may want to look at mm-naive.c
 */
void *calloc (size_t nmemb, size_t size) {
    size_t bytes = nmemb * size;
    void* newptr;
    newptr = malloc(bytes);
    memset(newptr, 0, bytes);

    return newptr;
}

// Returns 0 if no errors were found, otherwise returns the error
int mm_checkheap(int verbose) {
    char* ptr = heap_listp + WSIZE;
    size_t size = 0, header = 0, footer = 0;
    int free = 0;
    while (ptr != NULL) {
        if (verbose) {
            printf("[%p+%zu,%s]->",ptr, size, free?"free":"allo");
        }
        if (!aligned(ptr)) {
            printf("Block pointer %p isn't aligned\n", ptr);
            return 1;
        }
        if (!in_heap(ptr)) {
            printf("Block pointer %p isn't in heap\n", ptr);
            return 1;
        }
        size = block_size(ptr);
        free = is_block_free(ptr);
        header = get(ptr - WSIZE);
        footer = get(ptr + size);
        if (header != footer) {
            printf("Header and footer doesn't match: %p\n", ptr );
            return 1;   
        }
        ptr = block_next(ptr);
    }
    return 0;
}
