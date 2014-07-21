/*
 * mm.c
 * Nikita Chepanov
 * nchepano@andrew.cmu.edu
 *
  --> block ptr
  | 
---------------------------------------
  |         |          |         |
  |  header |   data   |  footer | header ...
  | 8 bytes |          | 8 bytes |
----------------------------------------
  <------------block------------->
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
#define DSIZE       16
/* Memory allignmnet in bytes */
#define ALIGNMENT   WSIZE       
/* expand heap by this, in bytes */
#define CHUNKSIZE   (1024*32) 
/* Block minimal size: header + next + prev + footer*/
#define MINSIZE     (4*WSIZE)
/* lower bit of header/footer */
#define FREE        0
#define ALLOCED     1
/* get/put - cast to size_t and set/return value */
#define PUT(ptr, val)   ((*(size_t*)(ptr)) = val)
#define GET(ptr)        (*(size_t*)(ptr))
/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

/* max value */
#define MAX(x, y)   ((x) > (y) ? (x) : (y))

/*
 *  Helper functions
 *  ----------------
 */


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
    return GET(block) & ~0x7;
}

// Return true if the block is free, false otherwise
static inline size_t is_block_free(const char* block) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));

    return !(GET(block) & 0x1);
}

// Get pointer to the next free block
static inline char* next_free(const char* block) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));
    return block + 2*WSIZE;
}


// Get pointer to the prev free block
static inline char* prev_free(const char* block) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));
    return block + WSIZE;
}

// Mark the given block as free(1)/alloced(0) by marking the header and footer.
static inline void mark_block(char* block, size_t size, uint64_t free) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));

    size_t val = size | free;
    PUT(block, val);
    PUT(block + size - WSIZE , val);
}

// For the current block set pointers to the next
// Assuming the block header/footer are set
static inline void mark_prev_free(char* block, void* prev){
    PUT(block + WSIZE, prev);
}

// For the current block set pointers to the prev 
// Assuming the block header/footer are set
static inline void mark_next_free(char* block, void* next){
    PUT(block + DSIZE, next);
}
// Return the header to the previous block
static inline char* block_prev(char* const block) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));

    return block - block_size(block - WSIZE);
}

// Return the header to the next block
static inline char* block_next(char* const block) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));

    return block + block_size(block);
}


/*
 *  Malloc Implementation
 *  ---------------------
 *  The following functions deal with the user-facing malloc implementation.
 */

/*
 * Global vars
 */
static char* heap_listp;
static char* free_list;
/*
 * My helper function headers
 */

static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t bp);
static void put_block(void* bp, size_t size);
static void put_free_block(char* block);

/*
 * Initialize: return -1 on error, 0 on success.
 */
int mm_init(void) {
    dbg_printf("\n-mm_init-");
    char* prologue;
    heap_listp = mem_sbrk(4*WSIZE);
    if (heap_listp == (void *)-1) return -1;

    /* allignemnt, size: WSIZE */
    put(heap_listp, WSIZE|ALLOCED);
    
    /* put prologue, size: 2*WSIZE */
    prologue = heap_listp + WSIZE;
    mark_block(prologue, 2*WSIZE, ALLOCED);

    /* epilogue, size: 0, alloced*/
    put(prologue + 2*WSIZE, 0x1);

    /* point to the footer of prologue */
    heap_listp = prologue;

    checkheap(1);  // Let's make sure the heap is ok!
    if (extend_heap(CHUNKSIZE) == NULL)
        return -1;
    checkheap(1);  // Let's make sure the heap is ok!
    return 0;
}

/*
 * Extend heap by size bytes
 */
static void *extend_heap(size_t size) {
    dbg_printf("-extend_heap-");
    char *bp;
    char *new_block;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;
    /* Overwrite epilogue*/
    new_block = bp - WSIZE; 
    /* Mark new block with footer and header as free */
    mark_block(new_block, size, FREE);
    /* Set epilogue */
    put(block_next(new_block), 0x1);
    checkheap(1);  // Let's make sure the heap is ok!
    return coalesce(new_block);

}

/*
 * bp isassumed to be a new free block 
 * and is currently not in the list, so
 * while coalescing we need to put new 
 * block to the free list
 */
static void *coalesce(void *bp){
    dbg_printf("-coalesce-");
    char* b_next = block_next(bp);
    char* b_prev = block_prev(bp);
    size_t is_prev_free = is_block_free(b_prev);
    size_t is_next_free = is_block_free(b_next);
    size_t size = block_size(bp);

    if (!is_prev_free && !is_next_free) {
        /* Add new block to the list as is */
        add_free_block(new_block);
        return bp;
    }

    else if (!is_prev_free && is_next_free) {
        /* Get link to the prev/next free blocks
         * for physically next block
         */
        char* prev_next_free = prev_free(b_next);
        char* next_next_free = next_free(b_next);
        size += block_size(block_next(bp));
        mark_block(bp, size, FREE);

    }

    else if (is_prev_free && !is_next_free) {
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
    checkheap(1);  // Let's make sure the heap is ok!
    return bp;
}

static void* find_fit(size_t size) {
    char* ptr = heap_listp;
    size_t bsize = block_size(ptr);
    while (bsize != 0)  {
        if (is_block_free(ptr) && bsize >= size) return ptr;
        ptr = block_next(ptr);
        bsize = block_size(ptr);
    }
    return NULL;
}

static void put_block(void* bp, size_t size){
    dbg_printf("-put_block(%zu)-", size);
    size_t old_size = block_size(bp);
    if (size < old_size) {
        char* free = (char*)bp + size;
        mark_block(free, old_size - size, FREE);
    } 
    mark_block(bp, size, ALLOCED);
    checkheap(1);  // Let's make sure the heap is ok!
}

// put the block to free list
// add block to the beginning of the free list
static  void put_free_block(char* block) {
    char* root, next;
    if (free_list == NULL) {
        mark_next_free(block, NULL);
        mark_prev_free(block, NULL);
    } else {
        next = next_free(free_list);
        /* Set link from second element to new root*/
        if (next != NULL) mark_prev_free(next, block);
        /* Set link to the second element from new root */
        mark_next_free(block, next);
        /* Set link to prev element for the new root */
        mark_prev_free(block, NULL);
    }
    /* Change root element */
    free_list = block;
}

/*
 * malloc
 */
void *malloc (size_t size) {
    dbg_printf("-malloc(%zu)-", size);
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
        return bp + WSIZE;
    }

    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize)) == NULL)
        return NULL;
    put_block(bp, asize);
    return bp + WSIZE;
}

/*
 * free
 */
void free (void *ptr) {
    if (ptr == NULL) return;
    REQUIRES(in_heap(ptr));
    dbg_printf("-free-");
    char* block = (char*)ptr - WSIZE;
    size_t size = block_size(block);
    mark_block(block, size, FREE);
    checkheap(1);  // Let's make sure the heap is ok!
    coalesce(block);
}

/*
 * realloc - you may want to look at mm-naive.c
 */
void *realloc(void *oldptr, size_t size) {
    dbg_printf("-realloc-");
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

    oldsize = block_size(oldptr) - 2*WSIZE;
    if (size < oldsize) oldsize = size;
    memcpy(newptr, oldptr, oldsize);

    free(oldptr);

    return newptr;
}

/*
 * calloc - you may want to look at mm-naive.c
 */
void *calloc (size_t nmemb, size_t size) {
    dbg_printf("-calloc-");
    size_t bytes = nmemb * size;
    void* newptr;
    newptr = malloc(bytes);
    memset(newptr, 0, bytes);

    return newptr;
}

// Returns 0 if no errors were found, otherwise returns the error
int mm_checkheap(int verbose) {
    verbose = verbose;
    char* ptr = heap_listp; 
    size_t size = block_size(ptr);
    size_t header = 0;
    size_t footer = 0;
    dbg_printf("\t");
    while (size != 0) {
        dbg_printf("[%p+%zu,%s]->", ptr, size, is_block_free(ptr)?"f":"a");
        if (!aligned(ptr)) {
            printf("Block pointer %p isn't aligned\n", ptr);
            return 1;
        }
        if (!in_heap(ptr)) {
            printf("Block pointer %p isn't in heap\n", ptr);
            return 1;
        }
        header = get(ptr);
        footer = get(ptr + size - WSIZE);
        if (header != footer) {
            printf("Header and footer doesn't match: %zu vs %zu\n", header, footer);
            return 1;   
        }
        ptr = block_next(ptr);
        size = block_size(ptr);
    }
    printf("OK\n");
    return 0;
}
