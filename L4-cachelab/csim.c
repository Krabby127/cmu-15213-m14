/*
 * Name: Nikita Chepanov
 * Andrew ID: nchepano@andrew.cmu.edu
 */

#include <stdio.h>
#include <getopt.h>
#include <stdlib.h>
#include <string.h>
#include "cachelab.h"

/* auxiliary types */
typedef enum {      /* states */
    S_NONE  =0,
    S_MISS  =1,
    S_HIT   =2,
    S_EVICT =4,

    S_MISS_EVICT =(S_MISS|S_EVICT),
    S_MISS_HIT =(S_MISS|S_HIT),
    S_MISS_EVICT_HIT =(S_MISS|S_EVICT|S_HIT)
} parse_state_t;

#define SETBITS( ad, s, b ) ( (0x7fffffff>>(31 - (s))) & ((ad)>>(b)) )
#define TAGBITS( ad, s, b ) (( 0x7fffffff >> (31 - (s) - (b)) ) & ((ad) >> ((s) + (b))) )

typedef struct {
    int isValid; 
    int tag; 
    int accessCount; 
} cache_line_t;

typedef cache_line_t* cache_line_p;

typedef struct {
    int set_count;
    int lines_per_set; 
    cache_line_p *set;
} cache_t;

typedef struct {
    int s, E, b, verbose;
    char fname[512];
} run_options_t;

typedef struct {
    int hitCount;
    int missCount;
    int evictionCount;
} cache_stats_t;
/* end auxiliary types */

/* function prototypes */
int             print_help();
int             parse_args(run_options_t* opt, int argc, char *argv[] );
int             cache_init(cache_t *cache, const run_options_t* );
int             cache_upd_accessCount(cache_t *cache, int selset, int cl);
void            print_line_status( FILE*, const char* buf, parse_state_t state );
parse_state_t   process_trace_line(cache_t *cache, cache_stats_t* stats, const char *line_buf, const run_options_t* opt );
/* end of function prototypes */

int main(int argc, char *argv[])
{
    run_options_t opt = {0};
    if( parse_args(&opt, argc, argv ) < 0 ) 
        exit(-1);

    cache_t cache={0};
    cache_init(&cache, &opt );
    FILE* fp = fopen(opt.fname, "r");
    if (!fp) {
        printf("failed to open trace file  %s\n", opt.fname);
        exit(-1);
    }

    cache_stats_t cache_stats={0};
    for( char line_buf[100]; fgets(line_buf, 100, fp); ) {
        if (' ' == *line_buf) {
            line_buf[strlen(line_buf)-1] = '\0'; /* removing trailing newline */
            parse_state_t state = process_trace_line(&cache, &cache_stats, line_buf, &opt );
            if (opt.verbose)
                print_line_status( stdout, line_buf+1, state );
        }
    }
    fclose(fp);
    printSummary(cache_stats.hitCount, cache_stats.missCount, cache_stats.evictionCount);
}

void print_line_status( FILE*fp, const char* s, parse_state_t state )
{
        switch (state) {
        case S_HIT: fprintf(fp, "%s hits\n", s ); break;
        case S_MISS: fprintf(fp, "%s miss\n", s ); break;
        case S_MISS_HIT: fprintf(fp, "%s miss hit\n", s ); break;
        case S_MISS_EVICT: fprintf(fp, "%s miss eviction\n", s ); break;
        case S_MISS_EVICT_HIT: fprintf(fp, "%s miss eviction hit\n", s ); break;
        default: break;
        }
}

int parse_args(run_options_t* opt, int argc, char *argv[])
{
    if( argc < 2 ) 
        return print_help();

    for (char o=0; -1 != (o = getopt(argc, argv, "vs:E:b:t:")); ) {
        int x = atoi(optarg);
        switch (o) {
        case 'v': opt->verbose = 1; break;
        case 's': opt->s = x; break;
        case 'E': opt->E = atoi(optarg); break;
        case 'b': opt->b = atoi(optarg); break;
        case 't': strncpy(opt->fname, optarg, sizeof( opt->fname)-1 ); break;

        default:
            return print_help();
        }
    }
    return 0;
}

int print_help()
{
    fprintf(stderr, "Usage: csim -s <SET BITS> -E <LINES PER SET> -b <BLOCK BITS> -t <filename>\n ALSO: \n -h: prints this help \n -v: verbose mode \n ");
    return -1;
}

int cache_init(cache_t *cache, const run_options_t* opt )
{
    cache->set_count = (2 << opt->s );
    cache->lines_per_set = opt->E;
    cache_line_p* set = (cache_line_p*)calloc(cache->set_count, sizeof(cache_line_p));
    cache->set = set;

    for ( cache_line_p* s = set, *s_end = s+cache->set_count; s < s_end; ++s) {
        *s = (cache_line_p)malloc(cache->lines_per_set * sizeof(cache_line_t));
        for (cache_line_p p = *s, p_end = p+cache->lines_per_set; p <p_end; ++p) {
            p->isValid = 0;
        }
    }
    return 0;
}

parse_state_t process_trace_line(cache_t *cache, cache_stats_t* stats, const char *line_buf, const run_options_t* opt )
{
    char o=0;
    int addr=0, selset=0, tag=0;

    if( sscanf(line_buf, " %c %x", &o, &addr) < 2 ) 
        return S_NONE;
    selset = SETBITS(addr, opt->s, opt->b);
    tag    = TAGBITS(addr, opt->s, opt->b);

    cache_line_p ss= cache->set[selset];
#define LINE_LOOP for (cache_line_p p = ss, p_end=ss+cache->lines_per_set; p < p_end; ++p)
    LINE_LOOP {
        if (1 == p->isValid && tag == p->tag) {
            stats->hitCount += ( 'M' == o ? 2: 1 );
            cache_upd_accessCount(cache, selset, (p-ss));
            return S_HIT;
        }
    }
    ++(stats->missCount);
    LINE_LOOP {
        if (!p->isValid) {              
            p->isValid= 1;
            p->tag    = tag;
            cache_upd_accessCount(cache, selset, (p-ss));
            return( 'M' == o ? (++(stats->hitCount), S_MISS_HIT) : S_MISS );
        }
    }
    ++(stats->evictionCount);
    LINE_LOOP {
        if (p->accessCount == 1) {
            p->isValid=1;
            p->tag = tag;
            cache_upd_accessCount(cache, selset, (p-ss));
            return( 'M' == o ? (++(stats->hitCount),S_MISS_EVICT_HIT) : S_MISS_EVICT );
        }
    }
    return S_NONE;
}

int cache_upd_accessCount(cache_t *cache, int selset, int cl)
{
    cache_line_p set = cache->set[selset], clLine = set+cl;
    for (cache_line_p p = set, p_end =p+cache->lines_per_set; p < p_end; ++p) {
        if(p->isValid && p->accessCount > clLine->accessCount) --(p->accessCount);
    }
    return (clLine->accessCount = cache->lines_per_set, 0 );
}
