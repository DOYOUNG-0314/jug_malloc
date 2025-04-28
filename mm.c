/*
 * mm-seglist-opt.c - Segregated Free List + Best Fit + Address Order + realloc 최적화
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>
#include "mm.h"
#include "memlib.h"

team_t team = {"ateam", "Harry Bovik", "bovik@cs.cmu.edu", "", ""};

#define WSIZE 8
#define DSIZE 16
#define CHUNKSIZE (1<<12)
#define LISTLIMIT 20

#define MAX(x, y) ((x) > (y) ? (x) : (y))
#define PACK(size, alloc) ((size) | (alloc))
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE((char *)(bp) - DSIZE))

#define GET_SUCC(bp) (*(void **)((char *)(bp) + WSIZE))
#define GET_PRED(bp) (*(void **)(bp))

static char *heap_listp;
static void *segregated_free_lists[LISTLIMIT];

static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static void insert_node(void *bp);
static void remove_node(void *bp);
static int find_list_index(size_t size);

int mm_init(void) {
    for (int i = 0; i < LISTLIMIT; i++)
        segregated_free_lists[i] = NULL;

    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
        return -1;

    PUT(heap_listp, 0);
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));
    heap_listp += (2 * WSIZE);

    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;
    return 0;
}

static int find_list_index(size_t size) {
    int idx = 0;
    size_t temp = size;
    while (idx < LISTLIMIT - 1 && temp > 1) {
        temp >>= 1;
        idx++;
    }
    return idx;
}

static void insert_node(void *bp) {
    int idx = find_list_index(GET_SIZE(HDRP(bp)));
    void *cur = segregated_free_lists[idx];
    void *prev = NULL;

    while (cur != NULL && cur < bp) {
        prev = cur;
        cur = GET_SUCC(cur);
    }

    if (prev != NULL)
        GET_SUCC(prev) = bp;
    else
        segregated_free_lists[idx] = bp;

    if (cur != NULL)
        GET_PRED(cur) = bp;

    GET_PRED(bp) = prev;
    GET_SUCC(bp) = cur;
}

static void remove_node(void *bp) {
    int idx = find_list_index(GET_SIZE(HDRP(bp)));

    if (GET_PRED(bp))
        GET_SUCC(GET_PRED(bp)) = GET_SUCC(bp);
    else
        segregated_free_lists[idx] = GET_SUCC(bp);

    if (GET_SUCC(bp))
        GET_PRED(GET_SUCC(bp)) = GET_PRED(bp);
}

static void *extend_heap(size_t words) {
    char *bp;
    size_t size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;

    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    return coalesce(bp);
}

static void *coalesce(void *bp) {
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {
        insert_node(bp);
        return bp;
    } else if (prev_alloc && !next_alloc) {
        remove_node(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    } else if (!prev_alloc && next_alloc) {
        remove_node(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    } else {
        remove_node(PREV_BLKP(bp));
        remove_node(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    insert_node(bp);
    return bp;
}

static void *find_fit(size_t asize) {
    int idx = find_list_index(asize);
    for (int i = idx; i < LISTLIMIT; i++) {
        void *bp = segregated_free_lists[i];
        void *best = NULL;
        size_t best_size = (size_t)(-1);

        while (bp != NULL) {
            size_t bsize = GET_SIZE(HDRP(bp));
            if (bsize >= asize && bsize < best_size) {
                best = bp;
                best_size = bsize;
            }
            bp = GET_SUCC(bp);
        }
        if (best != NULL)
            return best;
    }
    return NULL;
}

static void place(void *bp, size_t asize) {
    size_t csize = GET_SIZE(HDRP(bp));
    remove_node(bp);

    if ((csize - asize) >= (2 * DSIZE)) {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));

        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
        insert_node(bp);
    } else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

void *mm_malloc(size_t size) {
    size_t asize;
    size_t extendsize;
    char *bp;

    if (size == 0)
        return NULL;

    if (size <= DSIZE)
        asize = 2 * DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);

    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}

void mm_free(void *bp) {
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

void *mm_realloc(void *ptr, size_t size) {
    if (ptr == NULL)
        return mm_malloc(size);
    if (size == 0) {
        mm_free(ptr);
        return NULL;
    }

    size_t oldsize = GET_SIZE(HDRP(ptr));
    size_t asize = (size <= DSIZE) ? (2 * DSIZE) : DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);

    if (asize <= oldsize)
        return ptr;

    void *next = NEXT_BLKP(ptr);
    if (!GET_ALLOC(HDRP(next)) && (oldsize + GET_SIZE(HDRP(next))) >= asize) {
        remove_node(next);
        size_t newsize = oldsize + GET_SIZE(HDRP(next));
        PUT(HDRP(ptr), PACK(newsize, 1));
        PUT(FTRP(ptr), PACK(newsize, 1));
        return ptr;
    }

    void *newptr = mm_malloc(size);
    if (newptr == NULL)
        return NULL;

    size_t copySize = oldsize - DSIZE;
    if (size < copySize)
        copySize = size;
    memcpy(newptr, ptr, copySize);
    mm_free(ptr);
    return newptr;
}
