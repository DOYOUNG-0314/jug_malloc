/*
 * Segregated Free List + Next Fit malloc
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>
#include "mm.h"
#include "memlib.h"

#define WSIZE 8
#define DSIZE 16
#define CHUNKSIZE (1<<12)

#define MAX(x, y) ((x) > (y) ? (x) : (y))
#define PACK(size, alloc) ((size) | (alloc))
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))
#define GET_SUCC(bp) (*(void **)((char *)(bp) + WSIZE))
#define GET_PRED(bp) (*(void **)(bp))

#define LISTLIMIT 20

team_t team = {
    "ateam",
    "Harry Bovik",
    "bovik@cs.cmu.edu",
    "",
    ""
};

static void *segregated_free_lists[LISTLIMIT];
static char *heap_listp;
static void *last_bp;  // Next Fit용 마지막 탐색 위치

static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static int find_list_index(size_t size);
static void add_free_block(void *bp);
static void splice_free_block(void *bp);

/* 초기화 함수 */
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

    last_bp = NULL;  // next-fit 포인터 초기화

    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;

    return 0;
}

/* 크기에 따라 리스트 인덱스 찾기 */
static int find_list_index(size_t size) {
    int idx = 0;
    size_t temp = size;

    while (temp > 1 && idx < LISTLIMIT - 1) {
        temp >>= 1;
        idx++;
    }
    return idx;
}

/* 가용 블록 추가 */
static void add_free_block(void *bp) {
    int idx = find_list_index(GET_SIZE(HDRP(bp)));
    void *head = segregated_free_lists[idx];

    if (head != NULL)
        GET_PRED(head) = bp;
    GET_SUCC(bp) = head;
    GET_PRED(bp) = NULL;
    segregated_free_lists[idx] = bp;
}

/* 가용 블록 제거 */
static void splice_free_block(void *bp) {
    int idx = find_list_index(GET_SIZE(HDRP(bp)));

    if (GET_PRED(bp))
        GET_SUCC(GET_PRED(bp)) = GET_SUCC(bp);
    else
        segregated_free_lists[idx] = GET_SUCC(bp);

    if (GET_SUCC(bp))
        GET_PRED(GET_SUCC(bp)) = GET_PRED(bp);
}

/* 힙 확장 */
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

/* 가용 블록 병합 */
static void *coalesce(void *bp) {
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {
        add_free_block(bp);
        return bp;
    }
    else if (prev_alloc && !next_alloc) {
        splice_free_block(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    else if (!prev_alloc && next_alloc) {
        splice_free_block(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    else {
        splice_free_block(PREV_BLKP(bp));
        splice_free_block(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    add_free_block(bp);
    return bp;
}

/* Next Fit 방식으로 가용 블록 탐색 */
static void *find_fit(size_t asize) {
    void *start_bp = last_bp;
    int idx = 0;

    if (start_bp == NULL)
        start_bp = heap_listp;

    // 처음 위치부터 끝까지
    for (idx = 0; idx < LISTLIMIT; idx++) {
        void *bp = segregated_free_lists[idx];
        while (bp != NULL) {
            if (GET_SIZE(HDRP(bp)) >= asize) {
                last_bp = bp;
                return bp;
            }
            bp = GET_SUCC(bp);
        }
    }
    // 못 찾으면 다시 처음부터
    for (idx = 0; idx < LISTLIMIT; idx++) {
        void *bp = segregated_free_lists[idx];
        while (bp != NULL) {
            if (GET_SIZE(HDRP(bp)) >= asize) {
                last_bp = bp;
                return bp;
            }
            bp = GET_SUCC(bp);
        }
    }
    return NULL;
}

/* 요청 블록 배치 및 분할 */
static void place(void *bp, size_t asize) {
    splice_free_block(bp);

    size_t csize = GET_SIZE(HDRP(bp));

    if ((csize - asize) >= (2 * DSIZE)) {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));

        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
        add_free_block(bp);
    } else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/* malloc 함수 */
void *mm_malloc(size_t size) {
    size_t asize;
    size_t extendsize;
    char *bp;

    if (size == 0)
        return NULL;

    if (size <= DSIZE)
        asize = 2 * DSIZE;
    else
        asize = DSIZE * ((size + DSIZE + DSIZE - 1) / DSIZE);

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

/* free 함수 */
void mm_free(void *bp) {
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

/* realloc 함수 */
void *mm_realloc(void *ptr, size_t size) {
    if (ptr == NULL) return mm_malloc(size);
    if (size == 0) { mm_free(ptr); return NULL; }

    void *newptr = mm_malloc(size);
    if (newptr == NULL)
        return NULL;

    size_t copySize = GET_SIZE(HDRP(ptr)) - DSIZE;
    if (size < copySize)
        copySize = size;
    memcpy(newptr, ptr, copySize);
    mm_free(ptr);
    return newptr;
}
