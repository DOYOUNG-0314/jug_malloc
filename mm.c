/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>
#include <errno.h>

#include "mm.h"
#include "memlib.h"

/* 팀 정보 */
team_t team = {
    "ateam",
    "Harry Bovik",
    "bovik@cs.cmu.edu",
    "",
    ""
};

/* 함수 선언 */
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);

/* 기본 상수 및 매크로 */
#define WSIZE 4               // 워드 크기 (4바이트)
#define DSIZE 8               // 더블워드 크기 (8바이트)
#define CHUNKSIZE (1 << 12)    // 초기 확장 힙 크기 (4KB)

#define MAX(x, y) ((x) > (y) ? (x) : (y)) // 큰 값 반환
#define PACK(size, alloc) ((size) | (alloc)) // 크기와 할당 비트를 결합

#define GET(p) (*(unsigned int *)(p))             // 주소 p가 가리키는 값을 읽기
#define PUT(p, val) (*(unsigned int *)(p) = (val)) // 주소 p에 val 저장

#define GET_SIZE(p) (GET(p) & ~0x7)     // 주소 p의 블록 크기 얻기
#define GET_ALLOC(p) (GET(p) & 0x1)     // 주소 p의 할당 여부 얻기

#define HDRP(bp) ((char *)(bp) - WSIZE)                // 블록 포인터 bp의 헤더 주소
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) // 블록 포인터 bp의 풋터 주소

#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) // 다음 블록
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) // 이전 블록

#define ALIGNMENT 8
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7) // 8바이트 정렬
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* 전역 변수 */
static char *heap_listp;  // 힙 시작 포인터
static char *last_bp;     // next-fit 탐색용 마지막 포인터

/* mm_init - 힙과 프롤로그/에필로그 블록 초기화 */
int mm_init(void) {
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
        return -1;
    PUT(heap_listp, 0);                              // 패딩
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1));    // 프롤로그 헤더
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1));    // 프롤로그 풋터
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));        // 에필로그 헤더
    heap_listp += (2 * WSIZE);
    last_bp = heap_listp;                            // last_bp 초기화
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;
    return 0;
}

/* extend_heap - 힙을 words 워드만큼 확장 */
static void *extend_heap(size_t words) {
    char *bp;
    size_t size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;
    PUT(HDRP(bp), PACK(size, 0));         // 새 가용 블록 헤더
    PUT(FTRP(bp), PACK(size, 0));         // 새 가용 블록 풋터
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); // 새로운 에필로그 헤더
    return coalesce(bp); // 확장한 블록을 coalesce해서 리턴
}

/* coalesce - 인접 가용 블록 병합 */
static void *coalesce(void *bp) {
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {           // case 1: 둘 다 할당
        // 아무 것도 하지 않음
    } else if (prev_alloc && !next_alloc) {    // case 2: 다음만 가용
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    } else if (!prev_alloc && next_alloc) {    // case 3: 이전만 가용
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    } else {                                  // case 4: 둘 다 가용
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    last_bp = bp; // ✅ 병합한 블록을 last_bp로 설정 (필수)
    return bp;
}

/* find_fit - next-fit 방식으로 가용 블록 탐색 */
static void *find_fit(size_t asize) {
    char *bp = last_bp;

    // 1. last_bp 이후부터 힙 끝까지 탐색
    for (; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
            last_bp = bp; // 찾으면 last_bp 업데이트
            return bp;
        }
    }

    // 2. 못 찾으면 힙 처음부터 last_bp까지 다시 탐색
    for (bp = heap_listp; bp != last_bp; bp = NEXT_BLKP(bp)) {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
            last_bp = bp;
            return bp;
        }
    }

    return NULL; // 없음
}

/* place - 요청한 블록을 가용 블록에 배치하고 필요 시 분할 */
static void place(void *bp, size_t asize) {
    size_t csize = GET_SIZE(HDRP(bp));

    if ((csize - asize) >= (2 * DSIZE)) { // 분할 가능
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
    } else { // 분할 불가
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/* mm_malloc - 메모리 블록 할당 */
void *mm_malloc(size_t size) {
    size_t asize;
    size_t extendsize;
    char *bp;

    if (size == 0)
        return NULL;

    if (size <= DSIZE)
        asize = 2 * DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);

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

/* mm_free - 메모리 블록 해제 */
void mm_free(void *bp) {
    size_t size = GET_SIZE(HDRP(bp));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

/* mm_realloc - 메모리 블록 크기 재조정 */
void *mm_realloc(void *ptr, size_t size) {
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;

    newptr = mm_malloc(size);
    if (newptr == NULL)
        return NULL;

    copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    if (size < copySize)
        copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}
