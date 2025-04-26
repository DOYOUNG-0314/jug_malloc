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
static void put_free_block(void *bp);
static void remove_free_block(void *bp);
static void splice_free_block(void *bp); 



/* 기본 상수 및 매크로 */
#define WSIZE 8               // 워드 크기 (4바이트)
#define DSIZE 16               // 더블워드 크기 (8바이트)
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

#define GET_SUCC(bp) (*(void **)((char *)(bp) + WSIZE)) // 다음 가용 블록의 주소
#define GET_PRED(bp) (*(void **)(bp))                   // 이전 가용 블록의 주소

/* 전역 변수 */
static char *heap_listp;  // 힙 시작 포인터


/* mm_init - 힙과 프롤로그/에필로그 블록 초기화 */
int mm_init(void)
{
    /* 메모리 블록 초기화 */
    if ((heap_listp = mem_sbrk(8 * WSIZE)) == (void *)-1) // 8워드 크기의 힙 생성, free_listp에 힙의 시작 주소값 할당(가용 블록만 추적)
        return -1;
    PUT(heap_listp, 0);                                // 정렬 패딩
    PUT(heap_listp + (1 * WSIZE), PACK(2 * WSIZE, 1)); // 프롤로그 Header
    PUT(heap_listp + (2 * WSIZE), PACK(2 * WSIZE, 1)); // 프롤로그 Footer
    PUT(heap_listp + (3 * WSIZE), PACK(4 * WSIZE, 0)); // 첫 가용 블록의 헤더 -> 가용 블록 리스트의 시작점 역할
    PUT(heap_listp + (4 * WSIZE), 0);               // 이전 가용 블록의 주소
    PUT(heap_listp + (5 * WSIZE), 0);               // 다음 가용 블록의 주소
    PUT(heap_listp + (6 * WSIZE), PACK(4 * WSIZE, 0)); // 첫 가용 블록의 푸터
    PUT(heap_listp + (7 * WSIZE), PACK(0, 1));         // 에필로그 Header: 프로그램이 할당한 마지막 블록의 뒤에 위치하며, 블록이 할당되지 않은 상태를 나타냄

    heap_listp += (4 * WSIZE); // 첫번째 가용 블록의 bp

    // 힙을 CHUNKSIZE bytes로 확장
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;

    return 0;
}
/* extend_heap - 힙을 words 워드만큼 확장 */
static void *extend_heap(size_t words)
{
    char *bp;

    // 더블 워드 정렬 유지
    // size: 확장할 크기
    size_t size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE; // 2워드의 가장 가까운 배수로 반올림 (홀수면 1 더해서 곱함)

    if ((long)(bp = mem_sbrk(size)) == -1) // 힙 확장
        return NULL;

    PUT(HDRP(bp), PACK(size, 0));         // 새 빈 블록 헤더 초기화
    PUT(FTRP(bp), PACK(size, 0));         // 새 빈 블록 푸터 초기화
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); // 에필로그 블록 헤더 초기화

    return coalesce(bp); // 병합 후 coalesce 함수에서 리턴된 블록 포인터 반환
}

// 가용 리스트의 맨 앞에 현재 블록을 추가하는 함수
static void add_free_block(void *bp)
{
    GET_SUCC(bp) = heap_listp;     // bp의 SUCC은 루트가 가리키던 블록
    if (heap_listp != NULL)        // free list에 블록이 존재했을 경우만
        GET_PRED(heap_listp) = bp; // 루트였던 블록의 PRED를 추가된 블록으로 연결
    heap_listp = bp;               // 루트를 현재 블록으로 변경
}

/* coalesce - 인접 가용 블록 병합 */
static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); // 이전 블록 할당 상태
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); // 다음 블록 할당 상태
    size_t size = GET_SIZE(HDRP(bp));                   // 현재 블록 사이즈

    if (prev_alloc && next_alloc) // 모두 할당된 경우
    {
        add_free_block(bp); // free_list에 추가
        return bp;          // 블록의 포인터 반환
    }
    else if (prev_alloc && !next_alloc) // 다음 블록만 빈 경우
    {
        splice_free_block(NEXT_BLKP(bp)); // 가용 블록을 free_list에서 제거
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0)); // 현재 블록 헤더 재설정
        PUT(FTRP(bp), PACK(size, 0)); // 다음 블록 푸터 재설정 (위에서 헤더를 재설정했으므로, FTRP(bp)는 합쳐질 다음 블록의 푸터가 됨)
    }
    else if (!prev_alloc && next_alloc) // 이전 블록만 빈 경우
    {
        splice_free_block(PREV_BLKP(bp)); // 가용 블록을 free_list에서 제거
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); // 이전 블록 헤더 재설정
        PUT(FTRP(bp), PACK(size, 0));            // 현재 블록 푸터 재설정
        bp = PREV_BLKP(bp);                      // 이전 블록의 시작점으로 포인터 변경
    }
    else // 이전 블록과 다음 블록 모두 빈 경우
    {
        splice_free_block(PREV_BLKP(bp)); // 이전 가용 블록을 free_list에서 제거
        splice_free_block(NEXT_BLKP(bp)); // 다음 가용 블록을 free_list에서 제거
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); // 이전 블록 헤더 재설정
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0)); // 다음 블록 푸터 재설정
        bp = PREV_BLKP(bp);                      // 이전 블록의 시작점으로 포인터 변경
    }
    add_free_block(bp); // 현재 병합한 가용 블록을 free_list에 추가
    return bp;          // 병합한 가용 블록의 포인터 반환
}

/* find_fit - next-fit 방식으로 가용 블록 탐색 */
static void *find_fit(size_t asize)
{
    void *bp = heap_listp;
    while (bp != NULL) // 다음 가용 블럭이 있는 동안 반복
    {
        if ((asize <= GET_SIZE(HDRP(bp)))) // 적합한 사이즈의 블록을 찾으면 반환
            return bp;
        bp = GET_SUCC(bp); // 다음 가용 블록으로 이동
    }
    return NULL;
}

static void splice_free_block(void *bp)
{
    if (bp == heap_listp) // 분리하려는 블록이 free_list 맨 앞에 있는 블록이면 (이전 블록이 없음)
    {
        heap_listp = GET_SUCC(heap_listp); // 다음 블록을 루트로 변경
        return;
    }
    // 이전 블록의 SUCC을 다음 가용 블록으로 연결
    GET_SUCC(GET_PRED(bp)) = GET_SUCC(bp);
    // 다음 블록의 PRED를 이전 블록으로 변경
    if (GET_SUCC(bp) != NULL) // 다음 가용 블록이 있을 경우만
        GET_PRED(GET_SUCC(bp)) = GET_PRED(bp);
}

/* place - 요청한 블록을 가용 블록에 배치하고 필요 시 분할 */
static void place(void *bp, size_t asize)
{
    splice_free_block(bp); // free_list에서 해당 블록 제거

    size_t csize = GET_SIZE(HDRP(bp)); // 현재 블록의 크기

    if ((csize - asize) >= (2 * DSIZE)) // 차이가 최소 블록 크기 16보다 같거나 크면 분할
    {
        PUT(HDRP(bp), PACK(asize, 1)); // 현재 블록에는 필요한 만큼만 할당
        PUT(FTRP(bp), PACK(asize, 1));

        PUT(HDRP(NEXT_BLKP(bp)), PACK((csize - asize), 0)); // 남은 크기를 다음 블록에 할당(가용 블록)
        PUT(FTRP(NEXT_BLKP(bp)), PACK((csize - asize), 0));
        add_free_block(NEXT_BLKP(bp)); // 남은 블록을 free_list에 추가
    }
    else
    {
        PUT(HDRP(bp), PACK(csize, 1)); // 해당 블록 전부 사용
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/* mm_malloc - 메모리 블록 할당 */
void *mm_malloc(size_t size)
{
    size_t asize;      // 조정된 블록 사이즈
    size_t extendsize; // 확장할 사이즈
    char *bp;

    // 잘못된 요청 분기
    if (size == 0)
        return NULL;
  
    /* 사이즈 조정 */
    if (size <= DSIZE)     // 8바이트 이하이면
        asize = 2 * DSIZE; // 최소 블록 크기 16바이트 할당 (헤더 4 + 푸터 4 + 저장공간 8)
    else
        asize = DSIZE * ((size + DSIZE + DSIZE - 1) / DSIZE); // 8배수로 올림 처리

    /* 가용 블록 검색 */
    if ((bp = find_fit(asize)) != NULL)
    {
        place(bp, asize); // 할당
        return bp;        // 새로 할당된 블록의 포인터 리턴
    }

    /* 적합한 블록이 없을 경우 힙확장 */
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}

/* mm_free - 메모리 블록 해제 */
void mm_free(void *bp)
{
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