/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 *
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced(합체) or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "ateam",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/*기본 상수 및 매크로 정리*/
#define WSIZE 4
#define DSIZE 8
#define CHUNKSIZE (1<<12) //4KB

#define MAX(x, y) ((x) > (y) ? (x) : (y)) // 큰값 찾기

#define PACK(size, alloc) ((size) | (alloc)) // 사이즈랑 alloc 여부 OR 연산으로 헤더값, 풋터값 넣을 거 만들기

#define GET(p) (*(unsigned int *)(p)) // p가 참조하는 워드 읽기
#define PUT(p, val) (*(unsigned int *)(p) =(val)) // p가 참조하는 워드에 val 저장

#define GET_SIZE(p) (GET(p) & ~0x7) // 사이즈 받아오기 (헤더값과 111..1000 AND 연산으로 사이즈만 받아오기)
#define GET_ALLOC(p) (GET(p) & 0x1) // 할당여부 받아오기 (헤더값과 000..01 AND 연산으로 할당여부만 받아오기)

#define HDRP(bp) ((char *)(bp) - WSIZE) // 헤더 포인터 받아오기 (bp : 블록 포인터) (블록포인터 워드 사이즈만큼 전으로 이동)
// 풋터 포인터 받아오기 (블록포인터를 블록 크기만큼 이동시키고 더블 워드만큼 전으로 이동)
// 더블 워드 사이즈를 빼야함 (블록 사이즈는 헤더 + data + 풋터 다 포함 이니까)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) 

#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char*)(bp) - WSIZE))) // 다음 블록포인터 (블록 포인터 + 현재헤더보고 현재사이즈만큼 더하기)
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char*)(bp) - DSIZE))) // 이전 블록포인터 (블록 포인터 - 이전풋터보고 이전사이즈만큼 빼기)
//(블록 포인터 - 더블워드 => 이전 풋터)

// heap_listp 힙 시작? 포인터 or 끝 가리키는 포인터
static void *heap_listp = 0;
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *extend_heap(size_t words);
static void *coalesce(void *bp);

/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void) // 힙 초기화 후 할당& 반환 요청 준비완
{
    if((heap_listp = mem_sbrk(4*WSIZE)) == (void*)-1){ // 추가 힙 메모리 요청 (왜 4*WSIZE 이지?)
        return -1; 
    }

    PUT(heap_listp, 0); // 정렬 패딩
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); // 프롤로그헤더?
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); // 프롤로그풋터?
    PUT(heap_listp + (3*WSIZE), PACK(0, 1)); //에필로그 헤더
    heap_listp += (2*WSIZE); // 힙 영역이 시작할 곳,프롤로그 풋터 바로 다음 위치
    // 빈 가용 리스트 만들고 초기화

    if(extend_heap(CHUNKSIZE/WSIZE) == NULL){ // 힙 늘려라
    // 힙 확장하고 초기 가용 블록 생성 
        return -1;
    }
    return 0;
}

static void *extend_heap(size_t words) // size_t 는 문자열이나 메모리 사이즈를 나타낼 때 사용
// 1. 힙이 초기화 될때, 2. 적당한 fit을 못찾을 때 정렬(alignment)할때
{
    char *bp;
    size_t size;

    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE; // 패딩?
    if((long)(bp = mem_sbrk(size)) == -1){  // 새로 늘어난 힙의 시작 주소 리턴
        return NULL;
    }

    PUT(HDRP(bp), PACK(size, 0)); // 헤더에다가 사이즈, notAlloc 저장
    PUT(FTRP(bp), PACK(size, 0)); // 풋터에다가 사이즈, notAlloc 저장
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0,1)); // 에필로그 헤더였구나

    return coalesce(bp); // 앞 블록이 free이면 연결
}
/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize;
    char *bp;

    if(size == 0){
        return NULL;
    }

    if(size <= DSIZE){
        asize = 2*DSIZE;
    } else {
        asize = DSIZE * ((size + (DSIZE) + (DSIZE -1)) / DSIZE); // 걍 크기 더블워드로 맞춰주기
    }

    if((bp = find_fit(asize)) != NULL){ // 빈공간 찾기
        place(bp, asize);
        return bp;
    }

    extendsize = MAX(asize, CHUNKSIZE); // 없으면 힙 확장
    if((bp = extend_heap(extendsize/WSIZE)) == NULL){
        return NULL;
    }
    place(bp, asize);
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr) // ptr = bp 
{
    size_t size = GET_SIZE(HDRP(ptr)); //헤더로부터 사이즈 받고

    PUT(HDRP(ptr), PACK(size, 0));  // 헤더 
    PUT(FTRP(ptr), PACK(size, 0));  // 풋터
    coalesce(ptr); // 연결

}

static void *coalesce(void *bp)
{   
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); // 이전 블록 할당 여부
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); // 다음 블록 할당 여부
    size_t size  = GET_SIZE(HDRP(bp)); // 현재 사이즈

    if(prev_alloc && next_alloc) { // 앞 뒤 다 할당
        return bp;
    }
    else if(prev_alloc && !next_alloc){ // 앞 할당, 뒤 free
        size += GET_SIZE(HDRP(NEXT_BLKP(bp))); 
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0)); // 이거 해도 이전 풋터가 아닌 합친놈의 풋터가 나온다
    }
    else if(!prev_alloc && next_alloc){ // 앞 free, 뒤 할당
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    else{ // 둘 다 free
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    return bp;
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size) //realloc
{
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

static void *find_fit(size_t asize)  // 자리 찾기
{
    void *bp;

    for(bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){
        if(!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))){
            return bp;
        }
    }
    return NULL;
}

static void place(void * bp, size_t asize) // 
{
    size_t csize = GET_SIZE(HDRP(bp));

    if((csize - asize) >= (2*DSIZE)){ // 남는 공간이 더블비트 이상이면 쪼개고 할당
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize-asize, 0));
        PUT(FTRP(bp), PACK(csize-asize, 0));
    } else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}