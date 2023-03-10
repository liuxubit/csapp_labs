/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 * 
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
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
    ""
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* 头部/脚部的大小, 单字 */
#define WSIZE (4)

/* 双字大小 */
#define DSIZE (8)

/* 扩展堆时的默认大小 4kb */
#define CHUNKSIZE (1 << 12)

/* 最小申请内存大小 */
#define MINBLOCK (DSIZE + 2 * WSIZE)

#define MAX(x, y) ((x) > (y)? (x) : (y))

/* 设置头部/脚部, 将size和allocate bit 合并成一个字*/
#define PACK(size, alloc) ((size)|(alloc))

/* 读地址p处的一个字 */
#define GET(p) (*(unsigned int *)(p))

/* 向地址p处写一个字 */
#define PUT(p, val)  (*(unsigned int *)(p) = (val))

/* 得到地址p处的size */
#define GET_SIZE(p) (GET(p) & ~0x7)

/* 得到地址p处的标志位 */
#define GET_ALLOC(p) (*(p) & 0x1)

/* 获得头部地址 */
#define HDRP(bp) ((char*)(bp) - WSIZE)

/* 获得脚部地址 */
#define FTRP(bp) ((char*)bp + GET_SIZE(HDRP(bp)) - DSIZE)

/* 计算后块的地址 */
#define NEXT_BLKP(bp) ((char*)bp + GET_SIZE(HDRP(bp)))

/* 计算前块的地址 */
#define PREV_BLKP(bp) ((char*)bp - GET_SIZE((char*)(bp) - DSIZE))

/* 前一个链表节点 */
#define PREV_LINKNODE_RP(bp) ((char*)bp)

/* 后一个链表节点 */
#define NEXT_LINKNODE_RP(bp) ((char*)bp + WSIZE)

/* 指向序言块 */
static void* heap_listp;

/* 节点 */
static void* root;

/* 拓展块 */
static void *extend_heap(size_t size);

/* 寻找空闲块 */
static void *find_fit(size_t size);

/* 分割空闲块 */
static void place(char *bp, size_t asize);

/* 合并空闲块 */
static void *coalesce(void *bp);

/* 插入节点到链表 */
void insert_to_empty_list(char *bp);

void fix_linklist(char *p);

/* 打印 */
// static void mm_printblock(int verbose, const char* func);

/* 
 * mm_init - initialize the malloc package.
 * 建立序言块，结尾块，以及序言块前的对齐块(4B), 总共需要4个4B的空间
 */
int mm_init(void)
{
    if ((heap_listp = mem_sbrk(6 * WSIZE)) == (void *)-1){
        return -1;
    }
    PUT(heap_listp, 0);  // 堆起始位置的对齐块，使得bp对齐8字节
    PUT(heap_listp + 1 * WSIZE, 0);
    PUT(heap_listp + 2 * WSIZE, 0);
    PUT(heap_listp + 3 * WSIZE, PACK(DSIZE, 1));
    PUT(heap_listp + 4 * WSIZE, PACK(DSIZE, 1));
    PUT(heap_listp + 5 * WSIZE, PACK(0, 1));
    
    root = heap_listp + 1 * WSIZE;
    heap_listp += (4 * WSIZE);    

    if (extend_heap(CHUNKSIZE / DSIZE) == NULL){   // 扩展堆块
        return -1;
    }
    
    return 0;
}

static void *extend_heap(size_t size){
    size_t asize;
    char *bp;

    asize = (size % 2) ? (size + 1) * DSIZE : size * DSIZE;

    // if((long)(bp = mem_sbrk(asize)) == (void*)-1){
    if((long)(bp = mem_sbrk(asize)) == -1){
        return NULL;
    }

    PUT(HDRP(bp), PACK(asize, 0));  // 释放头部
    PUT(FTRP(bp), PACK(asize, 0));  // 释放脚部
    PUT(NEXT_LINKNODE_RP(bp), 0);
    PUT(PREV_LINKNODE_RP(bp), 0);
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); // 新的脚部

    return coalesce(bp);
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extend_size;
    char* bp;
    if (size == 0){
        return NULL;
    }

    if (size <= DSIZE){
        asize = 2 * DSIZE;
    } 
    else{
        asize = (DSIZE) * ((size + (DSIZE) + (DSIZE - 1)) / (DSIZE));
    }

    if ((bp = find_fit(asize)) != NULL){
        place(bp, asize);
        return bp;
    }

    extend_size = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extend_size / DSIZE)) == NULL){
        return NULL;
    }

    place(bp, asize);
    return bp;

}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    if (bp == 0){
        return;
    }

    size_t size = GET_SIZE(HDRP(bp));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(NEXT_LINKNODE_RP(bp), 0);
    PUT(PREV_LINKNODE_RP(bp), 0);
    coalesce(bp);
}

static void *coalesce(void *bp){

    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc){
    }
    else if (prev_alloc && !next_alloc){
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        fix_linklist(NEXT_BLKP(bp)); /* remove from empty list */
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    else if (!prev_alloc && next_alloc){
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        fix_linklist(PREV_BLKP(bp));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    else if (!prev_alloc && !next_alloc){
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(HDRP(NEXT_BLKP(bp)));
        fix_linklist(NEXT_BLKP(bp));
        fix_linklist(PREV_BLKP(bp));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    insert_to_empty_list(bp);
    return bp;
}

void insert_to_empty_list(char *bp){
    /* bp 会被插入到linklist中，LIFO */
    char *nextbp = GET(root);
    if (NULL != nextbp){
        PUT(PREV_LINKNODE_RP(nextbp), bp);
    }
    PUT(NEXT_LINKNODE_RP(bp), nextbp);

    PUT(root, bp);
}

void fix_linklist(char *bp){
    
    char *prevbp = GET(PREV_LINKNODE_RP(bp));
    char *nextbp = GET(NEXT_LINKNODE_RP(bp));

    if (NULL == prevbp){
        if(NULL != nextbp){
            PUT(PREV_LINKNODE_RP(nextbp), 0);
        }
        PUT(root, nextbp);
    }
    else {
        if(NULL != nextbp){
            PUT(PREV_LINKNODE_RP(nextbp), prevbp);
        }
        PUT(NEXT_LINKNODE_RP(prevbp), nextbp);
    }

    PUT(NEXT_LINKNODE_RP(bp), 0);
    PUT(PREV_LINKNODE_RP(bp), 0);
}

static void *find_fit(size_t size){

    char *bp;
    for(bp = GET(root); bp != NULL; bp = GET(NEXT_LINKNODE_RP(bp))){
        if (GET_SIZE(HDRP(bp)) >= size){
            return bp;
        }
    }
    return NULL;
}

static void place(char *bp, size_t asize){

    size_t csize = GET_SIZE(HDRP(bp));
    fix_linklist(bp);
    if ((csize - asize) >= (2 * DSIZE)){
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);

        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
        PUT(NEXT_LINKNODE_RP(bp), 0);
        PUT(PREV_LINKNODE_RP(bp), 0);
        coalesce(bp);
    }
    else{
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }

}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    size_t old_size;
    void *new_ptr;

    if (size == 0){
        mm_free(ptr);
        return 0;
    }

    if (ptr == NULL)
    {
        return mm_malloc(size);
    }

    new_ptr = mm_malloc(size);

    if (!new_ptr)
    {
        return 0;
    }

    old_size = GET_SIZE(HDRP(ptr));
    if (size < old_size){
        old_size = size;
    }

    memcpy(new_ptr, ptr, old_size);

    mm_free(ptr);

    return new_ptr;
}














