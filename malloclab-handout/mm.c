/*
 * mm.c - version 4, by Yilang Zhang.
 * 
 * Explicit free list + Segregated free list + Segregated fit + Boundary mark.
 * The size class lists (segregated free list) are saved in the head of heap.
 * The lists are linked by the `pred` pointer and `succ` pointer, which points
 * to the predecessor and successor of one block. And it should be stressed
 * that blocks in size class lists are ordered by their payload, i.e. their sizes.
 *
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

team_t team = {
    /* Team name */
    "16307130242",
    /* First member's full name */
    "Yilang Zhang",
    /* First member's email address */
    "16307130242@fudan.edu.cn",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

/* Align size to double words */
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* Basic constants and macros */
#define WSIZE 4				/* Word and header/footer size (bytes) */
#define DSIZE 8				/* Double word size (bytes) */
#define CHUNKSIZE (1<<12)	/* Extend heap by this amount (bytes) */
#define MAXCLASS 15			/* Max number of size classes (odd) */

#define MAX(x, y) ((x) > (y)? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a word at address P */
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))
#define PUT_P(p, p_to) (*(unsigned int *)(p) = (unsigned int)(p_to))

/* Read the size and allocated fields from address P */
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* Given block ptr bp, compute its predecessor and successor pointers */
#define PRED_PTR(bp) ((char *)(bp))
#define SUCC_PTR(bp) ((char *)(bp) + WSIZE)

/* Given block ptr bp, compute address of predecessor and successor blocks */
#define PRED(bp) (*(char **)(bp))
#define SUCC(bp) (*(char **)(SUCC_PTR(bp)))

/* Size class list pointer */
void* heap_listp;

/*
 * Insert ptr bp to appropriate position in segregated free list.
 */
static void insert_list(void* bp, size_t size)
{
	int class_idx = 0;										/* Size class index */
	void* class_ptr, * current_ptr, * last_ptr = NULL;		/* Size class pointer */

	/* Search list index corresponding to size */
	while ((size > 1) && (class_idx < MAXCLASS - 1)) {
		size >>= 1;
		class_idx ++;
	}
	class_ptr = heap_listp + class_idx * WSIZE;
	current_ptr = (void*)GET(class_ptr);

	/* Search insert position */
	while (current_ptr != NULL && (size > GET_SIZE(HDRP(current_ptr)))) {
		last_ptr = current_ptr;
		current_ptr = SUCC(current_ptr);
	}

	/* Insert */
	/* Case 1: insert into mid, last_ptr -> bp -> current_ptr */
	/* Case 2: insert into head, class_ptr (bp) -> current_ptr */
	/* Case 3: insert into tail, last_ptr -> bp -> current_ptr (NULL) */
	/* Case 4: empty list, class_ptr (bp) -> current_ptr (NULL) */
	PUT_P(PRED_PTR(bp), last_ptr);
	PUT_P(SUCC_PTR(bp), current_ptr);

	if (current_ptr != NULL)
		PUT_P(PRED_PTR(current_ptr), bp);

	if (last_ptr != NULL)		
		PUT_P(SUCC_PTR(last_ptr), bp);
	else						
		PUT_P(class_ptr, bp);
}

/*
 * remove_list - Remove ptr bp from segregated free list.
 */
static void remove_list(void* bp)
{
	int class_idx = 0;	/* Size class index */
	void* class_ptr;	/* Size class pointer */
	size_t size = GET_SIZE(HDRP(bp));

	/* Search list index corresponding to size */
	while ((size > 1) && (class_idx < MAXCLASS - 1)) {
		size >>= 1;
		class_idx ++;
	}
	class_ptr = heap_listp + class_idx * WSIZE;

	/* Remove */
	/* Case 1: remove from mid */
	/* Case 2: remove from head */
	/* Case 3: remove from tail */
	/* Case 4: only one pointer in list */
	if (PRED(bp) != NULL)
		PUT_P(SUCC_PTR(PRED(bp)), SUCC(bp));
	else PUT_P(class_ptr, SUCC(bp));

	if (SUCC(bp) != NULL)
		PUT_P(PRED_PTR(SUCC(bp)), PRED(bp));
}

/*
 * coalesce - Coalesce free blocks if they're adjacent. There are 4 cases (in textbook P.596 figure 9-40).
 */
static void* coalesce(void* bp, size_t size)
{
	size_t prev_alloc = GET_ALLOC(HDRP(PREV_BLKP(bp)));
	size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));

	if (prev_alloc && next_alloc);				/* Case 1 */

	else if (prev_alloc && !next_alloc) {		/* Case 2 */
		remove_list(NEXT_BLKP(bp));
		size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
		PUT(HDRP(bp), PACK(size, 0));
		PUT(FTRP(bp), PACK(size, 0));
	}

	else if (!prev_alloc && next_alloc) {		/* Case 3 */
		remove_list(PREV_BLKP(bp));
		size += GET_SIZE(HDRP(PREV_BLKP(bp)));
		PUT(FTRP(bp), PACK(size, 0));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		bp = PREV_BLKP(bp);
	}

	else {										/* Case 4 */
		remove_list(PREV_BLKP(bp));
		remove_list(NEXT_BLKP(bp));
		size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(HDRP(NEXT_BLKP(bp)));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
		bp = PREV_BLKP(bp);
	}

	insert_list(bp, size);
	return bp;
}

/*
 * extend_heap - Extend heap when: 1) initilize the heap, 2) mm_malloc cannot find a fit block.
 */
static void* extend_heap(size_t size)
{
	void* bp;	/* block pointer */

	/* Allocate an even number of words to maintain alignment */
	size = ALIGN(size);
	if ((long)(bp = mem_sbrk(size)) == -1)
		return NULL;

	/* Initialize free block header/footer and the epilogue header */
	PUT(HDRP(bp), PACK(size, 0));			/* Free block header */
	PUT(FTRP(bp), PACK(size, 0));			/* Free block footer */
	PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));	/* New epilogue header */

	/* Coalesce if the previous block was free */
	return coalesce(bp, size);
}

/*
 * place - Place asize into bp, split the block if neccessary.
 */
static void* place(void *bp, size_t asize)
{
	size_t csize = GET_SIZE(HDRP(bp)), remain = csize - asize;

	remove_list(bp);

	if (remain < (2 * DSIZE)) {
		PUT(HDRP(bp), PACK(csize, 1));
		PUT(FTRP(bp), PACK(csize, 1));
	}
	else if(asize < 96) {
		PUT(HDRP(bp), PACK(asize, 1));
		PUT(FTRP(bp), PACK(asize, 1));
		PUT(HDRP(NEXT_BLKP(bp)), PACK(remain, 0));
		PUT(FTRP(NEXT_BLKP(bp)), PACK(remain, 0));
		insert_list(NEXT_BLKP(bp), remain);
	}
	else {
		PUT(HDRP(bp), PACK(remain, 0));
		PUT(FTRP(bp), PACK(remain, 0));
		insert_list(bp, remain);
		bp = NEXT_BLKP(bp);
		PUT(HDRP(bp), PACK(asize, 1));
		PUT(FTRP(bp), PACK(asize, 1));
	}
	return bp;
}

/*
 * find_fit - Find a block in the segregated free list with fit size.
 *     Implement segregated fit.
 */
static void* find_fit(size_t asize)
{
	int class_idx = 0;
	void* bp = NULL;
	size_t size = asize;

	/* First-fit search */
	while (class_idx < MAXCLASS) {
		/* Search list index corresponding to size */
		if ((size <= 1) && ((bp = (void*)GET(heap_listp + class_idx * WSIZE)) != NULL)) {
			/* Search appropriate size */
			while ((bp != NULL) && (asize > GET_SIZE(HDRP(bp))))
				bp = SUCC(bp);
			if (bp != NULL)
				break;
		}

		size >>= 1;
		class_idx++;
	}
	return bp;
}

/* 
 * mm_init - initialize prologue header, epilogue header and segregated list (size class list).
 */
int mm_init(void)
{
	int i;
	/* Create the initial empty heap */
	if ((heap_listp = mem_sbrk((3 + MAXCLASS) * WSIZE)) == (void*)-1)
		return -1;

	/* Initialize segregated list */
	for (i = 0; i < MAXCLASS; i++)
		PUT_P(heap_listp + (i * WSIZE), NULL);

	PUT(heap_listp + (MAXCLASS * WSIZE), PACK(DSIZE, 1));		/* Prologue header */
	PUT(heap_listp + ((1 + MAXCLASS) * WSIZE), PACK(DSIZE, 1));	/* Prologue footer */
	PUT(heap_listp + ((2 + MAXCLASS) * WSIZE), PACK(0, 1));		/* Epilogue header */

	/* Extend the empty heap with a free block of CHUNKSIZE bytes */
	if (extend_heap(CHUNKSIZE) == NULL)
		return -1;
    return 0;
}

/* 
 * mm_malloc - Allocate a block by finding a fit block. If no fit block, extend the heap.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
	size_t asize;		/* Adjusted block size */
	size_t extendsize;	/* Amount to extend heap if no fit */
	char* bp;

	/* Ignore spurious request */
	if (size == 0)
		return NULL;

	/* Adjust block size to include overhead and alignment requsts */
	if (size <= DSIZE)
		asize = 2 * DSIZE;
	else
		asize = ALIGN(size + DSIZE);

	/* Search the free list for a fit */
	if ((bp = find_fit(asize)) != NULL)
		return place(bp, asize);

	/* No fit block found. Get more memory and place the block */
	extendsize = MAX(asize, CHUNKSIZE);
	if ((bp = extend_heap(extendsize)) == NULL)
		return NULL;
	return place(bp, asize);
}

/*
 * mm_free - Freeing a block by setting its head and tail mark, then do coalesce if possible.
 */
void mm_free(void *bp)
{
	size_t size = GET_SIZE(HDRP(bp));

	PUT(HDRP(bp), PACK(size, 0));
	PUT(FTRP(bp), PACK(size, 0));
	coalesce(bp, size);
}

/*
 * mm_realloc - Examine if nearest block is free. Coalesce them if the sum of their sizes
 *     is enough for realloc, extend heap otherwise.
 */
void* mm_realloc(void* ptr, size_t size)
{
	void* newptr = ptr;
	int remain;

	if (size == 0)
		return NULL;

	/* Align */
	if (size <= DSIZE)
		size = 2 * DSIZE;
	else
		size = ALIGN(size + DSIZE);

	/* New size < origin size, do nothing */
	if ((remain = GET_SIZE(HDRP(ptr)) - size) >= 0)
		return newptr;

	/* Examine nearest block */
	if (!GET_ALLOC(HDRP(NEXT_BLKP(ptr))) || !GET_SIZE(HDRP(NEXT_BLKP(ptr)))) {
		/* Not enough and need extend */
		if ((remain = GET_SIZE(HDRP(ptr)) + GET_SIZE(HDRP(NEXT_BLKP(ptr))) - size) < 0) {
			if (extend_heap(MAX(-remain, CHUNKSIZE)) == NULL)
				return NULL;
			remain += MAX(-remain, CHUNKSIZE);
		}
		/* Remove next block */
		remove_list(NEXT_BLKP(ptr));
		PUT(HDRP(ptr), PACK(size + remain, 1));
		PUT(FTRP(ptr), PACK(size + remain, 1));
	}
	/* No proper free block */
	else {
		newptr = mm_malloc(size);
		memcpy(newptr, ptr, GET_SIZE(HDRP(ptr)));
		mm_free(ptr);
	}

	return newptr;
}
