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
#include <math.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "OgdenGang",
    /* First member's full name */
    "HeartStoller",
    /* First member's email address */
    "heartstoller@hacker.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

#define ALIGNMENT 8 // single word (4) or double word (8) alignment
#define WSIZE 4 // word
#define DSIZE 8 // dword
#define CHUNKSIZE (1 << 12) // Extend heap by this amount(bytes)

#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7) // rounds up to the nearest multiple of ALIGNMENT
#define MAX(x, y) ((x) > (y) ? (x) : (y)) // find maximum between 2
#define SIZE_T_SIZE (ALIGN(sizeof(size_t))) // get size of size_t of current system

/*Pack a size and allocated bit in to a word, used for setting allocation status kinda things*/
#define PACK(size, alloc) ((size) | (alloc))

/*Read and write a word at address p, acts like getter and setter for pointed values*/
#define GET(p) (*(unsigned int*)(p))
#define PUT(p, val) (*(unsigned int*)(p) = (val))

/*Read the size and allocated fields from address p, get size and allocation status of a block*/
#define GET_SIZE(p) (GET(p) & ~0x7)      // header pointer as input
#define GET_ALLOC(p) (GET(p) & 0x1)      // header pointer as input

/*Given block ptr bp,compute address of its header and footer*/
#define HDRP(bp) ((char*)(bp) - WSIZE)
#define FTRP(bp) ((char*)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/*Given block ptr bp,compute address of next and previous blocks*/
#define NEXT_BLKP(bp) ((char*)(bp) + GET_SIZE(((char*)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char*)(bp) - GET_SIZE(((char*)(bp) - DSIZE)))

#define GET_CURR_NEXT_PTR(bp) (void **)(HDRP(bp) + (WSIZE))
#define GET_CURR_PREV_PTR(bp) (void **)(FTRP(bp) - (WSIZE))

#define PUT_PTR(p, val) (*(unsigned int*)(p) = (unsigned int)(val))

#define INSIDE(bp) (*(void **)bp)

#define GET_PTR(ptr) (*(void **)bp) 


// TODO DO:
/*
- Coalescing --> merging adjacent free block to reduce fragmentation --> i think best time to do is right after free
- 
*/

// global vars
static void *heap_listp;
static void *free_listp = NULL;

int var = 1;

static void *tail = NULL;
static void add_to_list(void *bp){
    // printf("bp %p", bp);
    // printf("tail %p", tail);
    if(free_listp == NULL){ // 1st free
        free_listp = bp;
        PUT(GET_CURR_NEXT_PTR(bp), 0);
        PUT(GET_CURR_PREV_PTR(bp), 0);
    }
    else{
        PUT(GET_CURR_NEXT_PTR(bp), 0);
        PUT(GET_CURR_PREV_PTR(bp), tail);
        PUT(GET_CURR_NEXT_PTR(tail), bp);
    }
    tail = bp;
}

static void remove_from_list(void *bp){
    void *iter = (void *)free_listp;

    if(*(void **)free_listp == 0){
        free_listp = 0;
        return;
    }

    if(bp == free_listp){
        void *prev_block = free_listp;
        free_listp = *(int *)free_listp;
        void *next_block = free_listp;
        PUT(GET_CURR_PREV_PTR(next_block), 0);
        PUT(GET_CURR_NEXT_PTR(prev_block), 0);
        PUT(GET_CURR_PREV_PTR(prev_block), 0);
        return;
    }

    while(iter != NULL){
        if(iter == bp){
            // printf("if");
            // printf("%p", iter);
            void *prev = *(void **)GET_CURR_PREV_PTR(bp);
            void *next = *(void **)GET_CURR_NEXT_PTR(bp);

            // printf("prev %p", prev); // confirmed
            // printf("next %p", next); // confirmed
            
            // last item in the list and list is long
            if(*(void **)iter == 0){
                PUT(GET_CURR_NEXT_PTR(prev), 0);
                tail = prev;
            }
            else{
                PUT(GET_CURR_NEXT_PTR(prev), next);
                PUT(GET_CURR_PREV_PTR(next), prev);
            }
            PUT(GET_CURR_NEXT_PTR(bp), 0);
            PUT(GET_CURR_PREV_PTR(bp), 0);
            return;
        }
        else{
            // printf("else");
            iter = *(void **)GET_CURR_NEXT_PTR(iter);
        }
    }
}

static void *coalesce(void *bp){
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if(prev_alloc && next_alloc){ // case1
        // printf("\ncoalesce 1\n");
        return bp;
    }
    else if(prev_alloc && !next_alloc){ // case2
        // printf("\ncoalesce 2\n");
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        remove_from_list(NEXT_BLKP(bp));
        remove_from_list(bp);
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    else if(!prev_alloc && next_alloc){ // case3
        // printf("\ncoalesce 3\n");
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        // printf("current %p", bp);
        remove_from_list(bp);
        // printf("previous %p", PREV_BLKP(bp));
        remove_from_list(PREV_BLKP(bp));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    else{ // case4
        // printf("\ncoalesce 4\n");
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        remove_from_list(NEXT_BLKP(bp));
        remove_from_list(PREV_BLKP(bp));
        remove_from_list(bp);
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    add_to_list(bp);
    return bp;
}


static void *extend_heap(size_t words){
    char *bp;
    size_t size;

    // allocate an even number of words to maintain alignment
    size = (words + (words % 2)) * WSIZE;
    if((int)(bp = mem_sbrk(size)) == -1){
        return NULL;
    }
   
    // initialize free block header/footer and the epilogue header
    PUT(HDRP(bp), PACK(size, 0)); // free block header
    PUT(FTRP(bp), PACK(size, 0)); // free block footer
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));// new epilogue header

    // coalesce if the previous block was free
    // return coalesce(bp);
    return bp;
}


static void *find_fit(size_t search_size){
    if(!free_listp){
        return NULL;
    }

    void *current_free = free_listp;

    while(GET_CURR_NEXT_PTR(current_free) != NULL){
        if(GET_ALLOC(HDRP(current_free)) == 0 && search_size <= GET_SIZE(HDRP(current_free))){
            return current_free;
        }
        else{
            current_free = *(void **)GET_CURR_NEXT_PTR(current_free);
        }
    }
    return NULL; // no fit
}

static void place(void *bp, size_t req_size){
    size_t curr_size = GET_SIZE(HDRP(bp));
    size_t rem_size = curr_size - req_size;

    if(rem_size >= (2*DSIZE)){
        // printf("splitting");
        PUT(HDRP(bp), PACK(req_size, 1)); // hdr for allocated block
        PUT(FTRP(bp), PACK(req_size, 1)); // ftr for allocated block

        // printf("%d", GET_ALLOC(HDRP(bp)));
        bp = NEXT_BLKP(bp);
        // printf("%d", GET_ALLOC(HDRP(bp)));

        PUT(HDRP(bp), PACK(rem_size, 0)); // hdr for remaining
        PUT(FTRP(bp), PACK(rem_size, 0)); // ftr for remaining
        add_to_list(bp);
        coalesce(bp);
    }
    else{
        // if not allocate entire block, no splitting
        // printf("full allocation");
        PUT(HDRP(bp), PACK(curr_size, 1));
        PUT(FTRP(bp), PACK(curr_size, 1));
    }
}


/* 
 * mm_init - initialize the malloc package.
 */

int mm_init(void){
    // initial empty heap
    // if(var){
    heap_listp = mem_sbrk(4 * WSIZE);
    if(heap_listp == (void *)-1){
        return -1;
    }
    PUT(heap_listp, 0);                            // padding for alignment ig
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); // prologue head
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); // prologue foot
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));     // epilogue hdr, marks end of heap
    heap_listp += DSIZE;  // now heap ptr points to after prologue
    free_listp = NULL;
    // extend_heap(CHUNKSIZE / WSIZE); // 1024
    // extend_heap(4); // for testing
    // NOTE: 4 blocks
    // printf("\nfreelist --> %p\n", &free_listp);
    var = 0;
    return 0;
    // }
}


/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size){
    // size_t not negative, so wrap around
    if(size == 0){
        return NULL;
    }
    
    size_t search_size; // size to search for
    void *temp_ptr;

    // size adjustments
    if (size <= DSIZE){
        search_size = 2 * DSIZE; // forces to 16 bytes
    }
    else{
        search_size = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);
    }

    // check for fit
    temp_ptr = find_fit(search_size);
    if(temp_ptr != NULL){
        // printf("fit found %p", temp_ptr);
        remove_from_list(temp_ptr);
        place(temp_ptr, search_size);
        return temp_ptr;
    }

    // if no fit found, extend heap
    temp_ptr = extend_heap(search_size / WSIZE);
    if (temp_ptr == NULL){
        return NULL;
    }
    place(temp_ptr, search_size);
    return temp_ptr;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr){
    if(ptr == NULL){
        return;
    }
    if(GET_ALLOC(HDRP(ptr)) == 1){
        size_t size = GET_SIZE(HDRP(ptr));
        PUT(HDRP(ptr), PACK(size, 0));
        PUT(FTRP(ptr), PACK(size, 0));
        add_to_list(ptr);
    }
    coalesce(ptr);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size){

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
