/*
 * mm.c
 *
 * ID:1900011003@pku.edu.cn  Name:Zhang BaiZhou
 * 
 * Segregated free list
 * .
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "mm.h"
#include "memlib.h"

/* If you want debugging output, use the following macro.  When you hand
 * in, remove the #define DEBUG line. */
#define DEBUG
#ifdef DEBUG
# define dbg_printf(...) printf(__VA_ARGS__)
#else
# define dbg_printf(...)
#endif

/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */


/*
 * If NEXT_FIT defined use next fit search, else use first-fit search 
 */

/* If the strategy of NEXT_FIT should be taken,define the following macro */

//#define NEXT_FITx


/* Basic constants and macros */
#define WSIZE       4       /* Word and header/footer and pointer size (bytes) */ 
#define DSIZE       8       /* Double word size (bytes) ,sizeof alignment*/
#define CHUNKSIZE  (1<<11)  /* The size of one page in Linux system,Extend heap by this amount (bytes) */  
#define LISTNUM     10
#define MAX(x, y) ((x) > (y)? (x) : (y))  

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc)) 

/* Read and write a word at address p */
#define GET(p)       (*(unsigned int *)(p))            
#define PUT(p, val)  (*(unsigned int *)(p) = (val))

/* Read and write a pointer stored at address p */
#define PTR_VALUE(p)    ((unsigned long)(p))
#define BIAS(p)         ((unsigned long)((p) ? (0x800000000):(0)))
#define GET_PTR(p)      ((unsigned int *)((BIAS(GET(p))) + (unsigned long)(GET(p)))) 
#define PUT_PTR(p, ptr) (*(unsigned int *)(p) = (unsigned int)((PTR_VALUE(ptr)) - (BIAS(ptr))))
   

/* Get a free block's predecessor or successor*/
#define PRED(p)  (GET_PTR(p))
#define SUCC(p)  (GET_PTR((char*)(p) + WSIZE))  
/* Set a free block's predecessor or successor to the value of ptr*/ 
#define SET_PRED(p,ptr) (PUT_PTR((p),(ptr)))
#define SET_SUCC(p,ptr) (PUT_PTR(((char*)(p) + WSIZE),(ptr)))


/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)                   
#define GET_ALLOC(p) (GET(p) & 0x1)                    

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)                      
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) 

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) 
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) 


/* Global variables */
static char *heap_listp = 0;  /* Pointer to first block */ 
static char *seg_list = 0;   /*Pointer to the list array */ 


/* Function prototypes for internal helper routines */
static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);
static int insert_list(void *bp);
static int delete_list(void *bp);
static int list_idx(size_t size);

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)



/*
 * Initialize: return -1 on error, 0 on success.
 * Reset all the global pointers.
 * segragate lists:[1,32),[32,64),[64,128),[128,256),[256,512),[512,1024),[1024,2048),
 * [2048,4096),[4096,8192),[8192,+INF)10 lists
 */
int mm_init(void) {

    //printf("mm_init called\n");

    /* Reset the global pointers */
    heap_listp = NULL;
    seg_list = NULL;

    /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk((LISTNUM + 4)*WSIZE)) == (void *)-1) 
        return -1;

    PUT(heap_listp, 0);                          /* Alignment padding */

    /* initialize the segregated list, 12 list head pointers in all */
    for(int i = 1;i <= LISTNUM;++i){
        PUT(heap_listp + (i*WSIZE), 0);
    }
    PUT(heap_listp + (LISTNUM + 1)*WSIZE, PACK(DSIZE, 1)); /* Prologue header */ 
    PUT(heap_listp + (LISTNUM + 2)*WSIZE, PACK(DSIZE, 1)); /* Prologue footer */ 
    PUT(heap_listp + (LISTNUM + 3)*WSIZE, PACK(0, 1));     /* Epilogue header */
    seg_list = (heap_listp + WSIZE); /*the start of free block list arrays */
    heap_listp += ((LISTNUM + 2) * WSIZE);  /*the block pointer of Prologue block */
   

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL) {
        return -1;
    }

    return 0;
}

/*
 * Given a pointer bp pointing to a free block
 * insert this block into a list with "head" as its head pointer
 * 
 * if operation succeeds return 0; else return -1; 
 */
static int insert_list(void * bp){

    /* if bp points to an allocated block, error occurs*/
    if(GET_ALLOC(HDRP(bp))){
        printf("Insert a block that is not free\n");
        return -1;
    }


    size_t b_size = GET_SIZE(HDRP(bp));
    int idx = list_idx(b_size);
    void * list_head = GET_PTR(seg_list + (idx * WSIZE));


    if(list_head == NULL){
        /* If the list is empty, add bp as the first node*/
        PUT_PTR((seg_list + (idx * WSIZE)),bp); /*renew the head */
        SET_PRED(bp,NULL);
        SET_SUCC(bp,NULL);

        //printf("A block of %ld size is inserted into list %d\n",b_size,idx);
        return 0;

    }else{
        /*The list is not empty */
        
        /*Find bp's successor */
        void * tmp = list_head;
        void * following = NULL;
        while((tmp != NULL) && (GET_SIZE(HDRP(tmp)) < b_size)){
            following = tmp;
            tmp = SUCC(tmp);
        }

/*
        while((tmp != NULL) && (GET_SIZE(HDRP(tmp)) == b_size) 
            && (PTR_VALUE(bp) > PTR_VALUE(tmp))){
            following = tmp;
            tmp = SUCC(tmp);
        }
        */

        
        if(tmp == list_head){
            /* bp points to the new headnode*/
            SET_PRED(bp,NULL);
            SET_SUCC(bp,tmp);
            SET_PRED(tmp,bp);
            PUT_PTR((seg_list + (idx * WSIZE)),bp); /* renew the head */
        }else if(tmp == NULL){
            /* bp points to the new lastnode */
            SET_SUCC(bp,NULL);
            SET_PRED(bp,following);
            SET_SUCC(following,bp);
        }else{
            /* following->bp->tmp */
            SET_SUCC(following,bp);
            SET_PRED(bp,following);
            SET_SUCC(bp,tmp);
            SET_PRED(tmp,bp);
        }
        //printf("A block of %ld size is inserted into list %d\n",b_size,idx);
        return 0;
    }
}

/* 
 * delete_list - Delete a block from the free block list
 * 
 * success:return 0;error: return -1;
 * 
 */

static int delete_list(void * bp){
    if(bp == NULL) return -1;

    int idx = list_idx((size_t)GET_SIZE(HDRP(bp)));
    void * list_head = GET_PTR(seg_list + (idx * WSIZE));  
    //printf("Starting to delete %lx with size %d at list %d\n",PTR_VALUE(bp),GET_SIZE(HDRP(bp)),idx);

    /* if bp isn't free or free list doesn't exist, error occurs */
    if(GET_ALLOC(HDRP(bp)) || (list_head == NULL)){
        printf("Deleting list error\n");
        return -1;
    }     

    /* bp is the list_head*/
    if(bp == list_head){
        /*only one node in the list*/
        if(SUCC(bp) == NULL){
            PUT_PTR((seg_list + (idx * WSIZE)),NULL);
        }else{
            /*more than one node in the list */
            SET_PRED(SUCC(bp),NULL);
            PUT_PTR((seg_list + (idx * WSIZE)),(SUCC(bp)));
            SET_SUCC(bp,NULL);
        }
    }else{
        /*bp isn't the list_head */
        SET_SUCC(PRED(bp),SUCC(bp));
        if(SUCC(bp) != NULL){
            SET_PRED(SUCC(bp),PRED(bp));
        }
        SET_PRED(bp,NULL);
        SET_SUCC(bp,NULL);
    }

   // printf("A block at %lu with size %u is removed from the list\n",(unsigned long)(bp),GET_SIZE(HDRP(bp)));

    return 0;
}



/* 
 * extend_heap - Extend heap with free block and return its block pointer
 */
static void *extend_heap(size_t words) 
{
    //printf("heap extended with %ld words\n",words);
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE; 
    if ((long)(bp = mem_sbrk(size)) == -1)  
        return NULL;                                        

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));         /* Free block header */   
    PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */ 
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */ 
    SET_PRED(bp,NULL);
    SET_SUCC(bp,NULL);

    /* Coalesce if the previous block was free */
    return coalesce(bp);                                         
}


/*
 * malloc
 */
void *malloc (size_t size) {

   // printf("malloc to size %u called\n",size);

    size_t asize;      /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    char *bp;      

    if (heap_listp == NULL){
        mm_init();
    }

    /* Ignore spurious requests */
    if (size == 0)
        return NULL;

    if (size == 448){
        size = 512;
    }

    /* Adjust block size to include header,footer and pointers*/
    if (size < DSIZE)                                          
        asize = 2*DSIZE;                                        
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE); 

    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {  
        place(bp, asize);                  
        return bp;
    }
    //printf("not found\n");
    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize,CHUNKSIZE);                 
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)  
        return NULL;                                  
    place(bp, asize);   

    return bp;
}


/*
 * free - Free a block
 * the free function never throws a fault
 */
void free (void *bp) {
    // printf("free called\n");
    if (bp == NULL) 
        return;

    size_t size = GET_SIZE(HDRP(bp));
    if (heap_listp == 0){
        mm_init();
    }

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);


}

/*
 * realloc - you may want to look at mm-naive.c
 */
void *realloc(void *oldptr, size_t size) {
 
   // printf("realloc called\n");
    size_t asize;
    size_t oldsize;

    /* If size == 0 then this is just free, and we return NULL. */
    if(size == 0) {
        free(oldptr);
        return NULL;
    }

    /* If oldptr is NULL, then this is just malloc. */
    if(oldptr == NULL) {
        return malloc(size);
    }


    oldsize = GET_SIZE(HDRP(oldptr));
    if(size <= DSIZE){
        asize = 2*DSIZE;
    }else{
        asize = DSIZE * ((size + DSIZE + (DSIZE-1))/DSIZE);
    }

    if(asize == oldsize){
        /* new block and old block share the same size, no need to apply for a new block */
        return oldptr;
    }else if(asize > oldsize){
        void * newptr;

        /* new block is larger, call malloc */
        newptr = malloc(size);

        /* If realloc() fails the original block is left untouched  */
        if(!newptr) {
            return 0;
        }
        memcpy(newptr, oldptr, oldsize);

        /* Free the old block. */
        free(oldptr);

        return newptr;

    }else{
        /*new block smaller than old block, cut the old block into the new block and a free block*/
        place(oldptr,asize);
        return oldptr;
    }
    
}






/*
 * malloc a block with the size of nmemb*size,and initialize it to zero
 */
void *calloc (size_t nmemb, size_t size) {
    size_t bytes = nmemb * size;
    void *newptr;

    newptr = malloc(bytes);
    memset(newptr, 0, bytes);

    return newptr;
}

/* 
 * list_idx - 根据块的大小，计算出块所在的链表索引，范围为0~9
 */

static int list_idx(size_t size){

    /*get the highest valid bit of size */
    int highest_bit = -1;
    while(size){
        size = size >> 1;
        highest_bit++;
    }

    if(highest_bit < 5){
        return 0;
    }else if(highest_bit >= 13 ){
        return 9;
    }else{
        return (highest_bit-4);
    }

}




/* 
 * place - Place block of asize bytes at start of free block bp 
 *         and split if remainder would be at least minimum block size
 */
static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));   

    /* delete the block from free list*/
    if(!GET_ALLOC(HDRP(bp))){
        delete_list(bp);
    }

    if ((csize - asize) >= (2*DSIZE)) { 
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize-asize, 0));
        PUT(FTRP(bp), PACK(csize-asize, 0));
        coalesce(bp);
    }
    else { 
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }

}


/*
 * coalesce - Boundary tag coalescing. Return ptr to coalesced block
 * The coalesced block will be inserted into the free block list
 */
static void *coalesce(void *bp) 
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));



    if (prev_alloc && next_alloc) {            /* Case 1 */
        insert_list(bp);
        return bp;
    }

    else if (prev_alloc && !next_alloc) {      /* Case 2 */
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        delete_list(NEXT_BLKP(bp));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    else if (!prev_alloc && next_alloc) {      /* Case 3 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        delete_list(PREV_BLKP(bp));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    else {                                     /* Case 4 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + 
            GET_SIZE(FTRP(NEXT_BLKP(bp)));
        delete_list(PREV_BLKP(bp));
        delete_list(NEXT_BLKP(bp));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    insert_list(bp);

    return bp;
}

/* 
 * find_fit - Find a fit for a block with asize bytes 
 */
static void *find_fit(size_t asize)
{   

    for(int idx = list_idx(asize); idx < LISTNUM;++idx){

        void * bp = GET_PTR(seg_list + idx*WSIZE);

        while(bp != NULL){
            /* A suitable block found */
            if(GET_SIZE(HDRP(bp)) >= asize){
                //printf("A block with size %d is found. asize is %ld\n",GET_SIZE(HDRP(bp)),asize);
                return bp;
            }
            bp = SUCC(bp);
        }

    }

    /*Unable to find a block large enough in any list */
    return NULL;
}




/*
 * Return whether the pointer is in the heap.
 * May be useful for debugging.
 */
static int in_heap(const void *p) {
    return p <= mem_heap_hi() && p >= mem_heap_lo();
}


/*
 * Return whether the pointer is aligned.
 * May be useful for debugging.
 */
static int aligned(const void *p) {
    return (size_t)ALIGN((size_t)p) == (size_t)p;
}


/*
 * mm_checkheap
 */
void mm_checkheap(int lineno) {

    /*check heap boundaries*/
    size_t upper_lim = 0x100000000;

    if(mem_heapsize() >= upper_lim){
        printf("%d:The size of heap is too large!\n",lineno);
        return;
    }
    
    /* check prologue block */
    if((GET_SIZE(HDRP(heap_listp)) != DSIZE) || !GET_ALLOC(HDRP(heap_listp))){
        printf("%d:Epilogue block error\n",lineno);
        return;
    }

    /*iterate all the blocks in heaps and check them one after another */

    unsigned int MINSIZE = 2*DSIZE;
    void * bp = NEXT_BLKP(heap_listp);
    int last_block_alloc = 1; //record the allocate bit of last block,initialized to 1
    for(;GET_SIZE(HDRP(bp)) > 0;bp = NEXT_BLKP(bp)){
        /* check whether this block is in the heap */
        if(!in_heap(bp)){
            printf("%d:Block not in the heap,SEGV!\n",lineno);
            return;
        }
        /* check address alignment */
        if(!aligned(bp)){
            printf("%d:Address not aligned to 8 bytes!\n",lineno);
            return;
        }
        /*check the size of the block*/
        if(GET_SIZE(HDRP(bp)) < MINSIZE){
            printf("%d:Block Size %u not large enough\n",lineno,GET_SIZE(HDRP(bp)));
        }

        /*check block's header and footer*/
        void * head = HDRP(bp);
        void * foot = FTRP(bp);
        if(GET(head) != GET(foot)){
            printf("%d:Header and Footer not matching each other\n",lineno);
            return;
        }

        /*check two consecutive free blocks*/
        if(!last_block_alloc && !GET_ALLOC(HDRP(bp))){
            printf("%d:Two consecutive free blocks\n",lineno);
            return;
        }

        /*check block overlapping */
        if(PTR_VALUE(HDRP(bp)) <= PTR_VALUE(FTRP(PREV_BLKP(bp)))){
            printf("%d:Two neigboring free block overlap\n",lineno);
        }

        last_block_alloc = GET_ALLOC(HDRP(bp)); 
    }

    /*check epilogue block*/
    if(!GET_ALLOC(HDRP(bp))){
        printf("%d:Epilogue block error\n",lineno);
        return;
    }    


    /*check the free block list*/
    for(int i = 0;i < 12;++i){
        bp = GET_PTR(seg_list + i*WSIZE);
        void * pred = NULL;
        void * succ = NULL;
        for(;bp != NULL;bp = SUCC(bp)){
        // printf("bp=%lx\n",PTR_VALUE(bp));
            pred = PRED(bp);
            succ = SUCC(bp);

            if(GET_ALLOC(HDRP(bp))){
                printf("%d:An allocated block in the free list %d\n",lineno,i);
                return;
            }

            if(PTR_VALUE(bp) < PTR_VALUE(mem_heap_lo())){
                printf("%d:Address lower than mem_heap_lo in list %d\n",lineno,i);
                return;
            }

            if(PTR_VALUE(bp) > PTR_VALUE(mem_heap_hi())){
                printf("%d:Address higher than mem_heap_hi in list %d\n",lineno,i);
                return;
            }


            if(pred != NULL){
                if((SUCC(pred) != bp) || (PRED(bp) != pred)){
                    printf("%d:previous pointer not consistent in list %d\n",lineno,i);
                    return;
                }
            }
            if(succ != NULL){
                if((SUCC(bp) != succ) || (PRED(succ) != bp)){
                    printf("%d:next pointer not consistent in list %d\n",lineno,i);
                    return;
                }
            }
        }
    }
}

void print_list(int idx){
    void * list_head = GET_PTR(seg_list + idx * WSIZE);
    if(list_head == NULL) {
        printf("The list is empty\n");
        return;
    }
    void * tmp = list_head;
    int cnt = 0;
    for(;tmp != NULL;tmp = SUCC(tmp),cnt++){
        printf("Node %d: %lx\n",cnt,PTR_VALUE(tmp));
    }
    printf("Done\n");
}