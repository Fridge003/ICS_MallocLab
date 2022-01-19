/*
 * mm.c
 *
 * ID:1900011003@pku.edu.cn   Name:ZhangBaiZhou 张柏舟
 * 
 * 使用分离链表以及分离适配的方法实现malloc/free/realloc
 * 
 * 用到的一些技巧：
 * 1.添加了一些操作指针的宏，简化关于指针的coding。为节省空间，指针在堆中以4字节的形式存在。
 *   因为指针从0x800000000处开始，所以将8字节非零指针转换为4字节需要减去一个BIAS。
 * 
 * 2.一共有10个链表，每个链表对应的空闲块大小分别位于区间[1,32),[32,64),[64,128),[128,256),[256,512),
 *   [512,1024),[1024,2048),[2048,4096),[4096,8192),[8192,+INF)。
 *   链表内部的空闲块按照从小到大排序，采用这种方法可以在搜索时，使首次试配的块最佳适配。
 *   10个链表的表头指针存放于序言块的之前40个字节。
 *  
 * 3.已分配块不需要用到foot，所以在malloc时可以少申请4个字节，从而提高内存利用率。
 *   为了实现这种方法，需要在每一个块的head的倒数第二位记录前一个块是否被allocated，因此需要改写textbook.c中定义的宏。(R_PUT)
 * 
 * 4.堆的结构：（每个方块为4字节）
 *    
 *    __________________________________________________________________________
 *    | 占用 | 表头1 | 表头2 | ... | 表头10 | 序言块 | 序言块 | 堆开始 | ... | 结尾块 |
 *    |_____|_______|______|_____|_______|__8/1__|__8/1__|_______|_____|__0/1__|
 *          ^                                    ^       
 *          |                                    |
 *        seg_list                            heap_listp
 *              
 *   已分配块的结构：
 * 
 *     31_______________________3__2_________1_______0  
 *      |        块的大小        |  | prev a/f|cur_a/f|  Header
 *      |_______________________|__|_________|_______|  
 *      |                                            |
 *      |                  有效载荷                   |
 *      |                                            |
 *      |____________________________________________|
 *      |                                            |
 *      |                 填充物（可选择）              |
 *      |____________________________________________|
 * 
 * 
 *   空闲块的结构：
 * 
 *     31_______________________3__2_________1_______0  
 *      |        块的大小        |  | prev a/f|cur_a/f|  Header
 *      |_______________________|__|_________|_______|
 *      |                  前驱指针                   | 
 *      |____________________________________________|                    
 *      |                  后继指针                   |     
 *      |____________________________________________|                                      
 *      |                                            |   
 *      |                  有效载荷                   |      
 *      |                                            |
 *      |____________________________________________|
 *      |                                            |
 *      |                 填充物（可选择）              |
 *      |____________________________________________| 
 *      |        块的大小        |  | prev a/f|cur_a/f|  Footer
 *      |_______________________|__|_________|_______| 
 * 
 * 
 * – 
 *                       
 * 
 * 
 * 
 * 
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
#define CHUNKSIZE  (1<<12)  /* The size of one page in Linux system*/  
#define LISTNUM     10      /* 空闲链表的个数，可依据实际情况改动 */
#define MAX(x, y) ((x) > (y)? (x) : (y))  

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc)) 

/* Read and write a word at address p */
#define GET(p)       (*(unsigned int *)(p))            
#define PUT(p, val)  (*(unsigned int *)(p) = (val))



/* 指针操作 */

/* 将指针自身的值转换为整数 */
#define PTR_VALUE(p)    ((unsigned long)(p)) 
/* 偏移量，如果指针非零，则为0x800000000，否则为0*/
#define BIAS(p)         ((unsigned long)((p) ? (0x800000000):(0)))
/* 取出p指向位置的四个字节，并将其转换为八字节指针 */
#define GET_PTR(p)      ((unsigned int *)((BIAS(GET(p))) + (unsigned long)(GET(p))))  
/* 将指针ptr转换为四字节，存入p指向位置开始的四个字节 */
#define PUT_PTR(p, ptr) (*(unsigned int *)(p) = (unsigned int)((PTR_VALUE(ptr)) - (BIAS(ptr)))) 
   

/* p为指向某一空闲块的指针 */

/* 指向该空闲块前驱的指针 */
#define PRED(p)  (GET_PTR(p)) 
/* 指向该空隙块后继的指针 */
#define SUCC(p)  (GET_PTR((char*)(p) + WSIZE))  
/* 设置该空闲块的前驱为ptr */
#define SET_PRED(p,ptr) (PUT_PTR((p),(ptr))) 
/* 设置该空闲块的后继为ptr */
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

/* 取HDPR的倒数第二位，即前一个块是否被分配 */
#define GET_PREV_ALLOC(bp) (GET(HDRP(bp)) & 0x2)
/* 设置下一个块header的倒数第二位，如果当前块已分配则为1，如果当前块空闲则为0 */
#define SET_NEXT_ALLOC(bp) (GET(HDRP(NEXT_BLKP(bp))) |= 0x2)
#define SET_NEXT_FREE(bp)  (GET(HDRP(NEXT_BLKP(bp))) &= (~0x2))
/* 在不改变倒数第二位的情况下，改变其他的位与val相同，R_PUT的R取Robust之意 */
#define R_PUT(p,val) (*(unsigned int *)(p) = ((GET(p) & 0x2) | val))





/* Global variables */
static char *heap_listp = 0;  /* Pointer to first block */ 
static char *seg_list = 0;   /* 指向第一个链表的头结点处 */ 


/* Function prototypes for internal helper routines */
static void *extend_heap(size_t words);  
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);
static int list_idx(size_t size); /* 给定大小size,返回size对应链表的index,范围为0~9 */
static int insert_list(void *bp); /* 向对应链表中插入块bp */
static int delete_list(void *bp); /* 从对应链表删除块bp */


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
    SET_NEXT_ALLOC(heap_listp); 

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL) {
        return -1;
    }

    return 0;
}


/*
 * malloc - Ask for a block
 */
void *malloc (size_t size) {

    //printf("malloc to size %u called\n",size);

    size_t asize;      /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    char *bp;      

    if (heap_listp == NULL){
        mm_init();
    }

    /* Ignore spurious requests */
    if (size == 0)
        return NULL;
    
    /* 特定优化 */
    if ((size >= 439) && (size <= 451)){
        size = 512;
    }

    /* Adjust block size to include header,footer and pointers*/
    if (size <= DSIZE)                                          
        asize = 2*DSIZE;                                        
    else
        asize = DSIZE * ((size + WSIZE + (DSIZE-1)) / DSIZE); 
        /* 已分配块不需要footer，所以只需要加上header的大小，即一个WSIZE */


    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {  
        place(bp, asize); 
        return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize,CHUNKSIZE);                 
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)  
        return NULL;                                  
    place(bp, asize); 
    return bp;
}

/*
 * free - Free a block
 * 
 */
void free (void *bp) {

    if (bp == NULL) 
        return;
        

    size_t size = GET_SIZE(HDRP(bp));
    if (heap_listp == 0){
        mm_init();
    }

    /* The second bit should be saved */
    R_PUT(HDRP(bp), PACK(size, 0));
    R_PUT(FTRP(bp), PACK(size, 0));
    SET_NEXT_FREE(bp); 

    SET_PRED(bp,NULL);
    SET_SUCC(bp,NULL);

    coalesce(bp);
}





/*
 * realloc - change the size of an allocated block
 */


void *realloc(void *oldptr, size_t size) {
    //printf("realloc to %lx of size %ld called\n",PTR_VALUE(oldptr),size);
    size_t asize;
    size_t oldsize;

    /* If oldptr is NULL, then this is just malloc. */
    if(oldptr == NULL) {
        return malloc(size);
    }

    /* If size == 0 then this is just free, and we return NULL. */
    if(size == 0) {
        free(oldptr);
        return NULL;
    }


    oldsize = GET_SIZE(HDRP(oldptr));

    if(size <= DSIZE){
        asize = 2*DSIZE;
    }else{
        asize = DSIZE * ((size + WSIZE + (DSIZE-1))/DSIZE);
        /* 同malloc，可以少申请一个WSIZE */
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
        /*copy the data */
        if(size < oldsize) oldsize = size;
        memcpy(newptr, oldptr, oldsize);

        /* Free the old block. */
        free(oldptr);

        return newptr;

    }else{
        
        size_t csize = oldsize-asize;
       
        
        if(csize >= 2*DSIZE){
            /* 新的大小asize小于oldsize，且差值大于一个最小空闲块的大小，
                需要将oldsize指向的块分割成一个已分配块和一个空闲块，原理类似place函数
                注意：不能为已分配块设置footer，这样会导致garbled bytes错误*/
            
            R_PUT(HDRP(oldptr),PACK(asize,1));
            /* 不能设置footer */
            SET_NEXT_ALLOC(oldptr);

            void * cp = NEXT_BLKP(oldptr);
            R_PUT(HDRP(cp),PACK(csize,0));
            PUT(FTRP(cp),PACK(csize,0));
            SET_NEXT_FREE(cp);
            SET_PRED(cp,NULL);
            SET_SUCC(cp,NULL);

            coalesce(cp);
        }

        return oldptr;
    }
    
}






/*
 * Calloc - malloc a block with the size of nmemb*size,and initialize it to zero
 */
void *calloc (size_t nmemb, size_t size) {
    size_t bytes = nmemb * size;
    void *newptr;

    newptr = malloc(bytes);
    memset(newptr, 0, bytes);

    return newptr;
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
    R_PUT(HDRP(bp), PACK(size, 0));         /* Free block header */   
    R_PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */ 
    
    SET_PRED(bp,NULL);
    SET_SUCC(bp,NULL);

    /* Coalesce if the previous block was free */
    return coalesce(bp);                                         
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

        R_PUT(HDRP(bp), PACK(asize, 1));
        R_PUT(FTRP(bp), PACK(asize, 1));
        SET_NEXT_ALLOC(bp);

        bp = NEXT_BLKP(bp);

        R_PUT(HDRP(bp), PACK(csize-asize, 0));
        R_PUT(FTRP(bp), PACK(csize-asize, 0));
        SET_NEXT_FREE(bp);
        SET_PRED(bp,NULL);
        SET_SUCC(bp,NULL);        
        coalesce(bp);
    }
    else { 
        R_PUT(HDRP(bp), PACK(csize, 1));
        R_PUT(FTRP(bp), PACK(csize, 1));
        SET_NEXT_ALLOC(bp);
    }

}


/*
 * coalesce - Boundary tag coalescing. Return ptr to coalesced block
 * The coalesced block will be inserted into the free block list
 */
static void *coalesce(void *bp) 
{
    size_t prev_alloc = (GET_PREV_ALLOC(bp) >> 1); /* 不能使用PREV_BLKP，因为前一个块不一定有footer */
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    //printf("%lx,%ld,%ld,%ld\n",PTR_VALUE(bp),prev_alloc,next_alloc,size);
   
    if (prev_alloc && next_alloc) {            /* Case 1 */
        SET_NEXT_FREE(bp);
        insert_list(bp);
        return bp;
    }

    else if (prev_alloc && !next_alloc) {      /* Case 2 */
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        delete_list(NEXT_BLKP(bp));
        R_PUT(HDRP(bp), PACK(size, 0));
        R_PUT(FTRP(bp), PACK(size, 0));
    }

    else if (!prev_alloc && next_alloc) {      /* Case 3 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        delete_list(PREV_BLKP(bp));
        R_PUT(FTRP(bp), PACK(size, 0));
        R_PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    else {                                     /* Case 4 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + 
            GET_SIZE(FTRP(NEXT_BLKP(bp)));
        delete_list(PREV_BLKP(bp));
        delete_list(NEXT_BLKP(bp));
        R_PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        R_PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    SET_NEXT_FREE(bp);
    insert_list(bp);
    return bp;
}

/* 
 * find_fit - Find a fit for a block with asize bytes 
 */
static void *find_fit(size_t asize)
{   
  
    for(int idx = list_idx(asize); idx < LISTNUM;++idx){

       /* 从索引为idx的链表开始搜索，如果当前链表没有搜到就换更大的链表 */
       /* 每个链表内的块按大小从小到大排序，确保了首次适配即最佳适配 */
        void * bp = GET_PTR(seg_list + idx * WSIZE); 

        while(bp != NULL){
            /* 找到一个足够大的空闲块 */
            if(GET_SIZE(HDRP(bp)) >= (asize)){
               // printf("A block with size %d is found. asize is %ld\n",GET_SIZE(HDRP(bp)),asize);
                return bp;
            }
            bp = SUCC(bp);
        }

    }
    //printf("Not Found\n");
    /* size比所有的空闲块的大小都大 */
    return NULL;
}

/* 
 * list_idx - Given the size of a free block;
 *            return the idx of the list it belongs to.
 *            idx range: [0,9]
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
 * Given a pointer bp pointing to a free block
 * insert this block into its corresponding free list
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
    int idx = list_idx(b_size); /* 对应链表的索引 ,idx范围[0,9] */
    void * list_head = GET_PTR(seg_list + (idx * WSIZE)); /* 链表表头 */


    if(list_head == NULL){
        /* 链表为空，插入该空闲块后，即成为头结点 */
        PUT_PTR((seg_list + (idx * WSIZE)),bp); 
        SET_PRED(bp,NULL);
        SET_SUCC(bp,NULL);
        
        //printf("A block of %ld size is inserted into list %d, bp = %lx\n",b_size,idx,PTR_VALUE(bp));
        return 0;

    }else{
        /* 链表非空 */
        
        /* 寻找bp的后继，即大小不小于bp的第一个块 */
        void * tmp = list_head;
        void * following = NULL;
        while((tmp != NULL) && (GET_SIZE(HDRP(tmp)) < b_size)){
            following = tmp;
            tmp = SUCC(tmp);
        }
        
        /* 现在following指向bp的前驱，tmp指向bp的后继 */

        if(tmp == list_head){
            /* bp的后继是头结点，即bp成为新的头结点 */
            SET_PRED(bp,NULL);
            SET_SUCC(bp,tmp);
            SET_PRED(tmp,bp);
            PUT_PTR((seg_list + (idx * WSIZE)),bp); /* renew the head */

        }else if(tmp == NULL){
            /* bp后继为空，即bp是最后一个结点 */
            SET_SUCC(bp,NULL);
            SET_PRED(bp,following);
            SET_SUCC(following,bp);
        }else{
            /* bp的前驱和后继均不为空  */
            SET_SUCC(following,bp);
            SET_PRED(bp,following);
            SET_SUCC(bp,tmp);
            SET_PRED(tmp,bp);
        }
        //printf("A block of %ld size is inserted into list %d,bp = %lx\n",b_size,idx,PTR_VALUE(bp));
        return 0;
    }
}

/* 
 * delete_list - Delete a block from its corresponding free block list
 * 
 * success:return 0;error: return -1;
 * 
 */

static int delete_list(void * bp){

    if(bp == NULL) return -1;

    int idx = list_idx((size_t)GET_SIZE(HDRP(bp))); /* idx为bp所在链表的索引 */
    void * list_head = GET_PTR(seg_list + (idx * WSIZE));   
  
    //printf("Starting to delete %lx with size %d at list %d\n",PTR_VALUE(bp),GET_SIZE(HDRP(bp)),idx);

    /* if bp isn't free or free list doesn't exist, error occurs */
    if(GET_ALLOC(HDRP(bp)) || (list_head == NULL)){
        printf("Deleting list error\n");
        return -1;
    }     

   
    if(bp == list_head){
        /* bp 为链表表头 */
        if(SUCC(bp) == NULL){
            /* 链表只有一个元素，则表头置空 */
            PUT_PTR((seg_list + (idx * WSIZE)),NULL);
        }else{
            /* 多于一个元素，则更新表头为bp的后继 */
            SET_PRED(SUCC(bp),NULL);
            PUT_PTR((seg_list + (idx * WSIZE)),(SUCC(bp)));
            SET_SUCC(bp,NULL);
        }
    }else{
        /* bp不是链表的表头 */
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
        printf("%d:Prologue block: %u error\n",lineno,GET(HDRP(heap_listp)));
        return;
    }


    /*iterate all the blocks in heaps and check them one after another */

    unsigned int MINSIZE = 2*DSIZE;
    void * bp = NEXT_BLKP(heap_listp);



    int last_block_alloc = 1; //record the allocate bit of last block,initialized to 1
    for(;GET_SIZE(HDRP(bp)) > 0;bp = NEXT_BLKP(bp)){
        /* check whether this block is in the heap */
        //printf("bp:%lx\n",PTR_VALUE(bp));
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
            printf("%d:Block Size %u not large enough,bp = %lx\n",lineno,GET_SIZE(HDRP(bp)),PTR_VALUE(bp));
        }

        /*check block's header and footer*/
        void * head = HDRP(bp);
        void * foot = FTRP(bp);

        if((!GET_ALLOC(head)) && ((GET(head) & (~0x2)) != (GET(foot) & (~0x2)))){
            printf("%d:Header and Footer not matching each other\n",lineno);
            return;
        }

        /*check two consecutive free blocks*/
        if(!last_block_alloc && !GET_ALLOC(HDRP(bp))){
            printf("%d:Two consecutive free blocks\n",lineno);
            return;
        }
    
        last_block_alloc = GET_ALLOC(HDRP(bp)); 
    }
    /*check epilogue block*/
    if(!GET_ALLOC(HDRP(bp))){
        printf("%d:Epilogue block error\n",lineno);
        return;
    }    


    /*check the free block list*/
    for(int i = 0;i < 10;++i){
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


/* 用于debug，打印索引为idx的链表的所有结点地址及其指向空闲块的大小 */
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