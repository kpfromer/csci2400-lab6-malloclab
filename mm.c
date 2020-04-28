/* 
 * mm-implicit.c -  Simple allocator based on implicit free lists, 
 *                  first fit placement, and boundary tag coalescing. 
 *
 * Each block has header and footer of the form:
 * 
 *      31                     3  2  1  0 
 *      -----------------------------------
 *     | s  s  s  s  ... s  s  s  0  0  a/f
 *      ----------------------------------- 
 * 
 * where s are the meaningful size bits and a/f is set 
 * iff the block is allocated. The list has the following form:
 *
 * begin                                                          end
 * heap                                                           heap  
 *  -----------------------------------------------------------------   
 * |  pad   | hdr(8:a) | ftr(8:a) | zero or more usr blks | hdr(8:a) |
 *  -----------------------------------------------------------------
 *          |       prologue      |                       | epilogue |
 *          |         block       |                       | block    |
 *
 * The allocated prologue and epilogue blocks are overhead that
 * eliminate edge conditions during coalescing.
 */
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <memory.h>
#include "mm.h"
#include "memlib.h"

// dyanmic memory - 13:33

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "PT",
    /* First member's full name */
    "Kyle Pfromer",
    /* First member's email address */
    "kyle.pfromer@colorado.edu",
    /* Second member's full name (leave blank if none) */
    "Saurabh Totey",
    /* Second member's email address (leave blank if none) */
    "saurabh.totey@colorado.edu"};

/////////////////////////////////////////////////////////////////////////////
// Constants and macros
//
// These correspond to the material in Figure 9.43 of the text
// The macros have been turned into C++ inline functions to
// make debugging code easier.
//
/////////////////////////////////////////////////////////////////////////////
#define WSIZE 4             /* word size (bytes) */
#define DSIZE 8             /* doubleword size (bytes) */
#define CHUNKSIZE (1 << 12) /* initial heap size (bytes) */
#define OVERHEAD 8          /* overhead of header and footer (bytes) */

static inline int MAX(int x, int y)
{
  return x > y ? x : y;
}

//
// Pack a size and allocated bit into a word
// We mask of the "alloc" field to insure only
// the lower bit is used
//
static inline uint32_t PACK(uint32_t size, int alloc)
{
  return ((size) | (alloc & 0x1));
}

//
// Read and write a word at address p
//
static inline uint32_t GET(void *p) { return *(uint32_t *)p; }
static inline void PUT(void *p, uint32_t val)
{
  *((uint32_t *)p) = val;
}

//
// Read the size and allocated fields from address p
//
static inline uint32_t GET_SIZE(void *p)
{
  return GET(p) & ~0x7;
}

static inline int GET_ALLOC(void *p)
{
  return GET(p) & 0x1;
}

//
// Given block ptr bp, compute address of its header and footer
//
static inline void *HEADER(void *bp)
{

  return ((char *)bp) - WSIZE;
}
static inline void *FOOTER(void *bp)
{
  return ((char *)(bp) + GET_SIZE(HEADER(bp)) - DSIZE);
}

//
// Given block ptr bp, compute address of next and previous blocks
//
static inline void *NEXT_BLOCK(void *bp)
{
  return ((char *)(bp) + GET_SIZE(((char *)(bp)-WSIZE)));
}

static inline void *PREVIOUS_BLOCK(void *bp)
{
  return ((char *)(bp)-GET_SIZE(((char *)(bp)-DSIZE)));
}

/////////////////////////////////////////////////////////////////////////////
//
// Global Variables
//

static char *heap_listp; /* pointer to first block */

//
// function prototypes for internal helper routines
//
static void *extend_heap(uint32_t words);
static void place(void *bp, uint32_t asize);
static void *find_fit(uint32_t asize);
static void *coalesce(void *bp);
static void printblock(void *bp);
static void checkblock(void *bp);

//
// mm_init - Initialize the memory manager
//
int mm_init(void)
{
  //
  // You need to provide this
  //
  mem_init();
  return 0;
}

//
// extend_heap - Extend heap with free block and return its block pointer
//
static void *extend_heap(uint32_t words)
{
  mem_sbrk((int)words);
  return NULL;
}

//
// Practice problem 9.8
//
// find_fit - Find a fit for a block with asize bytes
//
static void *find_fit(uint32_t asize)
{
  // dynamic memory - implicit allocator - 7:15
  void *p = mem_heap_lo();
  // first fit
  while ((p < mem_heap_hi()) && (GET_ALLOC(p) || GET_SIZE(p) < asize))
  {
    p = NEXT_BLOCK(p);
  }
  if (NEXT_BLOCK(p) > mem_heap_hi())
    return NULL;
  return p;
}

//
// mm_free - Free a block
//
void mm_free(void *bp)
{
  // get back to header from payload pointer
  bp = HEADER(bp);
  // dynamic memory 9:24
  // set to not allocated
  *(int *)bp = *(int *)bp & -2;
  // TODO: check if allocated (if not error)
  coalesce(bp);
}

//
// coalesce - boundary tag coalescing. Return ptr to coalesced block
//
static void *coalesce(void *bp)
{
  char *start = bp; //Assumes bp is a header pointer, not a payload pointer
  uint32_t size = GET_SIZE(bp);
  void *previous = PREVIOUS_BLOCK(bp);
  if (previous >= mem_heap_lo() && GET_ALLOC(previous) == 0)
  {
    start = ((char *)previous) + WSIZE;
    size += GET_SIZE(previous);
  }

  void *next = NEXT_BLOCK(bp);
  if (next + GET_SIZE(next) <= mem_heap_hi() && GET_ALLOC(next) == 0)
  {
    size += GET_SIZE(next);
  }

  uint32_t boundary = PACK(size, 0);
  // update header boundary
  PUT(start, boundary);
  // update footer boundary
  PUT(FOOTER(start + WSIZE), boundary);

  return bp;
}

//
// mm_malloc - Allocate a block with at least size bytes of payload
//
void *mm_malloc(uint32_t size)
{
  // find the fit
  void *p = find_fit(size);
  if (p == NULL)
  {
    return NULL;
  }
  int pSize = GET_SIZE(p);
  PUT(p, PACK(size, 1));
  //footer
  // TODO: Issue with adding to pointer?
  PUT(p + size, PACK(size, 1));
  // edge case for size is perfect match
  if (size == pSize)
  {
    return p;
  }
  // create block after if size is not padded
  void *empty = NEXT_BLOCK(p);
  // header for empty space
  PUT(empty, PACK(pSize - size, 0));
  // footer for empty space
  PUT(p + pSize, PACK(pSize - size, 0));
  // TODO: alignment?
  return p;
}

//
//
// Practice problem 9.9
//
// place - Place block of asize bytes at start of free block bp
//         and split if remainder would be at least minimum block size
//
static void place(void *bp, uint32_t asize)
{
}

//
// mm_realloc -- implemented for you
//
void *mm_realloc(void *ptr, uint32_t size)
{
  void *newp;
  uint32_t copySize;

  newp = mm_malloc(size);
  if (newp == NULL)
  {
    printf("ERROR: mm_malloc failed in mm_realloc\n");
    exit(1);
  }
  copySize = GET_SIZE(HEADER(ptr));
  if (size < copySize)
  {
    copySize = size;
  }
  memcpy(newp, ptr, copySize);
  mm_free(ptr);
  return newp;
}

//
// mm_checkheap - Check the heap for consistency
//
void mm_checkheap(int verbose)
{
  //
  // This provided implementation assumes you're using the structure
  // of the sample solution in the text. If not, omit this code
  // and provide your own mm_checkheap
  //
  void *bp = heap_listp;

  if (verbose)
  {
    printf("Heap (%p):\n", heap_listp);
  }

  if ((GET_SIZE(HEADER(heap_listp)) != DSIZE) || !GET_ALLOC(HEADER(heap_listp)))
  {
    printf("Bad prologue header\n");
  }
  checkblock(heap_listp);

  for (bp = heap_listp; GET_SIZE(HEADER(bp)) > 0; bp = NEXT_BLOCK(bp))
  {
    if (verbose)
    {
      printblock(bp);
    }
    checkblock(bp);
  }

  if (verbose)
  {
    printblock(bp);
  }

  if ((GET_SIZE(HEADER(bp)) != 0) || !(GET_ALLOC(HEADER(bp))))
  {
    printf("Bad epilogue header\n");
  }
}

static void printblock(void *bp)
{
  uint32_t hsize, halloc, fsize, falloc;

  hsize = GET_SIZE(HEADER(bp));
  halloc = GET_ALLOC(HEADER(bp));
  fsize = GET_SIZE(FOOTER(bp));
  falloc = GET_ALLOC(FOOTER(bp));

  if (hsize == 0)
  {
    printf("%p: EOL\n", bp);
    return;
  }

  printf("%p: header: [%d:%c] footer: [%d:%c]\n",
         bp,
         (int)hsize, (halloc ? 'a' : 'f'),
         (int)fsize, (falloc ? 'a' : 'f'));
}

static void checkblock(void *bp)
{
  if ((uintptr_t)bp % 8)
  {
    printf("Error: %p is not doubleword aligned\n", bp);
  }
  if (GET(HEADER(bp)) != GET(FOOTER(bp)))
  {
    printf("Error: header does not match footer\n");
  }
}
