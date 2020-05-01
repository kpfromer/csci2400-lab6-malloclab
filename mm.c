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

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "PT",
    /* First member's full name */
    "Saurabh Totey",
    /* First member's email address */
    "saurabh.totey@colorado.edu",
    /* Second member's full name (leave blank if none) */
    "Kyle Pfromer",
    /* Second member's email address (leave blank if none) */
    "kyle.pfromer@colorado.edu"};

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
void mm_checkheap(int);

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

static inline void SET_BLOCK_DATA(void *bp, uint32_t size, int alloc)
{
  uint32_t boundaryData = PACK(size, alloc);
  PUT(HEADER(bp), boundaryData);
  PUT(FOOTER(bp), boundaryData);
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

static char *next_fit_pointer;

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
  // Create the initial empty heap
  if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
    return -1;
  PUT(heap_listp, 0);                          // alignment padding
  PUT(heap_listp + WSIZE, PACK(OVERHEAD, 1));  // prologue header
  PUT(heap_listp + DSIZE, PACK(OVERHEAD, 1));  // prologue footer
  PUT(heap_listp + WSIZE + DSIZE, PACK(0, 1)); // epilogue header
  heap_listp += DSIZE;

  next_fit_pointer = heap_listp;

  // Extend the empty heap with a free block of CHUNKSIZE bytes
  if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
    return -1;
  return 0;
}

//
// extend_heap - Extend heap with free block and return its block pointer
//
static void *extend_heap(uint32_t words)
{
  char *bp;
  size_t size;

  // Allocate an even number of words to maintain alignment
  size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
  if ((long)(bp = mem_sbrk(size)) == -1)
    return NULL;

  // Initialize free block header/footer and the epilogue header
  SET_BLOCK_DATA(bp, size, 0);
  PUT(HEADER(NEXT_BLOCK(bp)), PACK(0, 1)); // new epilogue header

  // coalesce if the previous block was free
  return coalesce(bp);
}

//
// Practice problem 9.8
//
// find_fit - Find a fit for a block with asize bytes
//
static void *find_fit(uint32_t asize)
{
  // next fit
  void *bp = next_fit_pointer;
  do
  {
    if (!GET_ALLOC(HEADER(bp)) && (asize <= GET_SIZE(HEADER(bp))))
    {
      next_fit_pointer = bp;
      return bp;
    }
    bp = NEXT_BLOCK(bp);
    if (GET_SIZE(HEADER(bp)) <= 0)
    {
      bp = heap_listp;
    }
  } while (bp != next_fit_pointer);
  return NULL; // no fit
}

//
// mm_free - Free a block
//
void mm_free(void *bp)
{
  size_t size = GET_SIZE(HEADER(bp));

  SET_BLOCK_DATA(bp, size, 0);
  coalesce(bp);
}

//
// coalesce - boundary tag coalescing. Return ptr to coalesced block
//
static void *coalesce(void *bp)
{
  size_t previousAllocation = GET_ALLOC(FOOTER(PREVIOUS_BLOCK(bp)));
  size_t nextAllocation = GET_ALLOC(HEADER(NEXT_BLOCK(bp)));
  size_t size = GET_SIZE(HEADER(bp));

  if (previousAllocation && nextAllocation)
  {
    return bp;
  }
  else if (previousAllocation && !nextAllocation)
  {
    size += GET_SIZE(HEADER(NEXT_BLOCK(bp)));
    SET_BLOCK_DATA(bp, size, 0);
  }
  else if (!previousAllocation && nextAllocation)
  {
    bp = PREVIOUS_BLOCK(bp);
    size += GET_SIZE(HEADER(bp));
    SET_BLOCK_DATA(bp, size, 0);
  }
  else
  {
    size += GET_SIZE(HEADER(NEXT_BLOCK(bp)));
    bp = PREVIOUS_BLOCK(bp);
    size += GET_SIZE(HEADER(bp));
    SET_BLOCK_DATA(bp, size, 0);
  }
  // if next fit is pointing to middle of coalesced block change to point to
  // new block
  if (HEADER(bp) < next_fit_pointer && next_fit_pointer < FOOTER(bp))
    next_fit_pointer = bp;
  return bp;
}

//
// mm_malloc - Allocate a block with at least size bytes of payload
//
void *mm_malloc(uint32_t size)
{
  size_t asize;      /* adjusted block size */
  size_t extendsize; /* amount to extend heap if no fit */
  char *bp;

  /* Ignore spurious requests */
  if (size <= 0)
    return NULL;

  /* Adjust block size to include overhead and alignment reqs. */
  if (size <= DSIZE)
    asize = DSIZE + OVERHEAD;
  else
    asize = DSIZE * ((size + (OVERHEAD) + (DSIZE - 1)) / DSIZE);

  /* Search the free list for a fit */
  if ((bp = find_fit(asize)) != NULL)
  {
    place(bp, asize);
    return bp;
  }

  /* No fit found. Get more memory and place the block */
  extendsize = MAX(asize, CHUNKSIZE);
  if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
    return NULL;
  place(bp, asize);
  return bp;
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
  size_t csize = GET_SIZE(HEADER(bp));
  // minium block size is 16 bytes (DSIZE + OVERHEAD;)
  if ((csize - asize) >= (DSIZE + OVERHEAD))
  {
    SET_BLOCK_DATA(bp, asize, 1);
    bp = NEXT_BLOCK(bp);
    SET_BLOCK_DATA(bp, csize - asize, 0);
    coalesce(bp);
  }
  else
  {
    SET_BLOCK_DATA(bp, csize, 1);
  }
}

//
// mm_realloc -- implemented for you
//
void *mm_realloc(void *ptr, uint32_t size)
{
  void *newp;
  uint32_t copySize;

  copySize = GET_SIZE(HEADER(ptr));
  if (size == copySize)
  {
    return ptr;
  }

  uint32_t asize;
  if (size <= DSIZE)
    asize = DSIZE + OVERHEAD;
  else
    asize = DSIZE * ((size + (OVERHEAD) + (DSIZE - 1)) / DSIZE);

  if (asize < copySize)
  {
    SET_BLOCK_DATA(ptr, asize, 1);
    SET_BLOCK_DATA(NEXT_BLOCK(ptr), copySize - asize, 0);
    coalesce(NEXT_BLOCK(ptr));
    return ptr;
  }
  else if (size < copySize)
  {
    copySize = size;
  }
  else if (GET_ALLOC(HEADER(NEXT_BLOCK(ptr))) == 0 && GET_SIZE(HEADER(NEXT_BLOCK(ptr))) + copySize >= asize)
  {
    place(ptr, asize);
    return ptr;
  }

  newp = mm_malloc(size);
  if (newp == NULL)
  {
    printf("ERROR: mm_malloc failed in mm_realloc\n");
    exit(1);
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
