#include <errno.h>
#include <pthread.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "myMalloc.h"
#include "printing.h"

/* Due to the way assert() prints error messges we use out own assert function
 * for deteminism when testing assertions
 */
#ifdef TEST_ASSERT
  inline static void assert(int e) {
    if (!e) {
      const char * msg = "Assertion Failed!\n";
      write(2, msg, strlen(msg));
      exit(1);
    }
  }
#else
  #include <assert.h>
#endif

/*
 * Mutex to ensure thread safety for the freelist
 */
static pthread_mutex_t mutex;

/*
 * Array of sentinel nodes for the freelists
 */
header freelistSentinels[N_LISTS];

/*
 * Pointer to the second fencepost in the most recently allocated chunk from
 * the OS. Used for coalescing chunks
 */
header * lastFencePost;

/*
 * Pointer to maintian the base of the heap to allow printing based on the
 * distance from the base of the heap
 */ 
void * base;

/*
 * List of chunks allocated by  the OS for printing boundary tags
 */
header * osChunkList [MAX_OS_CHUNKS];
size_t numOsChunks = 0;

/*
 * direct the compiler to run the init function before running main
 * this allows initialization of required globals
 */
static void init (void) __attribute__ ((constructor));

// Helper functions for manipulating pointers to headers
static inline header * get_header_from_offset(void * ptr, ptrdiff_t off);
static inline header * get_left_header(header * h);
static inline header * ptr_to_header(void * p);

// Helper functions for allocating more memory from the OS
static inline void initialize_fencepost(header * fp, size_t object_left_size);
static inline void insert_os_chunk(header * hdr);
static inline void insert_fenceposts(void * raw_mem, size_t size);
static header * allocate_chunk(size_t size);

// Helper functions for freeing a block
static inline void deallocate_object(void * p);

// Helper functions for allocating a block
static inline header * allocate_object(size_t raw_size);

// Helper functions for verifying that the data structures are structurally 
// valid
static inline header * detect_cycles();
static inline header * verify_pointers();
static inline bool verify_freelist();
static inline header * verify_chunk(header * chunk);
static inline bool verify_tags();

static void init();

static bool isMallocInitialized;

/**
 * @brief Helper function to retrieve a header pointer from a pointer and an 
 *        offset
 *
 * @param ptr base pointer
 * @param off number of bytes from base pointer where header is located
 *
 * @return a pointer to a header offset bytes from pointer
 */
static inline header * get_header_from_offset(void * ptr, ptrdiff_t off) {
	return (header *)((char *) ptr + off);
}

/**
 * @brief Helper function to get the header to the right of a given header
 *
 * @param h original header
 *
 * @return header to the right of h
 */
header * get_right_header(header * h) {
	return get_header_from_offset(h, get_object_size(h));
}

/**
 * @brief Helper function to get the header to the left of a given header
 *
 * @param h original header
 *
 * @return header to the right of h
 */
inline static header * get_left_header(header * h) {
  return get_header_from_offset(h, -h->object_left_size);
}

/**
 * @brief Fenceposts are marked as always allocated and may need to have
 * a left object size to ensure coalescing happens properly
 *
 * @param fp a pointer to the header being used as a fencepost
 * @param object_left_size the size of the object to the left of the fencepost
 */
inline static void initialize_fencepost(header * fp, size_t object_left_size) {
	set_object_state(fp,FENCEPOST);
	set_object_size(fp, ALLOC_HEADER_SIZE);
	fp->object_left_size = object_left_size;
}

/**
 * @brief Helper function to maintain list of chunks from the OS for debugging
 *
 * @param hdr the first fencepost in the chunk allocated by the OS
 */
inline static void insert_os_chunk(header * hdr) {
  if (numOsChunks < MAX_OS_CHUNKS) {
    osChunkList[numOsChunks++] = hdr;
  }
}

/**
 * @brief given a chunk of memory insert fenceposts at the left and 
 * right boundaries of the block to prevent coalescing outside of the
 * block
 *
 * @param raw_mem a void pointer to the memory chunk to initialize
 * @param size the size of the allocated chunk
 */
inline static void insert_fenceposts(void * raw_mem, size_t size) {
  // Convert to char * before performing operations
  char * mem = (char *) raw_mem;

  // Insert a fencepost at the left edge of the block
  header * leftFencePost = (header *) mem;
  initialize_fencepost(leftFencePost, ALLOC_HEADER_SIZE);

  // Insert a fencepost at the right edge of the block
  header * rightFencePost = get_header_from_offset(mem, size - ALLOC_HEADER_SIZE);
  initialize_fencepost(rightFencePost, size - 2 * ALLOC_HEADER_SIZE);
}

/**
 * @brief Allocate another chunk from the OS and prepare to insert it
 * into the free list
 *
 * @param size The size to allocate from the OS
 *
 * @return A pointer to the allocable block in the chunk (just after the 
 * first fencpost)
 */
static header * allocate_chunk(size_t size) {
  void * mem = sbrk(size);
  
  insert_fenceposts(mem, size);
  header * hdr = (header *) ((char *)mem + ALLOC_HEADER_SIZE);
  set_object_state(hdr, UNALLOCATED);
  set_object_size(hdr, size - 2 * ALLOC_HEADER_SIZE);
  hdr->object_left_size = ALLOC_HEADER_SIZE;
  return hdr;
}

//My Helper Functions

/**
 * @brief Helper round to nearest multiple of 8 given a request_size
 *
 * @param request_size to round up
 *
 * @return Next multiple of 8 or number itself if @param is a multiple of 8
 */
static inline size_t roundup8(size_t requested_size) { //Only works on positive numbers
  int remainder = abs(requested_size) % sizeof(size_t);
  if (remainder == 0) {
    return requested_size;
  }
  size_t result = (size_t) requested_size + sizeof(size_t) - remainder;
  return result;
}

/**
 * @brief Helper gets index of corresponding freelist
 *
 * @param raw_size to determine the appropriate index of
 *
 * @return Index value of freelist in freelistSentinels
 */
static inline size_t getIndex(size_t raw_size) {
  int index = (raw_size/sizeof(size_t)) - 1;
  if (index > N_LISTS - 1) {
    index = N_LISTS -1;
  }
  return index;
}

//end of My Helper Functions

/**
 * @brief Helper allocate an object given a raw request size from the user
 *
 * @param raw_size number of bytes the user needs
 *
 * @return A block satisfying the user's request
 */
static inline header * allocate_object(size_t raw_size) {
  if (raw_size == 0) {
    return NULL;
  }

  /* Step 1: Calculating required block size */
  size_t new_raw_size = roundup8(raw_size);
  if (new_raw_size < (sizeof(header) - ALLOC_HEADER_SIZE)) {
    new_raw_size =(sizeof(header) - ALLOC_HEADER_SIZE);
  }
  size_t req_size = new_raw_size + ALLOC_HEADER_SIZE;
  if (req_size < sizeof(header)) {
    req_size = sizeof(header);
  }

  /* Step 2: Finding free list*/

  for (int i = getIndex(new_raw_size); i < N_LISTS; i++) {
    header *freelist = &freelistSentinels[i];
    if (freelist->next != freelist) { //freelist is not empty
      if (i == N_LISTS - 1) {
        //blocks are allocated in first-fit order
        header *currBlock = freelist->next;
        while (currBlock != freelist) {
          if (get_object_size(currBlock) > req_size) { //satisfies request
            int diff2 = get_object_size(currBlock) - req_size;
            if (diff2 < sizeof(header)) {
              set_object_state(currBlock, ALLOCATED);
              currBlock->next->prev = currBlock->prev;
              currBlock->prev->next = currBlock->next;
              currBlock->next = NULL;
              currBlock->prev = NULL;
              return (header*) currBlock->data;
            }
            //updating metadata
            header *splitBlock = get_header_from_offset(currBlock, diff2);
            set_object_size(currBlock, diff2);
            set_block_object_size_and_state(splitBlock, req_size, ALLOCATED);
            splitBlock->object_left_size = get_object_size(currBlock);
            header *right = get_right_header(splitBlock);
            right->object_left_size = get_object_size(splitBlock);
            splitBlock->prev = NULL;
            splitBlock->next = NULL;
            //manage free list
            int index = 0;
            if (get_object_size(currBlock) < N_LISTS*8) {
              index = ((get_object_size(currBlock) - ALLOC_HEADER_SIZE)/8) - 1;
            } else {
              index = N_LISTS - 1;
            }
            if (index != N_LISTS - 1) {
              //removing currBlock from previous list
              currBlock->next->prev = currBlock->prev;
              currBlock->prev->next = currBlock->next;
              //adding currBlock to list
              header *addToList = &freelistSentinels[index];
              if (addToList->next == addToList) {
                currBlock->prev = addToList;
                currBlock->next = addToList;
                addToList->next = currBlock;
                addToList->prev = currBlock;
              } else {
                currBlock->next = addToList->next;
                currBlock->prev = addToList;
                addToList->next->prev = currBlock;
                addToList->next = currBlock;
              }
            }
            return (header*) splitBlock->data;
          } //endif current block satisfies request
          else if (get_object_size(currBlock) == req_size) {
            currBlock->next->prev = currBlock->prev;
            currBlock->prev->next = currBlock->next;
            currBlock->next = NULL;
            currBlock->prev = NULL;
            set_object_state(currBlock, ALLOCATED);
            return (header*) currBlock->data;
          }
          currBlock = currBlock->next;
        }//endwhile traversing freelist
      } //endif index == N_LISTS - 1
      else {//case in which free list is not N_LISTS - 1
        header *currBlock = freelist->next;
        if (get_object_size(currBlock) > req_size) {
          int diff2 = get_object_size(currBlock) - req_size;
          if (diff2 < sizeof(header)) {
              set_object_state(currBlock, ALLOCATED);
              currBlock->next->prev = currBlock->prev;
              currBlock->prev->next = currBlock->next;
              currBlock->next = NULL;
              currBlock->prev = NULL;
              return (header*) currBlock->data;
          }
          set_object_size(currBlock, diff2);
          int index = 0;
          if (get_object_size(currBlock) < N_LISTS*8) {
            index = ((get_object_size(currBlock) - ALLOC_HEADER_SIZE)/8) - 1;
          } else {
            index = N_LISTS - 1;
          }
          //add to appropriate block list
          header *addToList = &freelistSentinels[index];
          if (addToList->next == addToList) { //list is empty
            //removing currBlock from previous list
            currBlock->next->prev = currBlock->prev;
            currBlock->prev->next = currBlock->next;
            currBlock->next = NULL;
            currBlock->prev = NULL;
            //updating metadata
            header *splitBlock = get_header_from_offset(currBlock, diff2);
            set_block_object_size_and_state(splitBlock, req_size, ALLOCATED);
            splitBlock->object_left_size = get_object_size(currBlock);
            header *right = get_right_header(splitBlock);
            right->object_left_size = get_object_size(splitBlock);
            splitBlock->prev = NULL;
            splitBlock->next = NULL;
            //adding currBlock to list
            if (addToList->next == addToList) {
              currBlock->prev = addToList;
              currBlock->next = addToList;
              addToList->next = currBlock;
              addToList->prev = currBlock;
            } else {
              currBlock->next = addToList->next;
              currBlock->prev = addToList;
              addToList->next->prev = currBlock;
              addToList->next = currBlock;
            }
            return (header*) splitBlock->data;
          } else { //traverse the list
            //removing currBlock from previous list
            currBlock->next->prev = currBlock->prev;
            currBlock->prev->next = currBlock->next;
            currBlock->next = NULL;
            currBlock->prev = NULL;
            //updating metadata
            header *splitBlock = get_header_from_offset(currBlock, diff2);
            set_block_object_size_and_state(splitBlock, req_size, ALLOCATED);
            splitBlock->object_left_size = get_object_size(currBlock);
            header *right = get_right_header(splitBlock);
            right->object_left_size = get_object_size(splitBlock);
            splitBlock->prev = NULL;
            splitBlock->next = NULL;
            //adding currBlock to list
            if (addToList->next == addToList) {
              currBlock->prev = addToList;
              currBlock->next = addToList;
              addToList->next = currBlock;
              addToList->prev = currBlock;
            } else {
              currBlock->next = addToList->next;
              currBlock->prev = addToList;
              addToList->next->prev = currBlock;
              addToList->next = currBlock;
            }
            return (header*) splitBlock->data;
          }
        } else if (get_object_size(currBlock) == req_size) {
          //simple allocate
          //removing currBlock from previous list
          currBlock->next->prev = currBlock->prev;
          currBlock->prev->next = currBlock->next;
          currBlock->next = NULL;
          currBlock->prev = NULL;
          set_object_state(currBlock, ALLOCATED);
          return (header*) currBlock->data;
        }
      }//end else if i != N_LISTS - 1
    } //endif freelist is not empty
  }//end forloop

  //Request new chunk
  //if program doesn't return after for loop, no block could satisfy request
  header *newChunk = allocate_chunk(ARENA_SIZE);
  /* otherChunk stores the initial value of newChunk */
  header *otherChunk = newChunk;

  if (newChunk == NULL) {
    return NULL;
  }
  /* flag is updated to 1 if the chunks are contiguous */
  int flag = 0;
  header *leftFencePost = get_left_header(newChunk);
  /* newHeader is the header of the newly allocated chunk */
  header *newHeader = newChunk;
  if (get_left_header(leftFencePost) == lastFencePost) {
    newHeader = lastFencePost; //replacing prevRight and currLeft w header
    set_block_object_size_and_state(newHeader, 2*ALLOC_HEADER_SIZE + get_object_size(newChunk), UNALLOCATED);
    flag = 1;
  }
  else {
    insert_os_chunk(leftFencePost);
  }

  //if chunk needs to be coalesced with existing blocks
  //needs to be done regardless of the result of the prev if/else
  header *leftBlock = get_left_header(newHeader);
  if(get_object_state(leftBlock) == UNALLOCATED) {
    //colaesce left and current block
    size_t currIndex = getIndex(roundup8(get_object_size(leftBlock)));
    //update left header
    set_object_size(leftBlock, get_object_size(leftBlock) + get_object_size(newHeader));
    header *rightHeader = get_right_header(leftBlock);
    rightHeader->object_left_size = get_object_size(leftBlock);
    //update pointer
    newHeader = leftBlock;
    //if its isnt in n_lists - 1, remove the block and add to req. list
    if (currIndex != N_LISTS - 1) {
      size_t newIndex = getIndex(roundup8(get_object_size(newHeader)) - ALLOC_HEADER_SIZE);
      leftBlock->prev->next = leftBlock->next;
      leftBlock->next->prev = leftBlock->prev;
      header *list = &freelistSentinels[newIndex];
      if (list->next == list) {
        newHeader->prev = list;
        newHeader->next = list;
        list->next = newHeader;
        list->prev = newHeader;
      } else {
        newHeader->next = list->next;
        newHeader->prev = list;
        list->next->prev = newHeader;
        list->next = newHeader;
      }
    }
  } 
  else { //object to the left is allocated; size of the left block doesn't change
    if (flag == 1) {
      newChunk = get_header_from_offset(newChunk, -2*ALLOC_HEADER_SIZE);
    }
    header *list = &freelistSentinels[N_LISTS -1];
    if (list->next == list) {
      newChunk->prev = list;
      newChunk->next = list;
      list->next = newChunk;
      list->prev = newChunk;
    } else {
      newChunk->next = list->next;
      newChunk->prev = list;
      list->next->prev = newChunk;
      list->next = newChunk;
    }
  }

  if (flag == 1) {
    //update lastFencePost
    lastFencePost = get_right_header(otherChunk);
    //update left block size of last Fence Post
    lastFencePost->object_left_size = get_object_size(otherChunk);
  }

  //retry after allocating
  return allocate_object(raw_size);

} /* allocate_object() */


/**
 * @brief Helper to get the header from a pointer allocated with malloc
 *
 * @param p pointer to the data region of the block
 *
 * @return A pointer to the header of the block
 */
static inline header * ptr_to_header(void * p) {
  return (header *)((char *) p - ALLOC_HEADER_SIZE); //sizeof(header));
}

/**
 * @brief Helper to manage deallocation of a pointer returned by the user
 *
 * @param p The pointer returned to the user by a call to malloc
 */
static inline void deallocate_object(void * p) {
  if (p == NULL) {
    return;
  }

  header *currBlock = ptr_to_header(p);
  if (get_object_state(currBlock) == UNALLOCATED) { //Handling double frees
    const char * msg = "Double Free Detected\nAssertion Failed!\n";
    write(1, msg, strlen(msg));
    exit(1);
  }

  header *rightBlock = get_right_header(currBlock);
  header *leftBlock = get_left_header(currBlock);
  set_object_state(currBlock, UNALLOCATED);

  if (get_object_state(rightBlock) == UNALLOCATED 
      && get_object_state(leftBlock) == UNALLOCATED) {
    //coalesce both blocks
    /* currIndex stores the current index of the leftBlock */
    size_t currIndex = getIndex(roundup8(get_object_size(leftBlock)));
    //remove right block from list
    rightBlock->prev->next = rightBlock->next;
    rightBlock->next->prev = rightBlock->prev;
    //update left header size to current size + right block size
    set_object_size(leftBlock, get_object_size(leftBlock) + get_object_size(currBlock) + get_object_size(rightBlock));
    header *rightHeader = get_right_header(leftBlock);
    rightHeader->object_left_size = get_object_size(leftBlock);
    //update pointer
    currBlock = leftBlock;
    //remove coalesced block if its not it n_lists - 1, remove from current list, add it to the req. list
    if (currIndex != N_LISTS - 1) {
      size_t newIndex = getIndex(roundup8(get_object_size(currBlock)) - ALLOC_HEADER_SIZE);
      currBlock->prev->next = currBlock->next;
      currBlock->next->prev = currBlock->prev;
      header *list = &freelistSentinels[newIndex];
      if (list->next == list) {
        list->next = currBlock;
        currBlock->prev = list;
        currBlock->next = list;
        list->prev = currBlock;
      } else {
        header *temp = list->next;
        temp->prev = currBlock;
        currBlock->next = temp;
        currBlock->prev = list;
        list->next = currBlock;
      }
    }
  }
  else if(get_object_state(rightBlock) != UNALLOCATED
          && get_object_state(leftBlock) != UNALLOCATED) {
    size_t index = getIndex(roundup8(get_object_size(currBlock)) - ALLOC_HEADER_SIZE);
    header *list = &freelistSentinels[index];
    if (list->next == list) {
      list->next = currBlock;
      currBlock->prev = list;
      currBlock->next = list;
      list->prev = currBlock;
    } else {
      header *temp = list->next;
      temp->prev = currBlock;
      currBlock->next = temp;
      currBlock->prev = list;
      list->next = currBlock;
    }
  }
  else if(get_object_state(rightBlock) == UNALLOCATED) {
    //coleasce right and current block
    /* currIndex stores the current index of the rightBlock */
    size_t currIndex = getIndex(roundup8(get_object_size(rightBlock)));
    //update the right header size to current block + right block
    set_object_size(currBlock, get_object_size(rightBlock) + get_object_size(currBlock));
    header *rightHeader = get_right_header(currBlock);
    rightHeader->object_left_size = get_object_size(currBlock);
    //if the right block isnt in n_lists - 1, remove the block and add to req. list
    if (currIndex != N_LISTS - 1) {
      size_t newIndex = getIndex(roundup8(get_object_size(currBlock)) - ALLOC_HEADER_SIZE);
      rightBlock->prev->next = rightBlock->next;
      rightBlock->next->prev = rightBlock->prev;
      header *list = &freelistSentinels[newIndex];
      if (list->next == list) {
        currBlock->prev = list;
        currBlock->next = list;
        list->next = currBlock;
        list->prev = currBlock;
      } else {
        currBlock->next = list->next;
        currBlock->prev = list;
        list->next->prev = currBlock;
        list->next = currBlock;
      }
    }
  }
  else if(get_object_state(leftBlock) == UNALLOCATED) {
    //colaesce left and current block
    size_t currIndex = getIndex(roundup8(get_object_size(leftBlock)));
    //update left header
    set_object_size(leftBlock, get_object_size(leftBlock) + get_object_size(currBlock));
    header *rightHeader = get_right_header(leftBlock);
    rightHeader->object_left_size = get_object_size(leftBlock);
    //update pointer
    currBlock = leftBlock;
    //if its isnt in n_lists - 1, remove the block and add to req. list
    if (currIndex != N_LISTS - 1) {
      size_t newIndex = getIndex(roundup8(get_object_size(leftBlock)) - ALLOC_HEADER_SIZE);
      leftBlock->prev->next = leftBlock->next;
      leftBlock->next->prev = leftBlock->prev;
      header *list = &freelistSentinels[newIndex];
      if (list->next == list) {
        currBlock->prev = list;
        currBlock->next = list;
        list->next = currBlock;
        list->prev = currBlock;
      } else {
        currBlock->next = list->next;
        currBlock->prev = list;
        list->next->prev = currBlock;
        list->next = currBlock;
      }
    }
  }

  return;

} /* deallocate_object() */

/**
 * @brief Helper to detect cycles in the free list
 * https://en.wikipedia.org/wiki/Cycle_detection#Floyd's_Tortoise_and_Hare
 *
 * @return One of the nodes in the cycle or NULL if no cycle is present
 */
static inline header * detect_cycles() {
  for (int i = 0; i < N_LISTS; i++) {
    header * freelist = &freelistSentinels[i];
    for (header * slow = freelist->next, * fast = freelist->next->next; 
         fast != freelist; 
         slow = slow->next, fast = fast->next->next) {
      if (slow == fast) {
        return slow;
      }
    }
  }
  return NULL;
}

/**
 * @brief Helper to verify that there are no unlinked previous or next pointers
 *        in the free list
 *
 * @return A node whose previous and next pointers are incorrect or NULL if no
 *         such node exists
 */
static inline header * verify_pointers() {
  for (int i = 0; i < N_LISTS; i++) {
    header * freelist = &freelistSentinels[i];
    for (header * cur = freelist->next; cur != freelist; cur = cur->next) {
      if (cur->next->prev != cur || cur->prev->next != cur) {
        return cur;
      }
    }
  }
  return NULL;
}

/**
 * @brief Verify the structure of the free list is correct by checkin for 
 *        cycles and misdirected pointers
 *
 * @return true if the list is valid
 */
static inline bool verify_freelist() {
  header * cycle = detect_cycles();
  if (cycle != NULL) {
    fprintf(stderr, "Cycle Detected\n");
    print_sublist(print_object, cycle->next, cycle);
    return false;
  }

  header * invalid = verify_pointers();
  if (invalid != NULL) {
    fprintf(stderr, "Invalid pointers\n");
    print_object(invalid);
    return false;
  }

  return true;
}

/**
 * @brief Helper to verify that the sizes in a chunk from the OS are correct
 *        and that allocated node's canary values are correct
 *
 * @param chunk AREA_SIZE chunk allocated from the OS
 *
 * @return a pointer to an invalid header or NULL if all header's are valid
 */
static inline header * verify_chunk(header * chunk) {
	if (get_object_state(chunk) != FENCEPOST) {
		fprintf(stderr, "Invalid fencepost\n");
		print_object(chunk);
		return chunk;
	}
	
	for (; get_object_state(chunk) != FENCEPOST; chunk = get_right_header(chunk)) {
		if (get_object_size(chunk)  != get_right_header(chunk)->object_left_size) {
			fprintf(stderr, "Invalid sizes\n");
			print_object(chunk);
			return chunk;
		}
	}
	
	return NULL;
}

/**
 * @brief For each chunk allocated by the OS verify that the boundary tags
 *        are consistent
 *
 * @return true if the boundary tags are valid
 */
static inline bool verify_tags() {
  for (size_t i = 0; i < numOsChunks; i++) {
    header * invalid = verify_chunk(osChunkList[i]);
    if (invalid != NULL) {
      return invalid;
    }
  }

  return NULL;
}

/**
 * @brief Initialize mutex lock and prepare an initial chunk of memory for allocation
 */
static void init() {
  // Initialize mutex for thread safety
  pthread_mutex_init(&mutex, NULL);

#ifdef DEBUG
  // Manually set printf buffer so it won't call malloc when debugging the allocator
  setvbuf(stdout, NULL, _IONBF, 0);
#endif // DEBUG

  // Allocate the first chunk from the OS
  header * block = allocate_chunk(ARENA_SIZE);

  header * prevFencePost = get_header_from_offset(block, -ALLOC_HEADER_SIZE);
  insert_os_chunk(prevFencePost);

  lastFencePost = get_header_from_offset(block, get_object_size(block));

  // Set the base pointer to the beginning of the first fencepost in the first
  // chunk from the OS
  base = ((char *) block) - ALLOC_HEADER_SIZE; //sizeof(header);

  // Initialize freelist sentinels
  for (int i = 0; i < N_LISTS; i++) {
    header * freelist = &freelistSentinels[i];
    freelist->next = freelist;
    freelist->prev = freelist;
  }

  // Insert first chunk into the free list
  header * freelist = &freelistSentinels[N_LISTS - 1];
  freelist->next = block;
  freelist->prev = block;
  block->next = freelist;
  block->prev = freelist;
}

/* 
 * External interface
 */
void * my_malloc(size_t size) {
  pthread_mutex_lock(&mutex);
  header * hdr = allocate_object(size); 
  pthread_mutex_unlock(&mutex);
  return hdr;
}

void * my_calloc(size_t nmemb, size_t size) {
  return memset(my_malloc(size * nmemb), 0, size * nmemb);
}

void * my_realloc(void * ptr, size_t size) {
  void * mem = my_malloc(size);
  memcpy(mem, ptr, size);
  my_free(ptr);
  return mem; 
}

void my_free(void * p) {
  pthread_mutex_lock(&mutex);
  deallocate_object(p);
  pthread_mutex_unlock(&mutex);
}

bool verify() {
  return verify_freelist() && verify_tags();
}
