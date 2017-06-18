// C Standard Includes
#include <errno.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
// Linux API Includes
#include <sys/mman.h>
#include <unistd.h>

void gc_init(uint64_t rootstack_size, uint64_t heap_size);
void gc_collect(int64_t **roostack_ptr, uint64_t bytes_requested);
int64_t read_int();
void write_void();
void write_int(int64_t n);
void write_bool(int64_t n);
void write_vector(int64_t *vec);
void write_any(int64_t n, int64_t ty);

extern int r0func();

extern int64_t ty_void;
extern int64_t ty_integer;
extern int64_t ty_boolean;
extern int64_t ty_vector;

int64_t *free_ptr = NULL;
int64_t *fromspace_begin = NULL;
int64_t *fromspace_end = NULL;
int64_t *tospace_begin = NULL;
int64_t *tospace_end = NULL;
int64_t **rootstack_begin = NULL;

long PG_SIZE;

int main(int argc, char *argv[]) {
  PG_SIZE = sysconf(_SC_PAGE_SIZE);

  uint64_t arg_heap_size = (uint64_t)PG_SIZE;
  uint64_t arg_rootstack_size = (uint64_t)PG_SIZE;

  if (argc > 1 && sscanf(argv[1], "%lu", &arg_rootstack_size) < 1) {
    fprintf(stderr, "couldn't read rootstack size: %s\n", argv[1]);
  }

  if (argc > 2 && sscanf(argv[2], "%lu", &arg_heap_size) < 1) {
    fprintf(stderr, "couldn't read heap size: %s\n", argv[2]);
  }

  gc_init(arg_rootstack_size, arg_heap_size);

  r0func();
  return EXIT_SUCCESS;
}

void gc_init(uint64_t rootstack_size, uint64_t heap_size) {
  // adjust rootstack size to multiple of page size
  uint64_t stack_misalign = rootstack_size % PG_SIZE;
  if (stack_misalign != 0 || rootstack_size == 0) {
    uint64_t stack_pages = (rootstack_size / PG_SIZE) + 1;
    rootstack_size = stack_pages * PG_SIZE;
  }

  // allocate rootstack
  void *tmp_rootstack =
      mmap(NULL, rootstack_size + (PG_SIZE * 2), PROT_READ | PROT_WRITE,
           MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  if (tmp_rootstack == (void *)-1) {
    perror("failed to allocate rootstack");
    exit(EXIT_FAILURE);
  }
  if (mprotect(tmp_rootstack, PG_SIZE, PROT_NONE) ||
      mprotect(tmp_rootstack + PG_SIZE + rootstack_size, PG_SIZE, PROT_NONE)) {
    perror("mprotect failed for rootstack in gc_init");
    exit(EXIT_FAILURE);
  }
  rootstack_begin = tmp_rootstack + PG_SIZE;
  memset(rootstack_begin, 0, rootstack_size);

  // adjust heap size to multiple of page size
  uint64_t heap_misalign = heap_size % PG_SIZE;
  if (heap_misalign != 0 || heap_size == 0) {
    uint64_t heap_pages = (heap_size / PG_SIZE) + 1;
    heap_size = heap_pages * PG_SIZE;
  }

  // allocate heap
  void *heap_begin =
      mmap(NULL, (heap_size * 2) + (PG_SIZE * 3), PROT_READ | PROT_WRITE,
           MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  if (heap_begin == (void *)-1) {
    perror("failed to allocate heap");
    exit(EXIT_FAILURE);
  }
  if (mprotect(heap_begin, PG_SIZE, PROT_NONE) ||
      mprotect(heap_begin + PG_SIZE + heap_size, PG_SIZE + heap_size + PG_SIZE,
               PROT_NONE)) {
    perror("mprotect failed for heap in gc_init");
    exit(EXIT_FAILURE);
  }
  fromspace_begin = heap_begin + PG_SIZE;
  free_ptr = fromspace_begin;
  fromspace_end = fromspace_begin + heap_size;
  tospace_begin = fromspace_end + PG_SIZE;
  tospace_end = tospace_begin + heap_size;
  memset(fromspace_begin, 0, heap_size);

  /*rootstack_begin = malloc(rootstack_size);
    if (rootstack_begin == NULL) {
        perror("failed to allocate rootstack");
        exit(EXIT_FAILURE);
    }
    memset(rootstack_begin, 0, rootstack_size);

    fromspace_begin = malloc(heap_size * 2);
    if (fromspace_begin == NULL) {
        perror("failed to allocate r0 heap");
        exit(EXIT_FAILURE);
    }
    free_ptr = fromspace_begin;
    fromspace_end = fromspace_begin + heap_size;
    tospace_begin = fromspace_end;
    tospace_end = tospace_begin + heap_size;
    memset(fromspace_begin, 0, heap_size * 2);*/
}

void gc_collect(int64_t **rootstack_ptr, uint64_t bytes_requested) {
  fprintf(stderr, "Garbage collection not implemented yet!\n");
}

int64_t read_int() {
  int64_t n;
  switch (scanf("%ld", &n)) {
    case 0:
      fprintf(stderr, "read_int failed: expected integer\n");
      break;
    case EOF:
      fprintf(stderr, "read_int failed: %s\n",
              (ferror(stdin) ? strerror(errno) : "EOF"));
      break;
    default:
      return n;
  }
  exit(EXIT_FAILURE);
}

// no-op for now?
void write_void() {
//  if (printf("#<void>\n") < 0) {
//    perror("write_void failed");
//    exit(EXIT_FAILURE);
// }
}

void write_int(int64_t n) {
  if (printf("%ld\n", n) < 0) {
    perror("write_int failed");
    exit(EXIT_FAILURE);
  }
}

void write_bool(int64_t n) {
  if (printf("%s\n", (n ? "#t" : "#f")) < 0) {
    perror("write_bool failed");
    exit(EXIT_FAILURE);
  }
}

void write_vector(int64_t *vec) {}

void write_any(int64_t n, int64_t ty) {
  if (ty == ty_void) {
    write_void();
  } else if (ty == ty_integer) {
    write_int(n);
  } else if (ty == ty_boolean) {
    write_bool(n);
  } else {
    fprintf(stderr, "write_any failed with unknown type: %ld\n", ty);
    exit(EXIT_FAILURE);
  }
}
