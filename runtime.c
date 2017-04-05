#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>

#define STR_TRUE "#t"
#define STR_FALSE "#f"

typedef int64_t int64;

int64 read_int();
void write_void();
void write_int(int64 n);
void write_bool(int64 n);
void write_any(int64 n, int64 ty);

extern int r0func();

extern int ty_void;
extern int ty_integer;
extern int ty_boolean;

int main(int argc, char* argv[]) {
    write_int(r0func());
    return EXIT_SUCCESS;
}

int64 read_int() {
    int64 n;
    int result;
    result = scanf("%ld", &n);
    if (result == -1) {
        perror("scanf failed");
        exit(EXIT_FAILURE);
    }
    else if (result == 0) {
        fprintf(stderr, "error: expected integer\n");
        exit(EXIT_FAILURE);
    }
    return n;
}

void write_void() {
    if (printf("#<void>\n") == -1) {
        perror("write_void failed");
        exit(EXIT_FAILURE);
    }
}

void write_int(int64 n) {
    if (printf("%ld\n", n) == -1) {
        perror("write_int failed");
        exit(EXIT_FAILURE);
    }
}

void write_bool(int64 n) {
    if (printf("%s\n", (n ? STR_TRUE : STR_FALSE)) == -1) {
        perror("write_bool failed");
        exit(EXIT_FAILURE);
    }
}

void write_any(int64 n, int64 ty) {
    if (ty == ty_void) {
        write_void();
    }
    else if (ty == ty_integer) {
        write_int(n);
    }
    else if (ty == ty_boolean) {
        write_bool(n);
    }
    else {
        fprintf(stderr, "write_any failed with unknown type: %ld\n", ty);
        exit(EXIT_FAILURE);
    }
}