#include <stdlib.h>
#include <stdio.h>

int read_int() {
    int result, n;
    result = scanf("%d", &n);
    if (result == -1) {
        perror("read_int failed");
        exit(EXIT_FAILURE);
    } else if (result == 0) {
        fprintf(stderr, "invalid value passed to read_int\n");
        exit(EXIT_FAILURE);
    }
    return n;
}

void write_int(int n) {
    if (printf("%d\n", n) == -1) {
        perror("write_int failed");
        exit(EXIT_FAILURE);
    }
}

extern int r0func();

int main(int argc, char* argv[]) {
    return r0func();
}