#include <stdlib.h>
#include <stdio.h>

int read_int() {
    int n;
    if (scanf("%d", &n) == -1) {
        perror("read_int failed");
        exit(EXIT_FAILURE);
    }
}

void write_int(int n) {
    if (printf("%d\n", n) == -1) {
        perror("write_int failed");
        exit(EXIT_FAILURE);
    }
}

extern int r0func();

int main(int argc, char* argv[]) {
    write_int(r0func());
    return EXIT_SUCCESS;
}