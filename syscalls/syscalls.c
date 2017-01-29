#include <stdio.h>

int __cdecl read() {
	int n, result;
	do {
		result = scanf("%d", &n);
	} while (result < 1);
	return n;
}

void __cdecl write(int n) {
	printf("%d\n", n);
}