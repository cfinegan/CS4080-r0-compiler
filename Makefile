all:
	gcc -Wall -pedantic -m64 --std=c99 -o bin/r0prog bin/r0func.s runtime.c 