all:
	gcc -Wall -pedantic -Wno-pointer-arith -m64 --std=gnu99 -o bin/r0prog bin/r0func.s runtime.c 
