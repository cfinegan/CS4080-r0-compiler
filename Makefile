all:
	gcc -m64 --std=c89 -o bin/r0prog bin/r0func.s runtime.c 