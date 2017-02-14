all:
	gcc -m64 --std=c89 -o bin/r0prog.exe bin/r0func.s runtime.c 