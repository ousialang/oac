CFLAGS = -Wall -g # -Os

.SUFFIXES :

all :
	time ./eval boot.scm emit.scm eval.scm > eval.s
	gcc -m32 -c -o eval.o eval.s && size eval.o && gcc -m32 -o eval1 eval.o && rm -f eval && mv eval1 eval
	make clean

clean :
	rm -f *~ *.o *.s *.o
	rm -rf *.dSYM
