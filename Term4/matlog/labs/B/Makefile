.PHONY: all run pack clean collect

tasknum=B

all: Main

run:
	./Main

test:
	echo ${SOURCES}

Main: Main.hs
	ghc Main.hs -O5 -o Main

pack: collect
	zip $(tasknum).zip $(tasknum)/*
	rm -R $(tasknum)

collect: *.hs Makefile
	mkdir $(tasknum)
	cp $? $(tasknum)/
	cp Makefile $(tasknum)/


clean: *.hi *.o
	rm $?
