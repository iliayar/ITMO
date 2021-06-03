.PHONY: all run pack clean collect

tasknum=C

all: Main

run:
	./Main

test:
	echo ${SOURCES}

Main: Main.hs
	ghc Main.hs -O5 -o Main

gen_parser: Tokens.hs Grammar.hs

Tokens.hs: Tokens.x
	alex Tokens.x
Grammar.hs: Grammar.y
	happy Grammar.y

pack: collect
	zip $(tasknum).zip $(tasknum)/*
	rm -R $(tasknum)

collect: *.hs Makefile gen_parser
	mkdir $(tasknum)
	cp $? $(tasknum)/
	cp Makefile $(tasknum)/


clean: *.hi *.o Grammar.hs Tokens.hs
	rm $?
