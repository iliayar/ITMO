.PHONY: all run pack clean parser

tasknum=B

all: Main

run:
	./Main

Main: parser Main.hs
	ghc Main.hs

parser: Tokens.hs Grammar.hs

Tokens.hs: Tokens.x
	alex Tokens.x
Grammar.hs: Grammar.y
	happy Grammar.y

pack: parser
	zip $(tasknum).zip *.hs Tokens.x Grammar.y Makefile

clean:
	rm *.hi *.o Grammar.hs Tokens.hs
