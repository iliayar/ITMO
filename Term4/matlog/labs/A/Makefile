.PHONY: all run pack clean parser

tasknum=A

all: Main

run: Main
	@./Main

Main: parser Main.hs
	ghc Main.hs -O5 -o Main

parser: Tokens.hs Grammar.hs

Tokens.hs: Tokens.x
	alex Tokens.x
Grammar.hs: Grammar.y
	happy Grammar.y

pack: parser
	zip $(tasknum).zip *.hs Tokens.x Grammar.y Makefile

clean:
	rm *.hi *.o Grammar.hs Tokens.hs
