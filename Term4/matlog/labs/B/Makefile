.PHONY: all run pack clean

tasknum=B

all: Main

run:
	@./Main

Main: Main.hs
	ghc Main.hs -O5 -o Main

pack: 
	zip $(tasknum).zip *.hs Makefile

clean:
	rm *.hi *.o
