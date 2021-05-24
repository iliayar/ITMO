.PHONY: all run pack clean collect

lab_SRCS:=$(wildcard *.hs)

all: Main

run: Main
	@./Main

Main: $(lab_SRCS)
	ghc Main.hs -o Main -dynamic

pack: collect
	@zip B.zip B/*
	@rm -R B

collect: *.hs Makefile
	@mkdir B
	cp $? B/
	@cp Makefile B/


clean: *.hi *.o
	rm $?
