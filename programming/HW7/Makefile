all: build test
build: build_test build_self

build_test:
	javac AbstractTest.java
	@cp AbstractTest.class ./markup

build_self:
	javac markup/*.java

test:
	java markup.TexListTest

run:
	java markup.Test

compile_pdf:
	rm test.tex
	@echo "\documentclass{article}" >> test.tex
	@echo " \begin{document}" >> test.tex
	java markup.Test >> test.tex
	@echo "\end{document}" >> test.tex
	pandoc -o test.pdf test.tex
	zathura test.pdf
