all: build_dep build run

build: build_dep build_self

build_self:
	javac Md2Html.java
	
build_dep:
	javac ../HW5/Scanner.java
	@cp ../HW5/Scanner.class ./
	make -C ../HW7 build_self
	@cp ../HW7/markup ./ -r

run:
	java Md2Html input.txt output.txt
