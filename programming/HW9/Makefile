all: build_dep build run

build: build_dep build_self

build_self:
	javac md2html/Md2Html.java
	
build_dep:
	javac ../HW5/Scanner.java
	@cp ../HW5/Scanner.class ./
	make -C ../HW7 build_self
	@cp ../HW7/markup ./ -r

run:
	java md2html.Md2Html input.md output.html

test:
	java -jar Md2HtmlTest.jar
