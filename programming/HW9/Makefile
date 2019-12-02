all: build_dep build run

build: build_dep build_self

build_self:
	javac md2html/*.java
	
build_dep:
	javac ../HW5/Scanner.java
	@cp ../HW5/Scanner.class ./

run:
	java md2html.Md2Html input.md output.html

test:
	java -jar Md2HtmlTest.jar

clean:
	rm -Rf md2html/*.class
