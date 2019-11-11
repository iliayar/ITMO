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
