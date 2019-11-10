all: build test

build:
	javac AbstractTest.java
	@cp AbstractTest.class ./markup
	javac markup/*.java

test:
	java markup.TexListTest

run:
	java markup.Test