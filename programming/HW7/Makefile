all: compile test

compile:
	javac AbstractTest.java
	@cp AbstractTest.class ./markup
	javac markup/ListTest.java
	javac markup/TexListTest.java

test:
	java markup.TexListTest
