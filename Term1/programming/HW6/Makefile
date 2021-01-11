all: compile test

compile:
	@javac ../HW5/Scanner.java
	@cp ../HW5/Scanner.class ./
	javac IntList.java
	javac WordStatLastIndex.java

run:
	java WordStatLastIndex

test:
	java -jar WordStatLastIndexTest.jar
