all: build run
span: build_span run_span

build:
	javac src/search/BinarySearch.java

run:
	cd src/ && \
	java search.BinarySearch ${ARGS}

test:
	cd src/ && \
	java -jar BinarySearchTest.jar

build_span:
	javac src/search/BinarySearchSpan.java

run_span:
	cd src/ && \
	java search.BinarySearchSpan ${ARGS}

test_span:
	cd src/ && \
	java -jar BinarySearchSpanTest.jar
