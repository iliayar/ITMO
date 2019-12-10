all: build run

build_base:
	cd src; javac base/*.java

clean_base:
	rm src/base/*.class

build:
	cd src; javac expression/*.java

clean:
	rm src/base/*.class

run:
	cd src; java expression.Main

run_test:
	cd src; java -ea expression.ExpressionTest hard
