all: build run
parser: build_parser run_parser

build_base:
	javac base/*.java

clean_base:
	rm base/*.class

build:
	javac expression/*.java

clean:
	rm base/*.class

run:
	java expression.Main

run_test:
	java -ea expression.ExpressionTest hard

build_parser:
	javac expression/parser/*.java
	
run_parser:
	java expression.parser.Main
run_parser_test:
	java -ea expression.parser.ParserTest
