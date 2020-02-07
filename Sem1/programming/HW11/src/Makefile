all: build run
parser: build_parser run_parser run_parser_test
exceptions: build_exceptions run_exceptions run_exceptions_test

build_base:
	javac base/*.java

clean_base:
	rm base/*.class

build:
	javac expression/*.java

clean:
	rm base/*.class

run:
	java expression.Main 123

run_test:
	java -ea expression.ExpressionTest hard

build_parser: build
	javac expression/parser/*.java
	
build_exceptions: build_parser
	javac expression/exceptions/*.java
run_exceptions_test_powlog:
	java -ea expression.exceptions.ExceptionsPowLogTest
run_exceptions_test:
	java -ea expression.exceptions.ExceptionsTest
run_exceptions:
	java expression.exceptions.Main

run_parser:
	java expression.parser.Main
run_parser_test:
	java -ea expression.parser.ParserTest
