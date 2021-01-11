all: maven


maven:
	mvn compile test; mvn surefire-report:report-only

test:
	cd target/classes && \
		java -jar -ea QueueTest.jar

test_functions:
	cd target/classes && \
		java -jar -ea QueueFunctionsTest.jar
