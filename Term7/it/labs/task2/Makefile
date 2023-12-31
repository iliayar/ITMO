.PHONY: run perf

browser = brave

task: main.cpp
	clang++ -std=c++17 -w main.cpp -DDEBUG -o task

task-rel: main.cpp
	clang++ -std=c++17 -w main.cpp -o task-rel

run-rel: task-rel
	./task-rel

run: task
	./task

perf: main.cpp
	clang++ -O3 -pg main.cpp -o taskperf
	perf record -g ./taskperf
	perf script | stackcollapse-perf.pl | flamegraph.pl > flamegraph.svg
	$(browser) flamegraph.svg
