.PHONY: run perf

browser = brave

task: main.cpp
	clang++ -std=c++17 main.cpp -o task

run: task
	./task

perf: main.cpp
	clang++ -O3 -pg main.cpp -o taskperf
	perf record -g ./taskperf
	perf script | stackcollapse-perf.pl | flamegraph.pl > flamegraph.svg
	$(browser) flamegraph.svg
