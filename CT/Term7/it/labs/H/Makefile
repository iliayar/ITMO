.PHONY: run_P run_LLR run_S perf_P perf_LLR perf_S

browser = brave

VARIANTS = P LLR S

define make-variant-targets
task_$1: main_$1.cpp
	clang++ -std=c++17 -g -O0 -w main_$1.cpp -DDEBUG -o task_$1
task-rel_$1: main_$1.cpp
	clang++ -std=c++17 -w main_$1.cpp -o task-rel_$1
run-rel_$1: task-rel_$1
	./task-rel_$1
run_$1: task_$1
	./task_$1
perf_$1: main_$1.cpp
	clang++ -O3 -pg main_$1.cpp -o taskperf_$1
	perf record -g ./taskperf_$1
	perf script | stackcollapse-perf.pl | flamegraph.pl > flamegraph_$1.svg
	$(browser) flamegraph_$1.svg
endef

$(foreach variant,$(VARIANTS),$(eval $(call make-variant-targets,$(variant))))
