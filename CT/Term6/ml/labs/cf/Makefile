.PHONY: run

task.cpp: sol.cpp template.cpp
	./precompile.py
task: task.cpp
	clang++ task.cpp -D_GLIBCXX_DEBUG -DLOCAL -o task -std=c++17
run: task
	./task
