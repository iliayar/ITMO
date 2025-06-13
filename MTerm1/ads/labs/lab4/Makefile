.PHONY: run cfcli-test

task.cpp: sol.cpp template.cpp
	@./precompile.py
task: task.cpp
	clang++ -O0 -g task.cpp -DLOCAL -o task -std=c++23
run: task
	./task

cfcli-task: task.cpp
	@clang++ -O0 -g task.cpp -o cfcli-task -std=c++23
cfcli-test: cfcli-task
	@./cfcli-task

