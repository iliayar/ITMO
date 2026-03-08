.PHONY: run cfcli-test submit

task.cpp: sol.cpp template.cpp
	@./precompile.py
task: task.cpp
	clang++ -O0 -g task.cpp -DLOCAL -o task -std=c++23
run: task
	./task

submit: task.cpp
	[ -e .cf ] && cfcli submit task.cpp --no-test

cfcli-task: task.cpp
	@clang++ -O0 -g task.cpp -o cfcli-task -std=c++23
cfcli-test: cfcli-task
	@./cfcli-task

