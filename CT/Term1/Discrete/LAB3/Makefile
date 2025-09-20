all: build_cpp run_cpp

build_cpp:
	@g++ task.cpp -DLOCAL -o task

run_cpp:
	./task

run_py:
	python3 task.py < input.txt > output.txt
