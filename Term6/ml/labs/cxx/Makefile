all: build run

build:
	./precompile.py
	g++ task.cpp -DLOCAL -o task --std=c++17

run:
	./task
