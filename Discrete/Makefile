all: compile run
python: run_py
tex: build_tex show_tex

compile:
	@g++ task.cpp -o task -D LOCAL

run:
	./task

run_py:
	python task.py LOCAL

build_tex:
	latexmk -halt-on-error -f -xelatex Discrete.tex

show_tex:
	zathura Discrete.pdf

tex_clean:
	latexmk -c
