all: compile


compile:
	 latexmk test.tex -pdf && find *.dot | rev | cut -b 5- | rev | xargs -d "\n" -I "{}" dot -Tpdf -o "{}.pdf" "{}.dot"
