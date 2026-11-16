PYTHON ?= python3
.PHONY: all verify paper clean
all: paper
verify:
	$(PYTHON) scripts/reproduce.py
	$(PYTHON) scripts/manuscript_exhibits.py
paper: verify
	cd paper && latexmk -bibtex -e '$$bibtex = "bibtex8 %O %B"' -pdf -interaction=nonstopmode -halt-on-error -outdir=../build main.tex
clean:
	rm -rf build
