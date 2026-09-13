PYTHON ?= python
LATEX ?= pdflatex

.PHONY: pdf check experiment clean

pdf:
	cd manuscript && $(LATEX) -interaction=nonstopmode -halt-on-error solution.tex
	cd manuscript && $(LATEX) -interaction=nonstopmode -halt-on-error solution.tex

check:
	OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 $(PYTHON) code/verify.py --output verification/checks.json

experiment:
	OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 $(PYTHON) code/experiment.py --sizes 2000 10000 50000 --sparsities 1 2 4 8 16 --repetitions 3 --output verification/experiments.csv

clean:
	rm -f manuscript/solution.aux manuscript/solution.log manuscript/solution.out
