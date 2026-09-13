.PHONY: pdf test clean

pdf:
	cd manuscript && pdflatex -interaction=nonstopmode -halt-on-error RA05_all_p_lower_bounds.tex
	cd manuscript && pdflatex -interaction=nonstopmode -halt-on-error RA05_all_p_lower_bounds.tex

test:
	./run_checks.sh

clean:
	rm -f manuscript/*.aux manuscript/*.log manuscript/*.out manuscript/*.toc
	rm -rf code/__pycache__
