.PHONY: check pdf

check:
	bash run_checks.sh

pdf:
	mkdir -p build
	cp manuscript/RA05_unrestricted_quartic.tex build/
	cd build && pdflatex -interaction=nonstopmode -halt-on-error RA05_unrestricted_quartic.tex
	cd build && pdflatex -interaction=nonstopmode -halt-on-error RA05_unrestricted_quartic.tex
	cd build && pdflatex -interaction=nonstopmode -halt-on-error RA05_unrestricted_quartic.tex
	@echo "Rebuilt PDF: build/RA05_unrestricted_quartic.pdf (packaged PDF unchanged)"
