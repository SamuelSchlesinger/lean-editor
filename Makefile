.PHONY: pearl check-pearl

check-pearl:
	python3 scripts/check_pearl.py
	lake build --wfail

pearl: check-pearl
	mkdir -p tmp/pdfs/pearl output/pdf
	latexmk -pdf -interaction=nonstopmode -halt-on-error -file-line-error -outdir=tmp/pdfs/pearl PEARL.tex
	cp tmp/pdfs/pearl/PEARL.pdf output/pdf/PEARL.pdf
