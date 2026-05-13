paper.pdf: paper.tex Makefile definitions.tex paper.bib 
	rm -f *.aux
	pdflatex -shell-escape paper
	bibtex paper
	pdflatex -shell-escape paper
	pdflatex -shell-escape paper

clean:
	rm -f *.aux *.log *.pyg *.out *.bbl *.blg
