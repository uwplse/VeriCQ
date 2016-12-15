all: paper.pdf abstract.txt

paper.pdf: bibliography.bib $(wildcard *.tex) figures
	scripts/latexrun -O . --bibtex-args=-min-crossrefs=99 paper

abstract.txt: abstract.tex
	@sed -e 's/\\vspace{.*}//g'       \
			 -e 's/\\begin{abstract}//g'  \
			 -e 's/\\end{abstract}//g'    \
			 -e 's/\\todo{.*}//g'         \
			 -e 's/\\label{.*}//g'        \
			 -e 's/\\looseness=[^ ]*//g'  \
			 -e 's/\\[a-z]*{\(.*\)}/\1/g' \
			 -e 's/``/"/g'                \
			 -e "s/''/\"/g"               \
			 -e 's/\\//g'                 \
			 -e '/^%.*/d'                 \
			 -e 's/~/ /g'               \
			 -e 's/^ *//g'                \
			 -e 's/  */ /g'               \
			 $^ | cat -s | fmt -w 72 > $@


clean:
	scripts/latexrun --clean-all
	rm -f abstract.txt paper.pdf latex.out 

cleaner:
	rm -f bibliography.bib *.pdf *.pdf_tex 

bibliography.bib:
	cp ../bagpipe-papers/related/bibliography.bib .

include Makefile.spell

%.pdf : fig/%.svg
	inkscape -z --export-pdf=`pwd`/$@ --export-latex `pwd`/$<

figures: 

.PHONY: tags clean cleaner
TAGS: tags
tags:
	etags `latex-process-inputs -list paper.tex | perl -p -e 's:(code/(locksrv|seqnum|pbj))\.tex:\1.v:'`
