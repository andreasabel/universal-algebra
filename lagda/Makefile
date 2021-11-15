# Makefile for agda2lagda generated pdfs

# Disable built-in rules
MAKEFLAGS += --no-builtin-rules
.SUFFIXES:

destdir=$(HOME)/public_html

# commands
bibtool=bibtool -- 'preserve.key.case = ON' \
	  -- 'print.use.tab = OFF' \
	  -- 'check.double = ON' \
	  -- 'check.double.delete = ON' \
	  -- 'delete.field = { abstract }' \
	  -- 'delete.field = { dvi }' \
	  -- 'delete.field = { postscript }' \
	  -- 'delete.field = { pdf }' \
	  -- 'delete.field = { month }' \
	  -- 'delete.field = { isbn }' \
	  -- 'delete.field = { note }'
#	  -- 'delete.field = { editor }'
#	  -- 'delete.field = { doi }' \

catcfg=sed -e "s/%.*//g" <
latex=xelatex
bibliography=medium.bib

files=lipics-v2019.cls Makefile \
  cc-by.pdf lipics-logo-bw.pdf orcid.pdf \
  SK-Bool-ortho.lagda.tex \
  latex/agda.sty \
  latex/SK-Bool-ortho.tex

.PHONY : default add all pack ship debugMake html

.PRECIOUS : %.pdf %.tex # %.dvi %.ps %.gz

default : MultiSortedAlgebra.pdf

all : default

ship : $(destdir)/agda/MultiSortedAlgebra.pdf

# The generic rule does somehow not work
.PHONY: ship-%
ship-% : $(destdir)/agda/%.pdf

.PHONY: pack
pack : MultiSortedAlgebra.zip

# pack sources for arXiv
MultiSortedAlgebra.zip : MultiSortedAlgebra.tex template.tex latex/MultiSortedAlgebra.tex latex/agda.sty auto-MultiSortedAlgebra.bib  MultiSortedAlgebra.bbl
	zip $@ $^

%.lagda.tex : ../%.agda
	agda2lagda --force -o $@ $<

latex/%.tex : %.lagda.tex
	agda --latex $<

# MultiSortedAlgebra
##################################################################

# initially, run latex once to create an .aux file
# mark .aux file as fresh by creating a stamp _aux
MultiSortedAlgebra_aux : MultiSortedAlgebra.tex template.tex latex/MultiSortedAlgebra.tex
	-$(latex) $<;
	touch $@;

# main
##################################################################

# main.pdf: main.tex $(files)
# 	latexmk -f -pdf main.tex

# initially, run latex once to create an .aux file
# mark .aux file as fresh by creating a stamp _aux
main_aux : main.tex $(files)
	-$(latex) $<;
	touch $@;

# then, run bibtex
main.bbl : main_aux auto-main.bib
	-bibtex main;

# finally, finish by running latex twice again
# this will update .aux, but leave the stamp _aux intact
# (otherwise we would not converge and make would never
# return a "Nothing to do")
main.pdf : main.bbl
	-$(latex) main.tex;
	$(latex) main.tex;

# auto-main.bib is only defined if bibtool is present and all.bib exists

ifneq ($(shell which bibtool),)
ifneq ($(shell ls $(bibliography)),)
auto-main.bib : main_aux $(bibliography)
	echo "%%%% WARNING! AUTOMATICALLY CREATED BIBFILE" > $@;
	echo "%%%% DO NOT EDIT! ALL CHANGES WILL BE LOST!" >> $@ ;
	echo "" >> $@ ;
	$(bibtool) -x main.aux -i $(bibliography) >> $@;
endif
endif

# main-long
##################################################################

# initially, run latex once to create an .aux file
# mark .aux file as fresh by creating a stamp _aux
main-long_aux : main-long.tex $(files)
	$(latex) main-long.tex;
	touch $@;

# then, run bibtex
main-long.bbl : main-long_aux auto-main.bib
	-bibtex main-long;

# finally, finish by running latex twice again
# this will update .aux, but leave the stamp _aux intact
# (otherwise we would not converge and make would never
# return a "Nothing to do")
main-long.pdf : main-long.bbl
	$(latex) main-long.tex;
	$(latex) main-long.tex;

# auto-main-long.bib is only defined if bibtool is present and all.bib exists

ifneq ($(shell which bibtool),)
ifneq ($(shell ls $(bibliography)),)
auto-main-long.bib : main-long_aux $(bibliography)
	echo "%%%% WARNING! AUTOMATICALLY CREATED BIBFILE" > $@;
	echo "%%%% DO NOT EDIT! ALL CHANGES WILL BE LOST!" >> $@ ;
	echo "" >> $@ ;
	$(bibtool) -x main-long.aux -i $(bibliography) >> $@;
endif
endif


# Templates for the LaTeX build

# then, run bibtex
%.bbl : %_aux auto-%.bib
	-bibtex $*;

# finally, finish by running latex twice again
# this will update .aux, but leave the stamp _aux intact
# (otherwise we would not converge and make would never
# return a "Nothing to do")
%.pdf : %.bbl
	-$(latex) $*.tex;
	$(latex) $*.tex;

# auto-%.bib is only defined if bibtool is present and $(bibliography) exists
ifneq ($(shell which bibtool),)
ifneq ($(shell ls $(bibliography)),)
auto-%.bib : %_aux $(bibliography)
	echo "%%%% WARNING! AUTOMATICALLY CREATED BIBFILE" > $@;
	echo "%%%% DO NOT EDIT! ALL CHANGES WILL BE LOST!" >> $@ ;
	echo "" >> $@ ;
	$(bibtool) -x $*.aux -i $(bibliography) >> $@;
endif
endif

# Templates

$(destdir)/agda/% : %
	cp -p $< $@

talk% : talk%.pdf
	cp -p $? $(destdir)/;
	touch $@;

talk%.pdf : talk%.tex
	latex $<;

# %.tex : %.lhs
# 	lhs2TeX --poly -i lhs2TeX.fmt $< > $@
# # /usr/local/share/lhs2tex-1.13/

% : %.pdf # %.dvi %.ps.gz # %.tar.gz
	cp -p $? $(destdir)/;
	touch $@;

# %.pdf : %.dvi
# 	latex $*.tex;

# %.ps  : %.dvi
# 	dvips -o $@ $<;

# %.gz : %
# 	cat $< | gzip > $@

## does not work since $ is evaluated before %
#%.tar : %.cfg $(shell cat %.cfg)
#	echo $?


#EOF
