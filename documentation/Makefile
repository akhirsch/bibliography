BIB := ../bibliography/main.bib
PAPER_FILES := PACMAnon.tex PACMCameraReady.tex main.tex includes.tex macros.tex sections.tex appendices.tex abstract.tex acmart.cls

export TEXINPUTS = .::./sections::./appendices::$TEXMF/tex/::../styles::../latex-pl-syntax

main: PACMTRCR
all: PACMAnon PACMCR PACMTRAnon PACMTRCR

PACMAnon: PACMAnon.pdf
PACMCR: PACMCameraReady.pdf
PACMTRAnon: PACMTRAnon.pdf
PACMTRCR: PACMTRCameraReady.pdf

%.pdf: %.tex $(PAPER_FILES) $(BIB)
	latexmk -pdf -bibtex -synctex=1 $<

.PHONY: clean cleanall all PACMAnon PACMCameraReady

ALLCLEANABLES := $(shell find . \( -name '*.aux'\
                             -o -name '\#*\#'\
			     -o -name '*.log'\
			     -o -name '*.bbl'\
                             -o -name '*.out'\
                             -o -name '*~'\
                             -o -name '*.pdf'\
                             -o -name '*.dvi'\
                             -o -name '*.synctex.gz'\
                             -o -name '*.blg'\
                             -o -name 'paper-outline.tex'\
                             -o -name '*.toc'\
                             -o -name '*.lot'\
			     -o -name '*.fls'\
			     -o -name '*.rip'\
			     -o -name '*.fdb_latexmk'\
			     -o -name '*.xcp'\
			     -o -name '*.xoj'\
                             -o -name '*.lof' \) -type f -not -path "./submissions/*" -not -path "./.git/*" -not -name 'acmart.pdf')

CLEANABLES := $(shell find . \( -name '*.aux'\
			     -o -name '\#*\#'\
			     -o -name '*.log'\
			     -o -name '*.bbl'\
                             -o -name '*.out'\
                             -o -name '*~'\
                             -o -name '*.synctex.gz'\
                             -o -name '*.blg'\
                             -o -name 'paper-outline.tex'\
                             -o -name '*.toc'\
                             -o -name '*.lot'\
			     -o -name '*.fls'\
			     -o -name '*.rip'\
			     -o -name '*.fdb_latexmk'\
			     -o -name '*.xcp'\
                             -o -name '*.lof' \) -type f -not -path "./submissions/*" -not -path "./.git/*")

clean: 
	@for f in $(CLEANABLES); do \
		echo "REMOVING $$f";\
		rm $$f;\
	done

cleanall: 
	@for f in $(ALLCLEANABLES); do \
		echo "REMOVING $$f";\
		rm $$f;\
	done
