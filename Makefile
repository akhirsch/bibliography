BIB := bibliography/akh.bib
NOTES_FILES := notes.tex
PAPER_FILES := 

main: notes 

all: notes 

# outline: paper-outline.pdf
notes: notes.pdf
# ICFPAnon: ICFPAnon.pdf
# ICFPCR: ICFPCameraReady.pdf
# TRAnon: TRAnon.pdf
# TRCR: TRCameraReady.pdf
# ACMTRAnon: ACMTRAnon.pdf
# ACMTRCR: ACMTRCameraReady.pdf

notes.pdf: notes.tex $(BIB) $(NOTES_FILES)
	latexmk -pdf -bibtex -synctex=1 $<

# paper-outline.pdf: paper-outline.org
# 	pandoc -o paper-outline.pdf paper-outline.org

%.pdf: %.tex $(PAPER_FILES) $(BIB)
	latexmk -pdf -bibtex -synctex=1 $<

.PHONY: clean cleanall notes all # outline ICFPAnon ICFPCR TRAnon TRCR

notes: notes.pdf

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
