# The main (final) document name
main_pdf = final.pdf

# The directory of your bib files
bib_dir = bib

# Split a pdf
# gs -dBATCH -dNOPAUSE -q -sDEVICE=pdfwrite -dFirstPage=1 -dLastPage=15 -sOUTPUTFILE=desc_no_refs.pdf desc.pdf

# The list of pdfs that we need to generate separately in the order of
# appearance in the main pdf
desc = desc
pdfs = $(desc).pdf budget.pdf facilities.pdf data.pdf personnel.pdf
pdfsb = $(desc).pdf budget.pdf facilities.pdf data.pdf personnel.pdf

# look for files
find = $(foreach dir,$(1),$(wildcard $(dir)/*.$(2)))
tex_files = desc.tex budget.tex facilities.tex data.tex personnel.tex

junk +=	*.aux *.log *.lof *.lot *.toc *.blg *.bbl *~ *.synctex.gz *.fdb_latexmk *.fls

all: $(pdfsb)
#	pdfjoin -o $(main_pdf) $(pdfs)
#	gs -dBATCH -dNOPAUSE -q -sDEVICE=pdfwrite -dFirstPage=1 -dLastPage=15 -sOUTPUTFILE=$(desc)_no_refs.pdf $(desc).pdf
#	gs -dBATCH -dNOPAUSE -q -sDEVICE=pdfwrite -dFirstPage=16 -sOUTPUTFILE=references.pdf $(desc).pdf

# Just regenerate everything whenever there's any change in any tex or bib file.
# It's not nice, I guess, but I think it's better than tracking dependencies.
$(pdfsb): $(tex_files) 

$(pdfsb): %.pdf: %.tex $(bib_dir)/*.bib
	latexmk -pdf -synctex=1 $<
#	pdflatex $<
#	bibtex $(desc)
#	pdflatex $<
#	bibtex $(desc)
#	pdflatex $<
clean:
	rm -f $(junk)
	rm *.pdf

