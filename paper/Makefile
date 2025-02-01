.PHONY: clean all

PAPER=polycheck
SRC=src/*.tex             \
    lib/*.tex             \
    papers.bib            \
    knowledges.kl         \
    ensps-colorscheme.sty \
    plainurl.bst	  \
    $(PAPER).md

TEMPLATES=templates/plain-article.tex \
	  templates/git-meta.lua      \
	  templates/lipics/lipics.tex \
	  templates/lncs/lncs.tex

FIGURES=

all: $(PAPER).pdf

# Default target: create the pdf file
%.pdf: %.tex $(FIGURES)
	latexmk -pdf -pdflatex="pdflatex -interaction=nonstopmode" $<

# How to create standalone versions of the pictures
fig/%.pdf: fig/%.tex
	@cp $^ $(notdir $^)
	pdflatex $(notdir $^)
	@mv $(notdir $@) $@
	@rm $(notdir $^)

$(PAPER).tex: $(SRC) $(TEMPLATES) ../paper-meta.yaml
	pandoc --template=templates/plain-article.tex \
		   --lua-filter=templates/git-meta.lua \
		   --metadata-file=../paper-meta.yaml \
		   --wrap=none \
		   -o $(PAPER).tex \
		   $(PAPER).md

# Create a lipics document for submission
$(PAPER).lipics.tex: $(SRC) $(TEMPLATES) ../paper-meta.yaml
	pandoc --template=templates/lipics/lipics.tex \
		   --lua-filter=templates/git-meta.lua \
		   --metadata-file=../paper-meta.yaml \
		   --wrap=none \
		   -o $(PAPER).lipics.tex \
		   $(PAPER).md

# Create a lipics document for submission
$(PAPER).lncs.tex: $(SRC) $(TEMPLATES) ../paper-meta.yaml
	pandoc --template=templates/lncs/lncs.tex \
		   --lua-filter=templates/git-meta.lua \
		   --metadata-file=../paper-meta.yaml \
		   --wrap=none \
		   -o $(PAPER).lncs.tex \
		   $(PAPER).md


# Create a single file tex document for arXiv
$(PAPER).arxiv.tex: $(SRC) $(TEMPLATES) ../paper-meta.yaml
	pandoc --template=templates/plain-article.tex \
		   --lua-filter=templates/git-meta.lua \
		   --metadata-file=../paper-meta.yaml \
		   --metadata=arxiv:true \
		   --wrap=none \
		   -o $(PAPER)-arxiv-tmp.tex \
		   $(PAPER).md
	latexmk -pdf -pdflatex="pdflatex -interaction=nonstopmode" $(PAPER)-arxiv-tmp.tex
	latexpand -o $(PAPER).arxiv.tex         \
		      --empty-comments          \
		      --expand-bbl $(PAPER)-arxiv-tmp.bbl \
              $(PAPER)-arxiv-tmp.tex
	@rm $(PAPER)-arxiv-tmp.*

# Create an archive with the single file tex document and the license
$(PAPER).arxiv.tar.gz: $(PAPER).arxiv.tex
	tar -czf $(PAPER).arxiv.tar.gz \
             $(PAPER).arxiv.tex    \
			 plainurl.bst          \
			 ensps-colorscheme.sty \
             ../LICENSE

$(PAPER).arxiv.pdf: $(PAPER).arxiv.tar.gz
	# create temporary directory
	@mkdir -p /tmp/$(PAPER).arxiv
	# extract archive
	@tar -xzf $(PAPER).arxiv.tar.gz -C /tmp/$(PAPER).arxiv
	# compile in the temporary directory
	cd  /tmp/$(PAPER).arxiv && latexmk -pdf $(PAPER).arxiv.tex
	# extract the pdf 
	@cp /tmp/$(PAPER).arxiv/$(PAPER).arxiv.pdf ./
	# delete the temporary directory
	@rm -rf /tmp/$(PAPER).arxiv/

clean: 
	latexmk -C
	rm -f *.tex *.tar.gz *.aux *.bbl *.kaux *.blg *.log *.out *.fls *.fdb_latexmk *.synctex.gz
