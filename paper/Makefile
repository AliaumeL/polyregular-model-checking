.PHONY: clean

PAPER=polycheck
SRC=src/*.tex             \
	lib/*.tex             \
	papers.bib            \
	knowledges.kl         \
	ensps-colorscheme.sty \
	plainurl.bst		  \
	$(PAPER).tex

TEMPLATES=templates/plain-article.tex \
		  templates/git-meta.lua 

FIGURES=

# Default target: create the pdf file
$(PAPER).pdf: $(SRC) $(FIGURES)
	latexmk -pdf -pdflatex="pdflatex -interaction=nonstopmode" $(PAPER).tex


# How to create standalone versions of the pictures
fig/%.pdf: fig/%.tex
	@cp $^ $(notdir $^)
	pdflatex $(notdir $^)
	@mv $(notdir $@) $@
	@rm $(notdir $^)

$(PAPER).tex: $(PAPER).md $(TEMPLATES) ../paper-meta.yaml
	pandoc --template=templates/plain-article.tex \
		   --lua-filter=templates/git-meta.lua \
		   --metadata-file=../paper-meta.yaml \
		   -o $(PAPER).tex \
		   $(PAPER).md

# Create a single file tex document for arXiv
$(PAPER).arxiv.tex: $(PAPER).pdf
	latexpand -o $(PAPER).arxiv.tex     \
			  --empty-comments          \
		      --expand-bbl $(PAPER).bbl \
              $(PAPER).tex

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
	rm -f $(PAPER).arxiv.tex $(PAPER).arxiv.tar.gz $(PAPER).arxiv.pdf
