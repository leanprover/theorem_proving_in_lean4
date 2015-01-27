CASK_BIN ?= cask
EMACS_BIN ?= emacs
LEAN_BIN ?= lean
ORGS  := $(wildcard [0-9][0-9]_*.org)
HTMLS := $(ORGS:.org=.html)
TEXS  := $(ORGS:.org=.tex)
PDFS  := $(ORGS:.org=.pdf)
CWD   := $(shell pwd)
WATCHMAN_BIN ?= $(CWD)/watchman/watchman
TMPDIR := $(shell mktemp -d /tmp/lean-tutorial.XXXX)

all: $(HTMLS) tutorial.pdf

htmls: $(HTMLS)

tutorial.org: $(ORGS)
	./merge_chapters.sh

%.html: %.org .cask elisp/org-html-export.el
	@if [ ! -f ~/.cask/bin/cask ]; then echo "Cask Not Found. Please do 'make install-cask' first"; exit 1; fi
	cat header/header.html.org $< > $(TMPDIR)/$<.temp.org
	$(EMACS_BIN) -no-site-file -q --batch -l elisp/org-html-export.el --visit $(TMPDIR)/$<.temp.org -f org-html-export-to-html
	mv $(TMPDIR)/$<.temp.html $@
	rm $(TMPDIR)/$<.temp.org

%.tex: %.org .cask elisp/org-pdf-export.el header/header.latex.org header/header.tex footer/footer.latex.org
	cat header/header.latex.org $< footer/footer.latex.org > $(TMPDIR)/$<.temp.org
	$(EMACS_BIN) -no-site-file -q --batch -l elisp/org-pdf-export.el --visit $(TMPDIR)/$<.temp.org -f org-latex-export-to-latex
	mv $(TMPDIR)/$<.temp.tex $@
	rm $(TMPDIR)/$<.temp.org

%.pdf: %.tex pygments-main
	# Use latexmk if exists otherwise use xelatex + bibtex
	if hash latexmk 2>/dev/null; then \
	    latexmk --xelatex --shell-escape $<; \
	else \
	    xelatex -shell-escape $<; bibtex $(<:.tex=); xelatex -shell-escape $<; xelatex -shell-escape $<; \
	fi

.cask: Cask
	@EMACS=$(EMACS_BIN) $(CASK_BIN)
	@touch .cask

clean:
	rm -rf $(HTMLS) \
	       ${PDFS} \
	       ${TEXS} \
	       *.acn *.aux *.glo *.idx *.ist *.log *.out *.toc *.fdb_latexmk *.fls *.ilg *.ind \
	       *.out.pyg *.pyg tutorial.* \
	       [0-9][0-9]*.lean

watch-on:
	$(WATCHMAN_BIN) watch $(CWD)
	$(WATCHMAN_BIN) -- trigger $(CWD) org-files '*.org' -- make all

watch-off:
	$(WATCHMAN_BIN) -- trigger-del $(CWD) org-files
	$(WATCHMAN_BIN) watch-del $(CWD)

install-cask:
	curl -fsSkL https://raw.github.com/cask/cask/master/go | python

install-watchman:
	git clone https://github.com/facebook/watchman.git
	cd watchman &&./autogen.sh && ./configure && make

pygments-main: install-pygments

install-pygments:
	if [ ! -d pygments-main ] ; then hg clone https://bitbucket.org/birkenfeld/pygments-main && cd pygments-main && sudo python setup.py install; fi

test:
	for ORG in $(ORGS); do ./test.sh $(LEAN_BIN) $$ORG || exit 1; done

.PHONY: all clean install-cask install-watchman watch-on watch-off
