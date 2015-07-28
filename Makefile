CASK_BIN ?= cask
EMACS_BIN ?= emacs
LEAN_BIN ?= lean
ORGS  := $(wildcard [0-9A][0-9]_*.org)
HTMLS := $(ORGS:.org=.html)
TEXS  := $(ORGS:.org=.tex)
PDFS  := $(ORGS:.org=.pdf)
CWD   := $(shell pwd)
WATCHMAN_BIN ?= $(CWD)/watchman/bin/watchman
TMPDIR := $(shell mktemp -d /tmp/lean-tutorial.XXXX)
NAV_DATA := js/nav_data.js

all: $(HTMLS) tutorial.pdf build_nav_data

htmls: $(HTMLS)

tutorial.org: $(ORGS)
	./merge_chapters.sh

%.html: %.org .cask elisp/org-html-export.el header/html.org footer/bib.html.org lean.bib
	@if [ ! -f ~/.cask/bin/cask ]; then echo "Cask Not Found. Please do 'make install-cask' first"; exit 1; fi
	cat header/html.org $< > $(TMPDIR)/$<.temp.org
	(grep "\\\\cite{" $< && cat footer/bib.html.org >> $(TMPDIR)/$<.temp.org) || true
	cp *.bib $(TMPDIR)
	$(EMACS_BIN) --no-site-file --no-site-lisp -q --batch -l elisp/org-html-export.el --visit $(TMPDIR)/$<.temp.org -f org-html-export-to-html
	mv $(TMPDIR)/$<.temp.html $@
	rm $(TMPDIR)/$<.temp.org

tutorial.tex: tutorial.org .cask elisp/org-pdf-export.el header/latex.org header/latex.tex footer/latex.org lean.bib
	make gitinfo
	cat header/latex.org $< footer/latex.org > $(TMPDIR)/$<.temp.org
	$(EMACS_BIN) --no-site-file --no-site-lisp -q --batch -l elisp/org-pdf-export.el --visit $(TMPDIR)/$<.temp.org -f org-latex-export-to-latex
	mv $(TMPDIR)/$<.temp.tex $@
	rm $(TMPDIR)/$<.temp.org

%.pdf: %.tex pygments-main
	# # Use latexmk if exists otherwise use xelatex + bibtex
	# if hash latexmk 2>/dev/null; then \
	#     latexmk --xelatex --shell-escape $<; \
	# else \
	#     xelatex -shell-escape $<; bibtex $(<:.tex=); xelatex -shell-escape $<; xelatex -shell-escape $<; \
	# fi
	# Ubuntu-12.04 uses an old version of latexmk which does not support XeLaTeX related options
	xelatex -shell-escape $<; bibtex $(<:.tex=); xelatex -shell-escape $<; xelatex -shell-escape $<

.cask: Cask
	@EMACS=$(EMACS_BIN) $(CASK_BIN) install
	@touch .cask

clean:
	rm -rf $(HTMLS) \
	       ${PDFS} \
	       ${TEXS} \
	       *.acn *.aux *.glo *.idx *.ist *.log *.out *.toc *.fdb_latexmk *.fls *.ilg *.ind \
	       *.out.pyg *.pyg tutorial.* \
	       [0-9][0-9]*.lean \
	       _minted-*

dist-clean:
	make clean
	rm -rf .cask watchman pygments-main

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
	cd watchman &&./autogen.sh && ./configure --prefix $(CWD)/watchman && make install

pygments-main: install-pygments

install-pygments:
	if [ ! -d pygments-main ] ; then hg clone https://bitbucket.org/leanprover/pygments-main && cd pygments-main && python setup.py build; fi

gitinfo:
	git log -1 --date=short \
	--pretty=format:"\usepackage[shash={%h},lhash={%H},authname={%an},authemail={%ae},authsdate={%ad},authidate={%ai},authudate={%at},commname={%an},commemail={%ae},commsdate={%ad},commidate={%ai},commudate={%at},refnames={%d}]{gitsetinfo}" HEAD > $(CWD)/gitHeadInfo.gin

test:
	for ORG in $(ORGS); do ./test.sh $(LEAN_BIN) $$ORG || exit 1; done
test_js:
	for ORG in $(ORGS); do ./test_js.sh $$ORG || exit 1; done

build_nav_data: $(HTMLS)
	echo "var lean_nav_data = [" > $(NAV_DATA)
	ls -1 [A0-9][0-9]_*.html | sed 's/\(.*\)/"\1",/' >> $(NAV_DATA)
	echo "];" >> $(NAV_DATA)

.PHONY: all clean install-cask install-watchman watch-on watch-off gitinfo
