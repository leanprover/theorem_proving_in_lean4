CASK_BIN ?= cask
EMACS_BIN ?= emacs
ORGS := $(wildcard *.org)
HTMLS := $(ORGS:.org=.html)

all: $(HTMLS)

%.html: %.org
	@if [ ! -f ~/.cask/bin/cask ]; then echo "Cask Not Found. Please do 'make install-cask' first"; exit 1; fi
	@EMACS=$(EMACS_BIN) $(CASK_BIN)
	$(EMACS_BIN) -no-site-file -q --batch -l elisp/org-batch.el --visit $< -f org-html-export-to-html

clean:
	rm -rf *.html *~

install-cask:
	curl -fsSkL https://raw.github.com/cask/cask/master/go | python

.PHONY: all clean install-cask
