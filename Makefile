CASK_BIN ?= cask
EMACS_BIN ?= emacs
ORGS := $(wildcard *.org)
HTMLS := $(ORGS:.org=.html)
CWD := $(shell pwd)
WATCHMAN_BIN ?= $(CWD)/watchman/watchman

all: $(HTMLS)

%.html: %.org
	@if [ ! -f ~/.cask/bin/cask ]; then echo "Cask Not Found. Please do 'make install-cask' first"; exit 1; fi
	@EMACS=$(EMACS_BIN) $(CASK_BIN)
	$(EMACS_BIN) -no-site-file -q --batch -l elisp/org-batch.el --visit $< -f org-html-export-to-html

clean:
	rm -rf *.html *~

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

.PHONY: all clean install-cask install-watchman
