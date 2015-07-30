#!/usr/bin/env bash

# 1. Build
make
make build_nav_data

# 2. Check sponge, cssmin, minify
hash sponge 2>/dev/null || { echo >&2 "sponge is not installed. Install 'moreutils'."; exit 1; }
hash cssmin 2>/dev/null || { echo >&2 "cssmin is not installed. Run 'npm -g i minify'."; exit 1; }
hash minify 2>/dev/null || { echo >&2 "minify is not installed. Run 'npm -g i minify'."; exit 1; }

# 3. Deploy
mkdir deploy
cd deploy
rm -rf *
git init
cp ../*.html ../tutorial.pdf ../quickref.pdf .
cp -r ../css ../images ../fonts ../js .
for CSS in css/*.css; do cssmin ${CSS} | sponge ${CSS} ; done
for JS in js/*.js; do minify ${JS} | sponge ${JS} ; done
git add -f *.html tutorial.pdf quickref.pdf
git add -f css/*
git add -f images/*
git add -f fonts/*
git add -f js/*
git commit -m "Update `date`"
git push git@github.com:leanprover/tutorial.git +HEAD:gh-pages
cd ../
rm -rf deploy
