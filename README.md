[![Build Status](https://travis-ci.org/leanprover/tutorial.svg?branch=master)](https://travis-ci.org/leanprover/tutorial)

Lean Tutorial
=============

How to Build
------------

We use [cask][cask] to install emacs dependencies ([org-mode][org-mode], [lean-mode][lean-mode], [htmlize][htmlize]).

```
git clone git@github.com:leanprover/tutorial
cd tutorial
make install-cask
make
```

[cask]: https://github.com/cask/cask
[org-mode]: http://orgmode.org/
[lean-mode]: https://github.com/leanprover/lean/tree/master/src/emacs
[htmlize]: https://github.com/emacsmirror/htmlize
