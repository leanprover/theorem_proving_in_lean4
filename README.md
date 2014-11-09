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


Automatic Build using Watchman
------------------------------

Using [watchman][watchman], we can detect any changes on the
org-files, and trigger re-builds automatically on the background.

To install [watchman][watchman]:

```
sudo apt-get install automake
make install-watchman
```

To enable watch:

```
make watch-on
```

To disable watch:

```
make watch-off
```

[watchman]: https://github.com/facebook/watchman


How to preview generated HTML files
-----------------------------------

It requires a webserver to preview generated HTML files. We can use Python's `SimpleHTTPServer` module:

```bash
tutorial $ python -m SimpleHTTPServer
```

The above command starts a HTTP server at `tutorial` directory (default port: `8000`). For example, `example.html` is available at `http://localhost:8000/example.html`.


Auto-reload HTML page
---------------------

 - Firefox: [Auto Reload][firefox-auto-reload] add-on
   - Tools > AutoReload Preferences
![1](https://cloud.githubusercontent.com/assets/403281/4966611/b211cda0-67d5-11e4-876e-a705f3326ac0.png)
   - Create Reload Rule
![2](https://cloud.githubusercontent.com/assets/403281/4966612/b3bdac00-67d5-11e4-83c9-118a4af8b0ea.png)
   - Link .html in the filesystem
![3](https://cloud.githubusercontent.com/assets/403281/4966613/b6461110-67d5-11e4-9d62-93c1e2a8f0da.png)

 - Chrome: [Tincr][google-tincr] (does *not* work on Linux)

[firefox-auto-reload]: https://addons.mozilla.org/en-US/firefox/addon/auto-reload
[google-tincr]: http://tin.cr






