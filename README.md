[![Build Status](https://travis-ci.org/leanprover/tutorial.svg?branch=master)](https://travis-ci.org/leanprover/tutorial)

Lean Tutorial
=============

 - Web : https://leanprover.github.io/tutorial
 - PDF : https://leanprover.github.io/tutorial/tutorial.pdf


How to Build
------------

We use [cask][cask] to install emacs dependencies ([org-mode][org-mode], [lean-mode][lean-mode], [htmlize][htmlize]).

```
sudo apt-get install mercurial python2.7 texlive-latex-recommended \
                     texlive-humanities texlive-xetex texlive-science \
                     texlive-latex-extra texlive-fonts-recommended
git clone git@github.com:leanprover/tutorial
cd tutorial
tar xvfz header/l3kernel.tar.gz -C ~/
make install-cask
make install-pygments  
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
   - Right-click and choose "Inspect Element" 
![5](https://cloud.githubusercontent.com/assets/403281/5134646/03701bf0-70de-11e4-801f-65f307d30e69.png)
   - Go to "tincr" tab, choose "Http Web Server" for project type, then select Root directory.
![4](https://cloud.githubusercontent.com/assets/403281/5134645/036c6bfe-70de-11e4-86af-c21ec79a4471.png)

[firefox-auto-reload]: https://addons.mozilla.org/en-US/firefox/addon/auto-reload
[google-tincr]: http://tin.cr


Test Lean Code in .org files
----------------------------

```bash
make test
```






