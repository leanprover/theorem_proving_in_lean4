;; emacs org-mode batch configuration
(require 'cask "~/.cask/cask.el")
(cask-initialize "./")
(setq working-dir (f-dirname (f-this-file)))
(add-to-list 'load-path working-dir)
(setq make-backup-files nil)

;;; ORG mode
(require 's)
(require 'f)
(require 'org)
(require 'ox-bibtex)
(require 'dash)
(require 'dash-functional)
(add-to-list 'load-path (f-join working-dir "elisp"))
(require 'lean-export-util)

(setq org-html-style-include-default nil)
(setq org-html-style-include-scripts nil)

;; set auto load on .org files
(add-to-list 'auto-mode-alist '("\\.org\\'" . org-mode))

;; org mode customisations
'(org-export-blocks (quote ((comment org-export-blocks-format-comment t) (ditaa org-export-blocks-format-ditaa nil) (dot org-export-blocks-format-dot t) (r org-export-blocks-format-R nil) (R org-export-blocks-format-R nil))))
'(org-export-html-inline-images t)
'(org-export-html-use-infojs t)
'(org-export-htmlize-output-type "css")
'(org-export-html-validation-link "<p class=\"xhtml-validation\"><a href=\"http://validator.w3.org/check?uri=referer\">Validate XHTML 1.0</a></p>")
'(org-export-html-with-timestamp nil)
'(org-modules (quote (org-bbdb org-bibtex org-info org-jsinfo org-irc org-w3m org-mouse org-eval org-eval-light org-exp-bibtex org-man org-mtags org-panel org-R org-special-blocks org-exp-blocks)))

;; Return the Lean tutorial example main part
(defun lean-example-main-part (code)
  (car (lean-extract-code code)))

;; Return the Lean tutorial example full code.
(defun lean-example-full (code)
  (cdr (lean-extract-code code)))

(defvar-local lean-src-block-counter 0)

;; Redefine org-html-src-block to use juicy-ace-editor
(eval-after-load "ox-html"
  '(defun org-html-src-block (src-block contents info)
     "Transcode a SRC-BLOCK element from Org to HTML.
CONTENTS holds the contents of the item.  INFO is a plist holding
contextual information."
     (setq lean-src-block-counter (1+ lean-src-block-counter))
     (if (org-export-read-attribute :attr_html src-block :textarea)
         (org-html--textarea-block src-block)
       (let ((lang (org-element-property :language src-block))
             (caption (org-export-get-caption src-block))
             (code (org-html-format-code src-block info))
             (label (let ((lbl (org-element-property :name src-block)))
                      (if (not lbl) ""
                        (format " id=\"%s\""
                                (org-export-solidify-link-text lbl))))))
         (if (not lang) (format "<pre class=\"example\"%s>\n%s</pre>" label code)
           (format
            "<div class=\"org-src-container\">\n%s%s\n</div>"
            (if (not caption) ""
              (format "<label class=\"org-src-name\">%s</label>"
                      (org-export-data caption info)))
            (cond ((or (string= lang "lean")
                       (string= lang "lean_text"))
                   (let ((juicy-ace-editor-html
                       (format "<juicy-ace-editor id='lean-juicy-ace-editor-%d' mode=\"ace/mode/%s\" readonly=\"true\">%s</juicy-ace-editor>"
                               lean-src-block-counter
                               "lean"
                               (lean-example-main-part code)))
                      (full-code-html (format "<div id='lean-full-code-%d' style='display:none'>%s</div>"
                                             lean-src-block-counter
                                             (lean-example-full code)))
                      (button-html
                       (if (string= lang "lean")
                           (format "<div class='no-print' align=\"left\"><button type=\"button\" onclick=\"invoke_leanjs($('#lean-full-code-%d').text());\">Try it yourself &raquo;</button></div>"
                                   lean-src-block-counter)
                         "")))
                     (concat juicy-ace-editor-html full-code-html button-html)))
                  (t
                   (format "\n<pre class=\"src src-%s\"%s>%s</pre>" lang label code)))))))))
(setq org-confirm-babel-evaluate nil)

(defun lean-extract-chapter-name (str)
  (let ((num (string-to-number str)))
    (cond ((= num 0) str)
          (t (format "%d" num)))))

(defun lean-filter-headline (text backend info)
  "Adjust the chapter number based on the filename. For example,
when the filename is '07_Induction_and_Recursion.org', it uses
'7' as a chapter number instead of '1' which is the default
value."
  (when (org-export-derived-backend-p backend 'html)
    (let ((file-name (f-filename (buffer-file-name))))
      (save-match-data
        (when (and
               (>= (length file-name) 2)
               (let ((case-fold-search t))
                 (string-match (rx
                                (group "<span class=\"section-number-"
                                       (+ (char digit))
                                       "\">")
                                (group (char digit))
                                (group (* (char digit ".")))
                                (group "</span>"))
                               text)))
          (replace-match (format "\\1 %s\\3\\4"
                                 (lean-extract-chapter-name (s-left 2 file-name)))
                         t nil text))))))

(defun lean-filter-html-link (text backend info)
  (when (eq backend 'html)
    (cond
     ;; 1. Extenral Links (starting with 'https://', 'http://', or '//')
     ;;    => add "target='_blank'"
     ((string-match
       (rx (group "href=\"" (or "http://" "https://" "//"))) text)
      (message "=================")
      (message "External Link: %s" text)
      (replace-match "target='_blank' \\1" t nil text))
     ;; 2. Internal Links
     ;; 2.1. (matched with "<a href="filename#anchor">
     ((string-match
       (rx "<a href=\"" (group (+ (not (any "#")))) "#" (group (+ (not (any "\"")))) "\"") text)
      (message "=================")
      (message "Internal Link -- filename + anchor: %s" text)
      (replace-match "<a href=\"#\" onclick=\"myModule.loadTutorial('\\1', '\\2')\"" t nil text))
     ;; 2.2.1 (matched with "<a href="#sec-?.*">
     ((string-match
       (rx "<a href=\"#sec-" (one-or-more digit)
           (group (zero-or-more "-" (one-or-more digit))))
       text)
      (message "=================")
      (message "Internal Link -- only anchor (sec): %s" text)
      (let* ((chapter-num-from-file
              (int-to-string
               (string-to-int
                (s-left 2 (f-filename (buffer-file-name))))))
             (rest-org (match-string 1 text))
             (rest (s-replace-all '(("-" . ".")) rest-org)))
        (s-concat
         "<a href=\"#\" onclick=\"myModule.scrollTutorialTo('"
         chapter-num-from-file
         rest
         "')\">"
         chapter-num-from-file
         rest
         "</a>"
         )))
     ;; 2.2.2 (matched with "<a href="#anchor">
     ((string-match
       (rx "<a href=\"#" (group (+ (not (any "\"")))) "\"") text)
      (message "=================")
      (message "Internal Link -- only anchor: %s" text)
      (replace-match "<a href=\"#\" onclick=\"myModule.scrollTutorialTo('\\1')\"" t nil text)
      )
     ;; 2.3. (matched with "<a href="filename">
     ((string-match
       (rx "<a href=\"" (group (+ (not (any "\"")))) "\"") text)
      (message "=================")
      (message "Internal Link -- only file: %s" text)
      (replace-match "<a href=\"#\" onclick=\"myModule.loadTutorial('\\1', null)\"" t nil text))
     )))

(eval-after-load 'ox
  '(progn
     (add-to-list 'org-export-filter-link-functions 'lean-filter-html-link)
     (add-to-list 'org-export-filter-headline-functions 'lean-filter-headline)
     (setq org-html-mathjax-options
           '((path  "//cdn.mathjax.org/mathjax/latest/MathJax.js?config=TeX-AMS-MML_HTMLorMML")
             (scale "100")
             (align "center")
             (indent "2em")
             (mathml nil)))
     (setq org-html-mathjax-template
           "<script type=\"text/x-mathjax-config\">
    MathJax.Hub.Config({
        // Only one of the two following lines, depending on user settings
        // First allows browser-native MathML display, second forces HTML/CSS
        :MMLYES: config: [\"MMLorHTML.js\"], jax: [\"input/TeX\"],
        :MMLNO: jax: [\"input/TeX\", \"output/HTML-CSS\"],
        extensions: [\"tex2jax.js\",\"TeX/AMSmath.js\",\"TeX/AMSsymbols.js\",
                     \"TeX/noUndefined.js\"],
        tex2jax: {
            inlineMath: [ [\"\\\\(\",\"\\\\)\"] ],
            displayMath: [ ['$$','$$'], [\"\\\\[\",\"\\\\]\"], [\"\\\\begin{displaymath}\",\"\\\\end{displaymath}\"] ],
            skipTags: [\"script\",\"noscript\",\"style\",\"textarea\",\"pre\",\"code\"],
            ignoreClass: \"tex2jax_ignore\",
            processEscapes: false,
            processEnvironments: true,
            preview: \"TeX\"
        },
        showProcessingMessages: true,
        displayAlign: \"%ALIGN\",
        displayIndent: \"%INDENT\",

        \"HTML-CSS\": {
             scale: %SCALE,
             availableFonts: [\"STIX\",\"TeX\"],
             preferredFont: \"TeX\",
             webFont: \"TeX\",
             imageFont: \"TeX\",
             showMathMenu: true,
        },
        MMLorHTML: {
             prefer: {
                 MSIE:    \"MML\",
                 Firefox: \"MML\",
                 Opera:   \"HTML\",
                 other:   \"HTML\"
             }
        }
    });
</script>
<script type=\"text/javascript\" src=\"%PATH\"></script>")))
