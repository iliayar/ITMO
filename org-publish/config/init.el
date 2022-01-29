(message "Loading Emacs init file")

(load "/publish/packages.el")

(require 'org)
(require 'ox-latex)
(require 'htmlize)
(require 'haskell-mode)

(org-reload)

(defun org-publish-command () (org-publish-project "conspects"))

(setq org-latex-packages-alist '(
                                 ("T1, T2A" "fontenc" t)
                                 ("lutf8" "luainputenc" t)
                                 ("english,russian" "babel" t)
                                 ("" "minted" t)
                                 ("" "graphicx" t)
                                 ("" "longtable" t)
                                 ("" "hyperref" t)
                                 ("" "xcolor" t)
                                 ("" "natbib" t)
                                 ("" "amssymb" t)
                                 ("" "stmaryrd" t)
                                 ("" "amsmath" t)
                                 ("" "caption" t)
                                 ("" "mathtools" t)
                                 ("" "amsthm" t)
                                 ("" "tikz" t)
                                 ("" "fancyhdr" t)
                                 ("" "lastpage" t)
                                 ("" "titling" t)
                                 ("" "grffile" t)
                                 ("" "extarrows" t)
                                 ("" "wrapfig" t)
                                 ("" "algorithm" t)
                                 ("" "algorithmic" t)
                                 ("" "lipsum" t)
                                 ("" "rotating" t)
                                 ("" "placeins" t)
                                 ("normalem" "ulem" t)
                                 ("" "amsmath" t)
                                 ("" "textcomp" t)
                                 ("" "svg" t)
                                 ("" "capt-of" t)))
(with-eval-after-load 'ox-latex
  (progn 
    (add-to-list 'org-latex-classes
                 (list "general"
                       "
  \\documentclass[english]{article}
  [NO-DEFAULT-PACKAGES]
  [PACKAGES]
  [EXTRA]
  \\usepackage{geometry}
  \\geometry{a4paper,left=2.5cm,top=2cm,right=2.5cm,bottom=2cm,marginparsep=7pt, marginparwidth=.6in}
  \\input{/publish/config/preamble.sty}
  "
                       '("\\section{%s}" . "\\section*{%s}")
                       '("\\subsection{%s}" . "\\subsection*{%s}")
                       '("\\subsubsection{%s}" . "\\subsubsection*{%s}")
                       '("\\paragraph{%s}" . "\\paragraph*{%s}")
                       '("\\subparagraph{%s}" . "\\subparagraph*{%s}")
                       ))
    (add-to-list 'org-latex-classes
                 (list "lectures"
                       "
  \\documentclass[oneside]{book}
  [NO-DEFAULT-PACKAGES]
  [PACKAGES]
  [EXTRA]
  \\addto\\captionsrussian{\\renewcommand{\\chaptername}{Лекция}}
  \\renewcommand{\\leftmark}{}
  \\usepackage[a4paper, total={6in, 8in}]{geometry}
  \\input{/publish/config/preamble.sty}
  \\fancyhead[L]{\\leftmark}
  "
                       '("\\chapter*{%1$s}\\renewcommand{\\leftmark}{%1$s}\\addcontentsline{toc}{chapter}{%1$s}\\stepcounter{chapter}" . "\\chapter{%s}")
                       '("\\section{%s}" . "\\section*{%s}")
                       '("\\subsection{%s}" . "\\subsection*{%s}")
                       '("\\subsubsection{%s}" . "\\subsubsection*{%s}")
                       '("\\paragraph{%s}" . "\\paragraph*{%s}")
                       '("\\subparagraph{%s}" . "\\subparagraph*{%s}")
                       ))))
(setq org-latex-listings 'minted
      org-latex-pdf-process
      '("pdflatex -shell-escape --synctex=1 -interaction nonstopmode -output-directory %o %f"
        "pdflatex -shell-escape --synctex=1 -interaction nonstopmode -output-directory %o %f"
        "pdflatex -shell-escape --synctex=1 -interaction nonstopmode -output-directory %o %f"))
(setq org-latex-minted-options
      '(("frame" "lines") ("linenos=true") ("mathescape")))
(add-to-list 'org-latex-minted-langs '(ipython "python"))

(defun my/org-publish (backend plist filename pub-dir)
  (with-temp-buffer 
    (insert-file-contents filename)
    (let
	((elem (org-element-context)))
      (if (and (eq 'keyword (org-element-type elem))
	       (string-equal "PUBNOTE" (org-element-property :key elem)))
	  (cond ((string-equal "ignore" (org-element-property :value elem))
		 (princ (concat filename " manually published")))
		((string-equal "html" (org-element-property :value elem))
		 (org-html-publish-to-html plist filename pub-dir)))
	(funcall backend plist filename pub-dir)))))

(defun my/org-html-publish-to-html (plist filename pub-dir)
  (my/org-publish 'org-html-publish-to-html plist filename pub-dir))
(defun my/org-latex-publish-to-pdf (plist filename pub-dir)
  (my/org-publish 'org-latex-publish-to-pdf plist filename pub-dir))

(setq org-publish-project-alist
      '(
        ("org-conspects"
         :base-directory "/publish/input"
         :exclude ".*[^E].org"
         :publishing-directory "/publish/output"
         :recursive t
         :html-postamble "<hr><a href=\"/public-notes/index.html\">Home Page</a><span style=\"float: right\"><a href=\"https://t.me/iliayar\"><i class=\"fab fa-telegram-plane\"></i></a> <a href=\"https://github.com/iliayar/ITMO\"><i class=\"fab fa-github\"></i></a></span><br><a href=\"/public-notes/conspects/README.html\">Conspects Home Page</a>"
         :publishing-function my/org-html-publish-to-html
         :headline-levels 4
         ) ("pdfs-conspects"
         :base-directory "/publish/input"
         :base-extension "org"
         :exclude "README.org\\|level-[0-9]*.org\\|level-subj.org"
         :publishing-directory "/publish/output"
         :recursive t
         :publishing-function my/org-latex-publish-to-pdf
         )
        ("conspects" :components ("org-conspects" "pdfs-conspects"))
        ))
