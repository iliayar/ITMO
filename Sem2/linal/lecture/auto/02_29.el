(TeX-add-style-hook
 "02_29"
 (lambda ()
   (TeX-add-to-alist 'LaTeX-provided-package-options
                     '(("inputenc" "utf8") ("babel" "russian")))
   (TeX-run-style-hooks
    "latex2e"
    "article"
    "art10"
    "inputenc"
    "babel"
    "amsmath"
    "amssymb"
    "latexsym"
    "amsthm"))
 :latex)

