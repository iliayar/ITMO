(require 'package)
(add-to-list
 'package-archives
 '("melpa" . "https://melpa.org/packages/")
 t)

(package-initialize)

(unless (package-installed-p 'use-package)
  (package-refresh-contents)
  (package-install 'use-package))

(add-to-list 'load-path "/publish/config/lisp/")

(use-package haskell-mode
  :ensure t)
(use-package htmlize
  :ensure t)
