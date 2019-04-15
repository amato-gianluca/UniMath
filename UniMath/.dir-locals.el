
((coq-mode
  . ((eval .
	   (let ((unimath-topdir (expand-file-name (locate-dominating-file buffer-file-name "UniMath"))))
	     (setq fill-column 100)
	     (make-local-variable 'coq-use-project-file)
	     (setq coq-use-project-file nil)
	     (make-local-variable 'coq-prog-args)
	     (setq coq-prog-args
		   ;; these options should match what's used in ../Makefile
		   `("-emacs" "-noinit" "-indices-matter" "-type-in-type" "-w" "-notation-overridden" "-Q" ,(concat unimath-topdir "UniMath") "UniMath" )
		   )
	     (make-local-variable 'coq-prog-name)
	     (setq coq-prog-name (concat unimath-topdir "sub/coq/bin/coqtop"))
	     (make-local-variable 'coq-load-path)
	     (setq coq-load-path `((recnoimport ,(concat unimath-topdir "UniMath") "UniMath")))
	     (make-local-variable 'before-save-hook)
	     (add-hook 'before-save-hook 'delete-trailing-whitespace)
	     (if (and (file-exists-p (concat unimath-topdir "TAGS")) (functionp 'visit-tags-table))
		 (visit-tags-table (concat unimath-topdir "TAGS")))
	     (modify-syntax-entry ?' "w")
	     (modify-syntax-entry ?_ "w")
	     (if (not (memq 'agda-input features))
		 (load (concat unimath-topdir "emacs/agda/agda-input")))
	     (if (not (member '("chimney" "╝") agda-input-user-translations))
		 (progn
		   (setq agda-input-user-translations (cons '("chimney" "╝") agda-input-user-translations))
		   (setq agda-input-user-translations (cons '("==>" "⟹") agda-input-user-translations))
		   (agda-input-setup)))
	     (set-input-method "Agda"))))))
