;;; dyn-rx.el --- Dynamic Regular Expressions for Emacs Lisp

;; Copyright (C) from 2014 Thorsten Jolitz
;; Author: Thorsten Jolitz <tjolitz at gmail dot com>
;; Keywords: regular expressions, regexp

;; This file is not (yet) part of GNU Emacs.

;; GNU Emacs is free software: you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published
;; by the Free Software Foundation, either version 3 of the License,
;; or (at your option) any later version.

;; GNU Emacs is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs.  If not, see <http://www.gnu.org/licenses/>

;;; Commentary

;; This library implements functionality for easy writing of regular
;; expressions that are not hard-coded strings but rather function
;; calls that dynamically calculate the regexp using a few variables
;; that might be set to alter the final appearance of the regexp.

;;; Requires

(eval-when-compile (require 'cl))
(require 'org-macs)

;;; Variables
;;;; Vars

(defvar drx-BOL "^"
  "Special character that signals BOL in regexps.")

(defvar drx-EOL "$"
  "Special character that signals EOL in regexps.")

(defvar drx-STAR (regexp-quote "*")
  "Special character that signals headline(-level) in regexps.")

;;; Defuns
;;;; Functions

;;;;; Helper Functions

(defun drx-regexp-group-p (rgxp)
  "Return RGXP if its a regexp group, nil otherwise."
  (with-temp-buffer
    (insert (format "%S" rgxp))
    (goto-char (point-min))
    (if (ignore-errors
	  (save-excursion
	    (and
	     (re-search-forward "(")
	     (save-match-data
	       (looking-back
		(concat "^" (regexp-quote "\"\\\\("))
		(line-beginning-position)))
	     (goto-char (match-beginning 0))
	     (progn
	       (forward-sexp)
	       (looking-at
		"[*+]?[?]?\"$")))))
	rgxp nil)))
  

(defun drx-calc-quantifier (spec &optional default-quantifier)
  "Calculate a regexp quantifier based on SPEC.

Here are the possible types/formats of SPEC:

  - nil or "" or "  " :: don't repeat

  - N :: (number) repeat exactly N times

  - \"n,\" :: (string) repeat >= n times

  - \",m\" :: (string) repeat <= m times

  - \"n,m\" :: (string) repeat n to m times

  - other :: (any) DEFAULT-QUANTIFIER (or repeat >= 1 times)

See docstring of `drx-make' for more information."
  (let ((fallback (or default-quantifier "\\{1,\\}")))
    (cond
     ;; nil or empty string or white string
     ((or
       (not spec)
       (and (stringp spec) (string= spec ""))
       (and (stringp spec) (not (org-string-nw-p spec))))
      "") 
     ;; integer
     ((integerp spec)
      (if (eq spec 1) "" (format "\\{%d\\}" spec)))
     ;; non-white string
     ((org-string-nw-p spec)
      (let* ((spec-split (split-string spec ","))
	     (car-as-strg (car-safe spec-split))
	     (cadr-as-strg (car-safe (cdr-safe spec-split)))
	     (car-as-num (and (stringp car-as-strg)
			      (string-to-number car-as-strg)))
 	     (cadr-as-num (and (stringp cadr-as-strg)
			       (string-to-number cadr-as-strg))))
	(cond
	 ((and (eq (length spec-split) 2)
	       car-as-num cadr-as-num)
	  (cond
	   ;; "n,"
	   ((and (>= car-as-num 0)
		 (string= (cadr spec-split) ""))
	    (format "\\{%d,\\}" car-as-num))
	   ;; ",m"
	   ((and (string= (car spec-split) "")
		 (>= cadr-as-num 0))
	    (format "\\{,%d\\}" cadr-as-num))
	   ;; "n,m"
	   ((and (>= car-as-num 0) (>= cadr-as-num 0))
	    (format "\\{%d,%d\\}" car-as-num cadr-as-num))
	   ;; other
	   (t fallback)))
	 ((and (eq (length spec-split) 1)
	       (member car-as-strg
			'("*" "?" "+" "*?"  "+?" "??")))
		car-as-strg)
	 ;; other
	 (t fallback))))
     ;; other
     (t fallback))))


(defun drx-process-specs-list (specs rgxps)
  "Process SPECS list applying elements to RGXPS (list or string)."
  (let* ((length-diff (and (consp rgxps)
			   (- (length rgxps) (1- (length specs)))))
	 (specs-list (or
		      (and length-diff
			   (> length-diff 0)
			   (setcdr (last specs)
				   (make-list length-diff nil))
			   specs)
		      specs))
	 (zip-list (and (consp rgxps)
			(cons (pop specs-list)
			      (mapcar* 'cons rgxps specs-list))))
	 (lst (or zip-list specs-list)))
    (concat (if (car lst) "\\(" "")
	    (mapconcat
	     (lambda (--elem)
	       (let ((--quantifier
		      (or (cdr-safe --elem)
			  ;; (car-safe --elem)
			  --elem)))
		 (concat
		  (if (consp --quantifier) "\\(" "")
		  (or (car-safe (car-safe --elem)) rgxps)
		  (if (consp --quantifier) "\\)" "")
		  (cond
		   ((not --quantifier) "")
		   ((integerp --quantifier)
		    (drx-calc-quantifier --quantifier))
		   ((symbolp --quantifier) "*")
		   ((member --quantifier
			    '("*" "?" "+" "*?"  "+?" "??"))
		    --quantifier)
		   ((member --quantifier
			    '("0" "2" "3" "4" "5" "6" "7" "8"))
		    (concat "\\{" --quantifier "\\}"))
		   ((and (stringp --quantifier)
			 (string= --quantifier "1")) "")
		   (t (drx-calc-quantifier
		       (if (consp --quantifier)
			   (car-safe --quantifier)
			 --quantifier) ""))))))
	     (cdr-safe lst) "")
	    (cond
	     ((and (car lst) (symbolp (car lst))) "\\)")
	     ((member (car lst) '("*" "?" "+" "*?"  "+?" "??"))
	      (concat "\\)" (car lst)))
	     ((member (car lst)
		      '("0" "2" "3" "4" "5" "6" "7" "8"))
	      (concat "\\)\\{" (car lst) "\\}"))
	     ((string= (car lst) "1") "\\)")
	     (t (let ((quant (drx-calc-quantifier (car lst) "")))
		  (if (car lst)
		      (concat "\\)" quant)
		    quant)))))))

;;;;; Core Function

(defun drx (rgxp &optional bolp stars eolp enclosing &rest rgxps)
  "Make regexp from RGXP and optionally RGXPS.

With BOLP non-nil, add `drx-BOL' at beginning of regexp, with
EOLP non-nil add `drx-EOL' at end of regexp. 

STARS uses `drx-STAR' and repeats it depending on its value:

  - N :: (number) repeat N times

  - \"n,\" :: (string)  repeat >= n times

  - \",m\" :: (string)  repeat <= m times

  - \"n,m\" :: (string) repeat n to m times

  - (nil (elem1) elem2 (elem3)... elemN) :: (list of elems and
       sublists) match a group containing N elements, each of
       either one of the four forms above (number or string) or a
       list of length 1 itself with an integer, string or symbol
       in its car. Elements that are lists are wrapped in a
       subgroup.
       
       The first list element is special as well for the whole
       list as for each of its sublists and should be one of the
       following values (the first two have different meaning for
       the whole group and subgroups):
       
    - nil :: group not enclosed, subgroup enclosed without repeater

    - t :: (or any other symbol) group enclosed without repeater,
      subgroup enclosed with default repeater

    - \"?\" :: (sub)group enclosed with trailing ?

    - \"*\" :: (sub)group enclosed with trailing *

    - \"+\" :: (sub)group enclosed with trailing +

    - \"*?\" :: (sub)group enclosed with trailing *?

    - \"+?\" :: (sub)group enclosed with trailing +?

    - \"n,m\", \"n,\" or \",m\" :: (sub)group enclosed with
         trailing repeater {n,m}, {n,} or {,m}

  - other non-nil values :: (string or symbol) match >= 1 stars

When STARS is nil, do not add stars to regexp.

ENCLOSING might take the symbol values
 
  - alt :: Concat and enclose RGXP and RGXPS as regexp
           alternatives.  Eventually add drx-BOL/STARS and
           drx-EOL before first/after last alternative.

  - group :: Concat and enclose RGXP and RGXPS. Eventually add
             drx-BOL, STARS and drx-EOL as first/second/last
             group.

  - shy :: Concat and enclose RGXP and RGXPS as shy regexp
           groups. Eventually add drx-BOL, STARS and drx-EOL as
           first/second/last group.

  - append :: like 'group', but rather append RGXP and RGXPS
              instead of enclosing them if they are already
              regexp groups themselves.

  - append :: like 'group', but rather append RGXP and RGXPS
              instead of enclosing them if they are already
              regexp groups themselves.

  - (nil (elem1) elem2 (elem3)... elemN) :: (list of elems and
       sublists) Just like the STARS argument, but the elem specs
       are applied to elements of RGXPS instead to drx-STAR,
       i.e. elem1 is applied to regexp1 in RGXPS, elem2 to
       regexp2, ... elemN to regexpN.

  - other non-nil values :: Concat and enclose RGXP and RGXPS as
       one group. Eventually add drx-BOL, STARS and drx-EOL as
       first/second/last group.

When ENCLOSING is nil, simply concat RGXP and RGXPS and
eventually add drx-BOL, STARS and drx-EOL at the beginning/end of
resulting regexp."
  (let* ((star (if stars drx-STAR ""))
	 (quantifier
	  (cond
	   ((consp stars) (drx-process-specs-list stars star))
	   (stars (drx-calc-quantifier stars))
	   (t "")))
	 (star-and-quantifier (if (consp stars)
				  quantifier
				(concat star quantifier))))
    (case enclosing
      ('alt 
       (concat (if bolp drx-BOL "")
	       star-and-quantifier
	       "\\("
	       rgxp 
	       (if rgxps
		   (concat "\\|"
			   (replace-regexp-in-string
			    (concat (regexp-quote "\\|") "$") ""
			    (mapconcat 'identity rgxps "\\|")))
		 "")
	       "\\)"
	       (if eolp drx-EOL "")))
      ('group
       (concat (if bolp drx-BOL "")
	       star-and-quantifier
	       "\\(" rgxp "\\)"
	       (if rgxps
		   (mapconcat
		    (lambda (--rx) (concat "\\(" --rx "\\)"))
		    rgxps "")
		 "")
	       (if eolp drx-EOL "")))
      ('shy
       (concat (if bolp drx-BOL "")
	       star-and-quantifier
	       "\\(?:" rgxp "\\)"
	       (if rgxps
		   (mapconcat
		    (lambda (--rx) (concat "\\(?:" --rx "\\)"))
		    rgxps "")
		 "")
	       (if eolp drx-EOL "")))
      ('append
       (concat (if bolp drx-BOL "")
	       star-and-quantifier
	       (or (drx-regexp-group-p rgxp)
		   (concat "\\(" rgxp "\\)"))
	       (if rgxps
		   (mapconcat
		    (lambda (--rx)
		      (or (drx-regexp-group-p --rx)
			  (concat "\\(" --rx "\\)")))
		    rgxps "")
		 "")
	       (if eolp drx-EOL "")))
      (t (let ((processed-rgxps
		(cond
		 ((and rgxps (consp enclosing))
		  (drx-process-specs-list enclosing rgxps))
		 (rgxps (mapconcat 'identity rgxps ""))
		 (t ""))))
	   (concat (if bolp drx-BOL "")
		   star-and-quantifier
		   (cond
		    ((not enclosing) "")
		    ((consp enclosing)
		     (if (car-safe enclosing) "\\(" ""))
		    (t "\\("))
		   rgxp
		   (cond
		    ((not enclosing) "")
		    ((consp enclosing)
		     (if (car-safe enclosing) "\\)" ""))
		    ((eq enclosing 'alt) "\\|")
		    ((eq enclosing 'group) "\\)\\(")
		    (t "\\)"))
		   processed-rgxps
		   (cond
		    ((not enclosing) "")
		    ((consp enclosing)
		     (if (memq (car-safe enclosing) '(alt group))
		       "\\)" ""))
		    (t ""))
		   (if eolp drx-EOL "")))))))

;;; Tests

(ert-deftest drx-test ()
  "Test return values of function `drx'.
Assumes the following variable definitions:

 (defvar drx-BOL \"^\"
   \"Special character that signals BOL in regexps.\")

 (defvar drx-EOL \"$\"
   \"Special character that signals EOL in regexps.\")

 (defvar drx-STAR (regexp-quote \"*\")
   \"Special character that signals headline(-level) in regexps.\")"
  ;; return identity
  (should (equal
	   (drx "foo")
	   "foo"))
  ;; add drx-BOL
  (should (equal
	   (drx "foo" t)
	   "^foo"))
  ;; append drx-EOL
  (should (equal
	   (drx "foo" nil nil t)
	   "foo$"))
  ;; add drx-BOL and append drx-EOL
  (should (equal
	   (drx "foo" t nil t)
	   "^foo$"))
  ;; add drx-BOL and append drx-EOL
  ;; and add drx-STAR with default quantifier
  (should (equal
	   (drx "foo" t t t)
	   "^\\*\\{1,\\}foo$"))
  (should (equal
	   (drx "foo" t 'bar t)
	   "^\\*\\{1,\\}foo$"))
  (should (equal
	   (drx "foo" t "bar" t)
	   "^\\*\\{1,\\}foo$"))
  ;; add drx-BOL and append drx-EOL
  ;; and add drx-STAR with specified quantifiers
  (should (equal
	   (drx "foo" t "0," t)
	   "^\\*\\{0,\\}foo$"))
  (should (equal
	   (drx "foo" t ",8" t)
	   "^\\*\\{,8\\}foo$"))
  (should (equal
	   (drx "foo" t "1,8" t)
	   "^\\*\\{1,8\\}foo$"))
  (should (equal
	   (drx "foo" t "*" t)
	   "^\\**foo$"))
  (should (equal
	   (drx "foo" t "+" t)
	   "^\\*+foo$"))
  (should (equal
	   (drx "foo" t "?" t)
	   "^\\*?foo$"))
  (should (equal
	   (drx "foo" t "*?" t)
	   "^\\**?foo$"))
  (should (equal
	   (drx "foo" t "+?" t)
	   "^\\*+?foo$"))
  (should (equal
	   (drx "foo" t "??" t)
	   "^\\*??foo$"))
  ;; add drx-STAR with specified quantifier list
  (should (equal
	   (drx "foo" nil '(nil) nil)
	   "foo"))
  (should (equal
	   (drx "foo" nil '(t) nil)
	   "\\(\\)foo"))
  (should (equal
	   (drx "foo" nil '(t nil) nil)
	   "\\(\\*\\)foo"))
  (should (equal
	   (drx "foo" nil '(t 1) nil)
	   "\\(\\*\\)foo"))
  (should (equal
	   (drx "foo" nil '(t t) nil)
	   "\\(\\**\\)foo"))
  (should (equal
	   (drx "foo" nil '(nil "+") nil)
	   "\\*+foo"))
  (should (equal
	   (drx "foo" nil '(nil "*") nil)
	   "\\**foo"))
  (should (equal
	   (drx "foo" nil '(nil "?") nil)
	   "\\*?foo"))
  (should (equal
	   (drx "foo" nil '(nil "+?") nil)
	   "\\*+?foo"))
  (should (equal
	   (drx "foo" nil '(nil "*?") nil)
	   "\\**?foo"))
  (should (equal
	   (drx "foo" nil '(nil "??") nil)
	   "\\*??foo"))
  (should (equal
	   (drx "foo" nil '(nil "1,") nil)
	   "\\*\\{1,\\}foo"))
  (should (equal
  	   (drx "foo" nil '(nil ("1,")) nil)
  	   "\\(\\*\\)\\{1,\\}foo"))
  (should (equal
	   (drx "foo" nil '(nil ",2") nil)
	   "\\*\\{,2\\}foo"))
  (should (equal
	   (drx "foo" nil '(nil (",2")) nil)
	   "\\(\\*\\)\\{,2\\}foo"))
  (should (equal
	   (drx "foo" nil '(nil "1,2") nil)
	   "\\*\\{1,2\\}foo"))
  (should (equal
	   (drx "foo" nil '(nil ("1,2")) nil)
	   "\\(\\*\\)\\{1,2\\}foo"))
  (should (equal
  	   (drx "foo" nil '(nil (2)) nil)
  	   "\\(\\*\\)\\{2\\}foo"))
  (should (equal
  	   (drx "foo" nil '(nil 2) nil)
  	   "\\*\\{2\\}foo"))
  (should (equal
  	   (drx "foo" nil '(nil (1)) nil)
  	   "\\(\\*\\)foo"))
  (should (equal
	   (drx "foo" nil '(nil 1) nil)
	   "\\*foo"))
  (should (equal
  	   (drx "foo" nil '(nil 2 ("2,3") "3") nil)
  	   "\\*\\{2\\}\\(\\*\\)\\{2,3\\}\\*\\{3\\}foo"))
  (should (equal
  	   (drx "foo" nil '(",3" (2) ("2,3") 3) nil)
  	   "\\(\\(\\*\\)\\{2\\}\\(\\*\\)\\{2,3\\}\\*\\{3\\}\\\)\\{,3\\}foo"))
  ;; temporarily change BOL and EOL e.g. using CSS comment syntax
  (should (equal
	   (let ((drx-BOL (concat "^" (regexp-quote "/* ")))
		 (drx-EOL (concat (regexp-quote "*/") "$")))
	     (drx "foo" t nil t))
	   "^/\\* foo\\*/$"))
  ;; temporarily change STAR using Elisp syntax
  (should (equal
	   (let ((drx-STAR ";"))
	     (drx " foo" nil 2))
	   ";\\{2\\} foo"))
  (should (equal
	   (let ((drx-BOL "^;;")
		 (drx-STAR ";"))
	     (drx " foo" t '(2 2) nil))
	   "^;;\\(;\\{2\\}\\)\\{2\\} foo"))
  ;; temporarily change STAR to whitespace syntax
  (should (equal
  	   (let ((drx-STAR "[ \t]"))
  	     (drx " foo" t "*"))
  	   "^[ 	]* foo"))
  ;; enclose rgxp
  (should (equal
	   (drx "foo" nil nil nil t)
	   "\\(foo\\)"))
  (should (equal
	   (drx "foo" t t t t)
	   "^\\*\\{1,\\}\\(foo\\)$"))
  (should (equal
	   (drx "foo" nil nil nil t)
	   "\\(foo\\)"))
  (should (equal
	   (drx "foo" nil nil nil t)
	   "\\(foo\\)"))

  
  
)

;;; Provide

(provide 'dyn-rx)

;;; dyn-rx.el ends here
