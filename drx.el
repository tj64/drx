;;; drx.el --- declarative dynamic regular expressions

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

;; This library implements functionality for writing dynamic regular
;; expressions for Emacs Lisp in a declarative style.

;; 'Dynamic' means that regexps are not (entirely) hard-coded
;; strings anymore but rather function calls and thus dynamically
;; calculated at run-time.

;; 'Declarative' means that most of the grouping, enclosing and
;; repeating boiler-plate syntax is not explicitly written down
;; anymore but rather declared with minimal specifiers via function
;; arguments.

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
  "Calculate quantifier based on SPEC and DEFAULT-QUANTIFIER.
See docstring of `drx' for more information."
  (let ((fallback (or default-quantifier "")))
    (cond
     ;; nil or empty string or white string
     ((or
       (booleanp spec)
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
	 ;; "*", "+", "?", ..., "??"
	 ((and (eq (length spec-split) 1)
	       (member car-as-strg '("*" "?" "+" "*?"  "+?" "??")))
	  car-as-strg)
	 ;; "<<number>>"
	 ((and car-as-strg
	       (save-match-data
		 (string-match "^[[:digit:]]+$" car-as-strg)))
	  (if (eq (string-to-number car-as-strg) 1)
	      "" (concat "\\{" car-as-strg "\\}")))
	 ;; other
	 (t fallback))))
     ;; other
     (t fallback))))

(defun drx-process-specs-list (specs rgxps)
  "Process SPECS list applying elements to RGXPS (list or string).

SPECS is a list with elements of the format described in the
docstring of `drx-calc-quantifier'. RGXPS is either a list of
regexp arguments (more exactly the &rest args given to function
`drx') or a single regexp string, i.e. the current value of
variable `drx-STAR', which could be e.g. the asteriks signalling
headlines in Org-mode (\"\\*\") or a regexp that matches optional
whitespace (\"[ \t]*\"). 

This functions works by either applying each spec1 ... specN in
SPECS independently to the same single regexp in RGXPS and
concatenating the N results, or by first making sure the SPECS
list is at least as long as the RGXPS list (by appending nil
elements if necessary) and then applying spec1 from SPECS to
rgxp1 from RGXPS, spec2 from SPECS to rgxp2 from RGXPS, ...,
specN from SPECS to rgxpN from RGXPS, and concatenating the
results."
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
    (concat (if (and (not zip-list) (car lst)) "\\(" "")
	    (mapconcat
	     (lambda (--elem)
	       (let ((--quantifier
		      (if zip-list (cdr-safe --elem) --elem)))
		 (concat
		  ;; (if  --quantifier "\\(" "")
		  (if (and --quantifier
		  	   (or (symbolp --quantifier)
		  	       (consp --quantifier)))
		      "\\(" "")
		  (if zip-list
		      (or (car-safe (car-safe --elem))
			  (car-safe --elem))
		    rgxps)
		  ;; (if  --quantifier "\\)" "")
		  (if (and --quantifier
		  	   (or (symbolp --quantifier)
		  	       (consp --quantifier)))
		      "\\)" "")
		  (cond
		   ((or (not --quantifier)
			(symbolp --quantifier)
			(and (stringp --quantifier)
			     (string= --quantifier "1"))) "")
		   ((integerp --quantifier)
		    (drx-calc-quantifier --quantifier))
		   ;; ((symbolp --quantifier) "*")
		   ((member --quantifier
			    '("*" "?" "+" "*?"  "+?" "??"))
		    --quantifier)
		   ((and (stringp --quantifier)
			 (save-match-data
			   (string-match "^[[:digit:]]+$"
					 --quantifier)))
		    (concat "\\{" --quantifier "\\}"))
		   (t (drx-calc-quantifier
		       (if (consp --quantifier)
			   (car-safe --quantifier)
			 --quantifier) ""))))))
	     (cdr-safe lst) "")
	    (unless zip-list
	      (cond
	       ((and (car lst) (symbolp (car lst))) "\\)")
	       ((member (car lst) '("*" "?" "+" "*?"  "+?" "??"))
		(concat "\\)" (car lst)))
	       ((member (car lst)
			'("0" "2" "3" "4" "5" "6" "7" "8"))
		(concat "\\)\\{" (car lst) "\\}"))
	       ((and (stringp (car lst)) (string= (car lst) "1"))
		"\\)")
	       (t (let ((quant (drx-calc-quantifier (car lst) "")))
		    (if (car lst)
			(concat "\\)" quant)
		      quant))))))))

;;;;; Core Function

(defun drx (rgxp &optional bolp stars eolp enclosing &rest rgxps)
  "Make regexp combining RGXP and optional RGXPS.

With BOLP non-nil, add 'drx-BOL' at beginning of regexp, with EOLP
non-nil add 'drx-EOL' at end of regexp.

STARS, when non-nil, uses 'drx-STAR' and encloses and repeats it.

ENCLOSING, when non-nil, takes RGXP and optional RGXPS and combines,
encloses and repeats them.

While BOLP and EOLP are switches that don't do nothing when nil and
insert whatever value 'drx-BOL' and 'drx-EOL' are set to when
non-nil, both arguments STARS and ENCLOSING take either symbols,
numbers, strings or (nested) lists as values and act conditional on
the type.

All the following 'atomic' argument values are valid for both STARS
and ENCLOSING but with a slightly different meaning:

STARS: repeat 'drx-STAR' (without enclosing) conditional on argument
value

ENCLOSING: repeat enclosed combination of RGXP and RGXPS conditional
on argument value

  - nil :: do nothing (no repeater, no enclosing)

  - t :: (and any other symbol w/o special meaning) repeat once

  - n :: (number) repeat n times {n}

  - \"n\" :: (number-as-string) repeat n times {n}

  - \"n,\" :: (string) repeat >= n times {n,}

  - \",m\" :: (string) repeat <= m times {,m}

  - \"n,m\" :: (string) repeat n to m times {n,m}
       
  - \"?\" :: (string) repeat with ?

  - \"*\" :: (string) repeat with *

  - \"+\" :: (string) repeat with +

  - \"??\" :: (string) repeat with ??

  - \"*?\" :: (string) repeat with *?

  - \"+?\" :: (string) repeat with +?

  - \"xyz\" :: (any other string) repeat once

Note that, when used with STARS and ENCLOSING, t almost always
means 'enclose and repeat once', while 1 and \"1\" stand for
'do not enclose, repeat once' - depending on the context.

These atomic values can be wrapped in a list and change their
meaning then. In a list of length 1 they specify 'enclose element
first, apply repeater then'. In a list of lenght > 1 the specifier
in the car applies to the combination of all elements, while each of
the specifiers in the cdr applies to one element only. In the case
of argument STAR, an element is always 'drx-STAR'. In the case of
argument ENCLOSING, a non-nil optional argument RGXPS represents the
list of elements, each of them being a regexp string.

Here are two calls of 'drx' with interchanged list arguments to
STARS and ENCLOSING and their return values, demonstrating the
above:

  ,------------------------------------------------------------
  | (drx \"foo\" t '(nil t (2)) t '(t nil (2))
  |      \"bar\" \"loo\")
  | \"^\\(\\*\\)\\(\\*\\)\\{2\\}\\(foobar\\(loo\\)\\{2\\}\\)$\"
  `------------------------------------------------------------

  ,------------------------------------------------------------
  | (drx \"foo\" t '(t nil (2)) t '(nil t (2))
  |       \"bar\" \"loo\")
  | \"^\\(\\*\\(\\*\\)\\{2\\}\\)foo\\(bar\\)\\(loo\\)\\{2\\}$\"
  `------------------------------------------------------------

Many more usage examples with their expected outcome can be found as
ERT tests in the test-section of drx.el and should be consulted in
doubt.

There are a few symbols with special meaning as values of the
ENCLOSING argument (when used as atomic argument or as car of a list
argument), namely:
 
  - alt :: Concat and enclose RGXP and RGXPS as regexp alternatives.
           Eventually add drx-BOL/STARS and drx-EOL before
           first/after last alternative.

  - grp :: Concat and enclose RGXP and RGXPS. Eventually add
             drx-BOL, STARS and drx-EOL as first/second/last group.

  - shy :: Concat and enclose RGXP and RGXPS as shy regexp
           groups. Eventually add drx-BOL, STARS and drx-EOL as
           first/second/last group.

  - app :: like 'grp', but rather append RGXP and RGXPS instead
              of enclosing them if they are already regexp groups
              themselves.

They create regexp groups but don't apply repeaters to them."
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
      ;; make regexp alternatives
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
      ;; make regexp groups
      ('grp
       (concat (if bolp drx-BOL "")
	       star-and-quantifier
	       "\\(" rgxp "\\)"
	       (if rgxps
		   (mapconcat
		    (lambda (--rx) (concat "\\(" --rx "\\)"))
		    rgxps "")
		 "")
	       (if eolp drx-EOL "")))
      ;; make shy regexp groups
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
      ;; make regexp groups appending elements that are groups
      ;; themselves (do not enclose them again)
      ('app
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
      ;; others
      (t (let ((preprocessed-rgxps
		(cond
		 ;; RGXPS, ENCLOSING is list 
		 ((and rgxps (consp enclosing))
		  (drx-process-specs-list enclosing rgxps))
		 ;; RGXPS
		 (rgxps (mapconcat 'identity rgxps ""))
		 ;; not RGXPS
		 (t ""))))
	   (concat
	    ;; BOL
	    (if bolp drx-BOL "")
	    ;; STARS
	    star-and-quantifier
	    ;; enclose RGXP
	    (cond
	     ;; no ENCLOSING
	     ((not enclosing) "")
	     ;; ENCLOSING is list
	     ((consp enclosing)
	      (let ((--grp (car-safe enclosing)))
		(cond
		 ;; car matches "?:" and "?num:"
		 ((and (org-string-nw-p --grp)
		       (save-match-data
			 (string-match
			  "\\?[[:digit:]]*:" --grp))) 
		  (concat "\\(" --grp))
		 ;; car is non-nil
		 (--grp "\\(")
		 ;; else
		 (t ""))))
	     (t "\\("))
	    ;; RGXP
	    rgxp
	    ;; no RGXPS => enclose RGXP
	    (if (not (org-string-nw-p preprocessed-rgxps))
		(cond
		 ;; no ENCLOSING
		 ((not enclosing) "")
		 ;; ENCLOSING is integer
		 ((integerp enclosing)
		  (if (eq enclosing 1)
		      ;; int=1
		      "\\)"
		    ;; else
		    (concat "\\)\\{"
			    (number-to-string enclosing)
			    "\\}")))
		 ;; ENCLOSING is non-white string
		 ((org-string-nw-p enclosing)
		  (concat "\\)"
			  (drx-calc-quantifier
			   enclosing "")))
		 ;; ENCLOSING is list
		 ((consp enclosing)
		  (let ((--quant
			 (car-safe (cdr-safe enclosing))))
		    (cond
		     ;; cdr is integer
		     ((integerp --quant)
		      (if (eq --quant 1)
			  ;; int=1
			  "\\)"
			;; else
			(concat "\\)\\{"
				(number-to-string --quant)
				"\\}"))
		      ;; cdr is non-white string
		      ((org-string-nw-p --quant)
		       (concat "\\)"
			       (drx-calc-quantifier
				--quant "")))
		      ;; else
		      (t "\\)")))))
		 ;; else
		 (t "\\)")) "")
	    ;; RGXPS
	    preprocessed-rgxps
	    ;; => enclose combined RGXP and RGXPS 
	    (if (org-string-nw-p preprocessed-rgxps)
		(cond
		 ;; no ENCLOSING
		 ((not enclosing) "")
		 ;; ENCLOSING is integer
		 ((integerp enclosing)
		  (if (eq enclosing 1)
		      ;; int=1
		      "\\)"
		    ;; else
		    (concat "\\)\\{"
			    (number-to-string enclosing)
			    "\\}")))
		 ;; ENCLOSING is non-white string 
		 ((org-string-nw-p enclosing)
		  (concat "\\)"
			  (drx-calc-quantifier
			   enclosing "")))
		 ;; ENCLOSING is list
		 ((consp enclosing)
		  (if (car-safe enclosing) "\\)" ""))
		 (t "\\)")) "")
	    ;; EOL
	    (if eolp drx-EOL "")))))))

;;;; Commands

;;; Tests

;;;; Convenience Functions

(defun drx-get-preceeding-test-number ()
  "Return number of preceeding test or 0."
  (save-excursion
      (if (re-search-backward
	      (concat
	       "\\(^\(ert-deftest drx-test-\\)"
	       "\\([[:digit:]]+\\)"
	       "\\( ()$\\)") (point-min) 'NOERROR)
	  (string-to-number (match-string 2)) 0)))
	  
;; fixme
(defun drx-change-ert-test-numbers (&optional op step beg end)
  "Change test-number with OP by STEP for next tests or in BEG END."
  (let ((incop (or op '+))
	(incstep (or step 1))
	(maxpos (or end (point-max))))
    (save-excursion
      (when beg (goto-char beg))
      (while (re-search-forward
	      (concat
	       "\\(^\(ert-deftest drx-test-\\)"
	       "\\([[:digit:]]+\\)"
	       "\\( ()$\\)") maxpos 'NOERROR)
	(replace-match
	  (eval
	   `(number-to-string
	     (,incop (string-to-number (match-string 2))
		     ,incstep)))
	   nil nil nil 2)))))


(defun drx-insert-ert-test-and-renumber ()
  "Insert ert-test template at point.
Make test number 1 or (1+ number of preceeding test). Increase
test number of all following tests by 1."
  (interactive)
  (insert
   (format "%s%d%s\n%S\n%s\n%s\n%S%s\n"
	   '\(ert-deftest\ drx-test-
	   (1+ (drx-get-preceeding-test-number))
	   '\ \(\)
	   "See docstring of `drx-test-1'."
	   '\(should\ \(equal
	   '(drx \"foo\")
	   "foo"
	   '\)\)\)))
  (indent-region (save-excursion (backward-sexp) (point)) (point))
  (drx-change-ert-test-numbers))

;;;; ERT Tests

;; return identity
(ert-deftest drx-test-1 ()
  "Test return values of function `drx'.
Assumes the following variable definitions:

 (defvar drx-BOL \"^\"
   \"Special character that signals BOL in regexps.\")

 (defvar drx-EOL \"$\"
   \"Special character that signals EOL in regexps.\")

 (defvar drx-STAR (regexp-quote \"*\")
   \"Special character that signals headline(-level) in regexps.\")"
  (should (equal
	   (drx "foo")
	   "foo")))

;; add drx-BOL
(ert-deftest drx-test-2 ()
  "See docstring of `drx-test-1'."
  (should (equal
	   (drx "foo" t)
	   "^foo")))

;; append drx-EOL
(ert-deftest drx-test-3 ()
  "See docstring of `drx-test-1'."
  (should (equal
	   (drx "foo" nil nil t)
	   "foo$")))

;; add drx-BOL and append drx-EOL
(ert-deftest drx-test-4 ()
  "See docstring of `drx-test-1'."
  (should (equal
	   (drx "foo" t nil t)
	   "^foo$")))

;; add drx-BOL and append drx-EOL
;; and add drx-STAR with default quantifier
(ert-deftest drx-test-5 ()
  "See docstring of `drx-test-1'."
  (should (equal
	   (drx "foo" t t t)
	   "^\\*foo$")))

(ert-deftest drx-test-6 ()
  "See docstring of `drx-test-1'."
  (should (equal
	   (drx "foo" t 'bar t)
	   "^\\*foo$")))

(ert-deftest drx-test-7 ()
  "See docstring of `drx-test-1'."
  (should (equal
	   (drx "foo" t "bar" t)
	   "^\\*foo$")))

;; add drx-BOL and append drx-EOL
;; and add drx-STAR with specified quantifiers
(ert-deftest drx-test-8 ()
  "See docstring of `drx-test-1'."
  (should (equal
	   (drx "foo" t "0," t)
	   "^\\*\\{0,\\}foo$")))

(ert-deftest drx-test-9 ()
  "See docstring of `drx-test-1'."
  (should (equal
	   (drx "foo" t ",8" t)
	   "^\\*\\{,8\\}foo$")))

(ert-deftest drx-test-10 ()
  "See docstring of `drx-test-1'."
  (should (equal
	   (drx "foo" t "1,8" t)
	   "^\\*\\{1,8\\}foo$")))

(ert-deftest drx-test-11 ()
  "See docstring of `drx-test-1'."
  (should (equal
	   (drx "foo" t "*" t)
	   "^\\**foo$")))

(ert-deftest drx-test-12 ()
  "See docstring of `drx-test-1'."
  (should (equal
	   (drx "foo" t "+" t)
	   "^\\*+foo$")))

(ert-deftest drx-test-13 ()
  "See docstring of `drx-test-1'."
  (should (equal
	   (drx "foo" t "?" t)
	   "^\\*?foo$")))

(ert-deftest drx-test-14 ()
  "See docstring of `drx-test-1'."
  (should (equal
	   (drx "foo" t "*?" t)
	   "^\\**?foo$")))

(ert-deftest drx-test-15 ()
  "See docstring of `drx-test-1'."
  (should (equal
	   (drx "foo" t "+?" t)
	   "^\\*+?foo$")))

;; add drx-STAR with specified quantifier list
(ert-deftest drx-test-16 ()
  "See docstring of `drx-test-1'."
  (should (equal
	   (drx "foo" t "??" t)
	   "^\\*??foo$")))

(ert-deftest drx-test-17 ()
  "See docstring of `drx-test-1'."
  (should (equal
	   (drx "foo" nil '(nil) nil)
	   "foo")))

(ert-deftest drx-test-18 ()
  "See docstring of `drx-test-1'."
  (should (equal
	   (drx "foo" nil '(t) nil)
	   "\\(\\)foo")))

(ert-deftest drx-test-19 ()
  "See docstring of `drx-test-1'."
  (should (equal
  	   (drx "foo" nil '(t nil) nil)
  	   "\\(\\*\\)foo")))

(ert-deftest drx-test-20 ()
  "See docstring of `drx-test-1'."
  (should (equal
  	   (drx "foo" nil '(t 1) nil)
  	   "\\(\\*\\)foo")))

(ert-deftest drx-test-21 ()
  "See docstring of `drx-test-1'."
  (should (equal
	   (drx "foo" nil '(t t) nil)
	   "\\(\\(\\*\\)\\)foo")))

(ert-deftest drx-test-22 ()
  "See docstring of `drx-test-1'."
  (should (equal
	   (drx "foo" nil '((t) t) nil)
	   "\\(\\(\\*\\)\\)foo")))

(ert-deftest drx-test-23 ()
  "See docstring of `drx-test-1'."
  (should (equal
	   (drx "foo" nil '((t) nil) nil)
	   "\\(\\*\\)foo")))

(ert-deftest drx-test-24 ()
  "See docstring of `drx-test-1'."
  (should (equal
	   (drx "foo" nil '("2,4" t) nil)
	   "\\(\\(\\*\\)\\)\\{2,4\\}foo")))

(ert-deftest drx-test-25 ()
  "See docstring of `drx-test-1'."
  (should (equal
	   (drx "foo" nil '("2,4" nil) nil)
	   "\\(\\*\\)\\{2,4\\}foo")))

(ert-deftest drx-test-26 ()
  "See docstring of `drx-test-1'."
  (should (equal
	   (drx "foo" nil '(("2,4") t) nil)
	   "\\(\\(\\*\\)\\)foo")))

(ert-deftest drx-test-27 ()
  "See docstring of `drx-test-1'."
  (should (equal
	   (drx "foo" nil '(("2,4") nil) nil)
	   "\\(\\*\\)foo")))

(ert-deftest drx-test-28 ()
  "See docstring of `drx-test-1'."
  (should (equal
	   (drx "foo" nil '(nil "+") nil)
	   "\\*+foo")))

(ert-deftest drx-test-29 ()
  "See docstring of `drx-test-1'."
  (should (equal
	   (drx "foo" nil '(nil "*") nil)
	   "\\**foo")))

(ert-deftest drx-test-30 ()
  "See docstring of `drx-test-1'."
  (should (equal
	   (drx "foo" nil '(nil "?") nil)
	   "\\*?foo")))

(ert-deftest drx-test-31 ()
  "See docstring of `drx-test-1'."
  (should (equal
	   (drx "foo" nil '(nil "+?") nil)
	   "\\*+?foo")))

(ert-deftest drx-test-32 ()
  "See docstring of `drx-test-1'."
  (should (equal
	   (drx "foo" nil '(nil "*?") nil)
	   "\\**?foo")))

(ert-deftest drx-test-33 ()
  "See docstring of `drx-test-1'."
  (should (equal
	   (drx "foo" nil '(nil "??") nil)
	   "\\*??foo")))

(ert-deftest drx-test-34 ()
  "See docstring of `drx-test-1'."
  (should (equal
	   (drx "foo" nil '(nil "1,") nil)
	   "\\*\\{1,\\}foo")))

(ert-deftest drx-test-35 ()
  "See docstring of `drx-test-1'."
  (should (equal
  	   (drx "foo" nil '(nil ("1,")) nil)
  	   "\\(\\*\\)\\{1,\\}foo")))

(ert-deftest drx-test-36 ()
  "See docstring of `drx-test-1'."
  (should (equal
	   (drx "foo" nil '(nil ",2") nil)
	   "\\*\\{,2\\}foo")))

(ert-deftest drx-test-37 ()
  "See docstring of `drx-test-1'."
  (should (equal
	   (drx "foo" nil '(nil (",2")) nil)
	   "\\(\\*\\)\\{,2\\}foo")))

(ert-deftest drx-test-38 ()
  "See docstring of `drx-test-1'."
  (should (equal
	   (drx "foo" nil '(nil "1,2") nil)
	   "\\*\\{1,2\\}foo")))

(ert-deftest drx-test-39 ()
  "See docstring of `drx-test-1'."
  (should (equal
	   (drx "foo" nil '(nil ("1,2")) nil)
	   "\\(\\*\\)\\{1,2\\}foo")))

(ert-deftest drx-test-40 ()
  "See docstring of `drx-test-1'."
  (should (equal
  	   (drx "foo" nil '(nil (2)) nil)
  	   "\\(\\*\\)\\{2\\}foo")))

(ert-deftest drx-test-41 ()
  "See docstring of `drx-test-1'."
  (should (equal
  	   (drx "foo" nil '(nil 2) nil)
  	   "\\*\\{2\\}foo")))

(ert-deftest drx-test-42 ()
  "See docstring of `drx-test-1'."
  (should (equal
  	   (drx "foo" nil '(nil (1)) nil)
  	   "\\(\\*\\)foo")))

(ert-deftest drx-test-43 ()
  "See docstring of `drx-test-1'."
  (should (equal
	   (drx "foo" nil '(nil 1) nil)
	   "\\*foo")))

(ert-deftest drx-test-44 ()
  "See docstring of `drx-test-1'."
  (should (equal
  	   (drx "foo" nil '(nil 2 ("2,3") "3") nil)
  	   "\\*\\{2\\}\\(\\*\\)\\{2,3\\}\\*\\{3\\}foo")))

(ert-deftest drx-test-45 ()
  "See docstring of `drx-test-1'."
  (should (equal
  	   (drx "foo" nil '(",3" (2) ("2,3") 3) nil)
  	   "\\(\\(\\*\\)\\{2\\}\\(\\*\\)\\{2,3\\}\\*\\{3\\}\\\)\\{,3\\}foo")))

;; temporarily change BOL and EOL e.g. using CSS comment syntax
(ert-deftest drx-test-46 ()
  "See docstring of `drx-test-1'."
  (should (equal
	   (let ((drx-BOL (concat "^" (regexp-quote "/* ")))
		 (drx-EOL (concat (regexp-quote "*/") "$")))
	     (drx "foo" t nil t))
	   "^/\\* foo\\*/$")))

;; temporarily change STAR using Elisp syntax
(ert-deftest drx-test-47 ()
  "See docstring of `drx-test-1'."
  (should (equal
	   (let ((drx-STAR ";"))
	     (drx " foo" nil 2))
	   ";\\{2\\} foo")))

(ert-deftest drx-test-48 ()
  "See docstring of `drx-test-1'."
  (should (equal
	   (let ((drx-BOL "^;;")
		 (drx-STAR ";"))
	     (drx " foo" t '(2 2) nil))
	   "^;;\\(;\\{2\\}\\)\\{2\\} foo")))

;; temporarily change STAR to whitespace syntax
(ert-deftest drx-test-49 ()
  "See docstring of `drx-test-1'."
  (should (equal
  	   (let ((drx-STAR "[ \t]"))
  	     (drx " foo" t "*"))
  	   "^[ 	]* foo")))

;; enclose rgxp
(ert-deftest drx-test-50 ()
  "See docstring of `drx-test-1'."
  (should (equal
	   (drx "foo" nil nil nil t)
	   "\\(foo\\)")))

(ert-deftest drx-test-51 ()
  "See docstring of `drx-test-1'."
  (should (equal
	   (drx "foo" t t t t)
	   "^\\*\\(foo\\)$")))

(ert-deftest drx-test-52 ()
  "See docstring of `drx-test-1'."
  (should (equal
	   (drx "foo" nil nil nil 'alt "bar")
	   "\\(foo\\|bar\\)")))

(ert-deftest drx-test-53 ()
  "See docstring of `drx-test-1'."
  (should (equal
	   (drx "foo" nil nil nil 'grp "bar")
	   "\\(foo\\)\\(bar\\)")))

(ert-deftest drx-test-54 ()
  "See docstring of `drx-test-1'."
  (should (equal
	   (drx "foo" nil nil nil 'shy "bar")
	   "\\(?:foo\\)\\(?:bar\\)")))

(ert-deftest drx-test-55 ()
  "See docstring of `drx-test-1'."
  (should (equal
	   (drx "foo" nil nil nil 'app "bar")
	   "\\(foo\\)\\(bar\\)")))

(ert-deftest drx-test-56 ()
  "See docstring of `drx-test-1'."
  (should (equal
	   (drx "foo" nil nil nil 'app "\\(bar\\)")
	   "\\(foo\\)\\(bar\\)")))

(ert-deftest drx-test-57 ()
  "See docstring of `drx-test-1'."
  (should (equal
	   (drx "foo" nil nil nil 'grp "\\(bar\\)")
	   "\\(foo\\)\\(\\(bar\\)\\)")))

(ert-deftest drx-test-58 ()
  "See docstring of `drx-test-1'."
  (should (equal
  	   (drx "foo" nil nil nil 'alt "bar")
  	   "\\(foo\\|bar\\)")))

(ert-deftest drx-test-59 ()
  "See docstring of `drx-test-1'."
  (should (equal
  	   (drx "foo" nil nil nil t)
  	   "\\(foo\\)")))

(ert-deftest drx-test-60 ()
  "See docstring of `drx-test-1'."
  (should (equal
  	   (drx "foo" nil nil nil 2)
  	   "\\(foo\\)\\{2\\}")))

(ert-deftest drx-test-61 ()
  "See docstring of `drx-test-1'."
  (should (equal
  	   (drx "foo" nil nil nil "2")
  	   "\\(foo\\)\\{2\\}")))

(ert-deftest drx-test-62 ()
  "See docstring of `drx-test-1'."
  (should (equal
  	   (drx "foo" nil nil nil 1)
  	   "\\(foo\\)")))

(ert-deftest drx-test-63 ()
  "See docstring of `drx-test-1'."
  (should (equal
  	   (drx "foo" nil nil nil "1")
  	   "\\(foo\\)")))

(ert-deftest drx-test-64 ()
  "See docstring of `drx-test-1'."
  (should (equal
  	   (drx "foo" nil nil nil "1,")
  	   "\\(foo\\)\\{1,\\}")))

(ert-deftest drx-test-65 ()
  "See docstring of `drx-test-1'."
  (should (equal
  	   (drx "foo" nil nil nil ",1")
  	   "\\(foo\\)\\{,1\\}")))

(ert-deftest drx-test-66 ()
  "See docstring of `drx-test-1'."
  (should (equal
  	   (drx "foo" nil nil nil "1,3")
  	   "\\(foo\\)\\{1,3\\}")))

(ert-deftest drx-test-67 ()
  "See docstring of `drx-test-1'."
  (should (equal
  	   (drx "foo" nil nil nil "bar")
  	   "\\(foo\\)")))

(ert-deftest drx-test-68 ()
  "See docstring of `drx-test-1'."
  (should (equal
	   (drx "foo" nil nil nil nil "bar" "loo")
	   "foobarloo")))

(ert-deftest drx-test-69 ()
  "See docstring of `drx-test-1'."
  (should (equal
	   (drx "foo" nil nil nil t "bar" "loo")
	   "\\(foobarloo\\)")))

(ert-deftest drx-test-70 ()
  "See docstring of `drx-test-1'."
  (should (equal
	   (drx "foo" nil nil nil 'grp "bar" "loo")
	   "\\(foo\\)\\(bar\\)\\(loo\\)")))

(ert-deftest drx-test-71 ()
  "See docstring of `drx-test-1'."
  (should (equal
	   (drx "foo" nil nil nil 'alt "bar" "loo")
	   "\\(foo\\|bar\\|loo\\)")))

(ert-deftest drx-test-72 ()
  "See docstring of `drx-test-1'."
  (should (equal
	   (drx "foo" t nil t 'shy "bar" "loo")
	   "^\\(?:foo\\)\\(?:bar\\)\\(?:loo\\)$")))

(ert-deftest drx-test-73 ()
  "See docstring of `drx-test-1'."
  (should (equal
	   (drx "foo" t t t 'app "\\(bar\\)" "loo")
	   "^\\*\\(foo\\)\\(bar\\)\\(loo\\)$")))

(ert-deftest drx-test-74 ()
  "See docstring of `drx-test-1'."
  (should (equal
	   (drx "foo" t 1 t 'grp "\\(bar\\)" "loo")
	   "^\\*\\(foo\\)\\(\\(bar\\)\\)\\(loo\\)$")))

(ert-deftest drx-test-75 ()
  "See docstring of `drx-test-1'."
  (should (equal
	   (drx "foo" t 2 t 'app "\\(bar\\)" "loo")
	   "^\\*\\{2\\}\\(foo\\)\\(bar\\)\\(loo\\)$")))

(ert-deftest drx-test-76 ()
  "See docstring of `drx-test-1'."
  (should (equal
	   (drx "foo" nil nil nil '(nil) "bar" "loo")
	   "foobarloo")))

(ert-deftest drx-test-77 ()
  "See docstring of `drx-test-1'."
  (should (equal
	   (drx "foo" nil nil nil '(nil nil) "bar" "loo")
	   "foobarloo")))

(ert-deftest drx-test-78 ()
  "See docstring of `drx-test-1'."
  (should (equal
	   (drx "foo" nil nil nil '(t) "bar" "loo")
	   "\\(foobarloo\\)")))

(ert-deftest drx-test-79 ()
  "See docstring of `drx-test-1'."
  (should (equal
	   (drx "foo" nil nil nil '(t t) "bar" "loo")
	   "\\(foo\\(bar\\)loo\\)")))

(ert-deftest drx-test-80 ()
  "See docstring of `drx-test-1'."
  (should (equal
	   (drx "foo" nil nil nil '(t nil t) "bar" "loo")
	   "\\(foobar\\(loo\\)\\)")))

(ert-deftest drx-test-81 ()
  "See docstring of `drx-test-1'."
  (should (equal
	   (drx "foo" nil nil nil '(t t t) "bar" "loo")
	   "\\(foo\\(bar\\)\\(loo\\)\\)")))

(ert-deftest drx-test-82 ()
  "See docstring of `drx-test-1'."
  (should (equal
	   (drx "foo" nil nil nil '(1 1 1) "bar" "loo")
	   "\\(foobarloo\\)")))

(ert-deftest drx-test-83 ()
  "See docstring of `drx-test-1'."
  (should (equal
	   (drx "foo" t '(t t t) t '(t t t) "bar" "loo")
	   "^\\(\\(\\*\\)\\(\\*\\)\\)\\(foo\\(bar\\)\\(loo\\)\\)$")))

(ert-deftest drx-test-84 ()
  "See docstring of `drx-test-1'."
  (should (equal
	   (drx "foo" 1 '(1 1 1) 1 '(1 1 1) "bar" "loo")
	   "^\\(\\*\\*\\)\\(foobarloo\\)$")))


(ert-deftest drx-test-85 ()
  "See docstring of `drx-test-1'."
  (should (equal
	   (drx "foo" "1" '("1" "1" "1") "1" '("1" "1" "1")
		"bar" "loo")
	   "^\\(\\*\\*\\)\\(foobarloo\\)$")))

;; org-heading-regexp "^\\(\\*+\\)\\(?: +\\(.*?\\)\\)?[ \t]*$"
(ert-deftest drx-test-86 ()
  "See docstring of `drx-test-1'."
  (should (equal
	   (drx "\\(\\*+\\)\\(?: +\\(.*?\\)\\)?[ \t]*" t nil t)
	   "^\\(\\*+\\)\\(?: +\\(.*?\\)\\)?[ \t]*$")))

;; org-heading-regexp "^\\(\\*+\\)\\(?: +\\(.*?\\)\\)?[ \t]*$"
(ert-deftest drx-test-87 ()
  "See docstring of `drx-test-1'."
  (should (equal
	   (drx "\\(?: +\\(.*?\\)\\)?[ \t]*" t '(t "+") t)
	   "^\\(\\*+\\)\\(?: +\\(.*?\\)\\)?[ \t]*$")))

;; org-heading-regexp "^\\(\\*+\\)\\(?: +\\(.*?\\)\\)?[ \t]*$"
(ert-deftest drx-test-88 ()
  "See docstring of `drx-test-1'."
  (should (equal
	   (drx "foo" t '(t "+") t '("2" "?:" "*?") " " ".")
	   "^\\(\\*+\\)\\(?: +\\(.*?\\)\\)?[ \t]*$")))



;;; Provide

(provide 'drx)

;;; drx.el ends here
