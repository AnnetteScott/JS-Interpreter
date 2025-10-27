#lang eopl

;; ===============================
;; AJS (Part 1: Arithmetic only)
;; ===============================

;; -------- Lexer --------
(define ajs-lex
  '((whitespace (whitespace) skip)
    (comment ("//" (arbno (not #\newline))) skip)
    (number (digit (arbno digit)) number)
    (number ((arbno digit) "." digit (arbno digit)) number)))

;; -------- Grammar --------
(define ajs-grammar
  '(
    (program ((arbno statement ";")) a-program)

    (statement (expression) expr-stmt)

    (expression (term expression+) an-expr)
    (expression+ ("+" term expression+) add-expr)
    (expression+ ("-" term expression+) sub-expr)
    (expression+ () empty-expr)

    (term (factor term+) a-term)
    (term+ ("*" factor term+) mul-term)
    (term+ ("/" factor term+) div-term)
    (term+ () empty-term)

    (factor (number) num-factor)
    (factor ("(" expression ")") group-factor)
    (factor ("-" factor) neg-factor)
   ))

;; -------- SLLGEN boilerplate --------
(sllgen:make-define-datatypes ajs-lex ajs-grammar)

(define show-the-datatypes
  (lambda () (sllgen:list-define-datatypes ajs-lex ajs-grammar)))

(define scan&parse
  (sllgen:make-string-parser ajs-lex ajs-grammar))

(define parse-stream
  (sllgen:make-stream-parser ajs-lex ajs-grammar))

;; -------- Interpreter --------
(define ->js
  (lambda (n)
    (cond
      [(and (rational? n) (not (integer? n))) (exact->inexact n)]
      [else n])))

(define value-of-program
  (lambda (pgm)
    (cases program pgm
      [a-program (stmt-list)
        (map value-of-statement stmt-list)])))

(define value-of-statement
  (lambda (st)
    (cases statement st
      [expr-stmt (e) (->js (value-of-expr e))])))

(define value-of-expr
  (lambda (e)
    (cases expression e
      [an-expr (t e+) (value-of-expr+ (value-of-term t) e+)])))

(define value-of-expr+
  (lambda (acc e+)
    (cases expression+ e+
      [add-expr (t rest) (value-of-expr+
                          (+ acc (value-of-term t))
                          rest)]
      [sub-expr (t rest) (value-of-expr+
                          (- acc (value-of-term t))
                          rest)]
      [empty-expr () acc])))

(define value-of-term
  (lambda (tm)
    (cases term tm
      [a-term (f t+) (value-of-term+ (value-of-factor f) t+)])))

(define value-of-term+
  (lambda (acc t+)
    (cases term+ t+
      [mul-term (f rest) (value-of-term+
                          (* acc (value-of-factor f))
                          rest)]
      [div-term (f rest) (value-of-term+
                          (->js (/ acc (value-of-factor f)))
                          rest)]
      [empty-term () acc])))

(define value-of-factor
  (lambda (f)
    (cases factor f
      [num-factor (n) n]
      [group-factor (e) (value-of-expr e)]
      [neg-factor (g) (- (value-of-factor g))])))

;; -------- Runner / REPL --------
(require racket/format)

(define (ajs-run s)
  (value-of-program (scan&parse s)))

(define (REPL)
  ((sllgen:make-rep-loop
     "AJS> "
     (lambda (pgm)
       (for-each
        (lambda (v)
          (display v)
          (newline))
        (value-of-program pgm)))
     parse-stream)))


(REPL)







