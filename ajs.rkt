#lang eopl

;; =========================================
;; AJS Interpreter — Part 1:
;; Arithmetic + Constant Declarations
;; =========================================

;; -------- Lexer --------

;; Define regex categories
(define ajs-lex
  '((whitespace (whitespace) skip)
    (comment ("//" (arbno (not #\newline))) skip)
    ;; numbers
    (number (digit (arbno digit)) number)
    (number ((arbno digit) "." digit (arbno digit)) number)
    ;; identifiers  [A-Za-z][A-Za-z0-9]*
    (identifier
     ((or
       "a" "b" "c" "d" "e" "f" "g" "h" "i" "j" "k" "l" "m" "n" "o" "p" "q" "r"
       "s" "t" "u" "v" "w" "x" "y" "z"
       "A" "B" "C" "D" "E" "F" "G" "H" "I" "J" "K" "L" "M" "N" "O" "P" "Q" "R"
       "S" "T" "U" "V" "W" "X" "Y" "Z")
      (arbno
       (or
        "a" "b" "c" "d" "e" "f" "g" "h" "i" "j" "k" "l" "m" "n" "o" "p" "q" "r"
        "s" "t" "u" "v" "w" "x" "y" "z"
        "A" "B" "C" "D" "E" "F" "G" "H" "I" "J" "K" "L" "M" "N" "O" "P" "Q" "R"
        "S" "T" "U" "V" "W" "X" "Y" "Z"
        "0" "1" "2" "3" "4" "5" "6" "7" "8" "9")))
     symbol)))


;; -------- Grammar --------
(define ajs-grammar
  '(
    (program ((arbno statement ";")) a-program)

    ;; Statements
    (statement ("const" identifier "=" expression) const-decl)
    (statement (expression) expr-stmt)

    ;; Expressions
    (expression (term expression+) an-expr)
    (expression+ ("+" term expression+) add-expr)
    (expression+ ("-" term expression+) sub-expr)
    (expression+ () empty-expr)

    (term (factor term+) a-term)
    (term+ ("*" factor term+) mul-term)
    (term+ ("/" factor term+) div-term)
    (term+ () empty-term)

    (factor (number) num-factor)
    (factor (identifier) id-factor)
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

;; -------- Environment utilities --------
(define empty-env '())

(define extend-env
  (lambda (var val env)
    (cons (cons var val) env)))

(define apply-env
  (lambda (env var)
    (cond
      [(assq var env) => cdr]
      [else (eopl:error 'apply-env "Unbound variable ~a" var)])))

;; -------- Numeric helper --------
(define ->js
  (lambda (n)
    (cond
      [(and (rational? n) (not (integer? n))) (exact->inexact n)]
      [else n])))

;; -------- Interpreter --------
(define value-of-program
  (lambda (pgm)
    (cases program pgm
      [a-program (stmt-list)
        (value-of-statements stmt-list empty-env)])))

(define value-of-statements
  (lambda (stmts env)
    (if (null? stmts)
        '()
        (let* ([stmt (car stmts)]
               [rest (cdr stmts)]
               [result+env (value-of-statement stmt env)]
               [val (car result+env)]
               [new-env (cdr result+env)])
          (cons val (value-of-statements rest new-env))))))

(define value-of-statement
  (lambda (st env)
    (cases statement st
      [const-decl (id exp)
        (let ([val (->js (value-of-expr exp env))])
          (cons val (extend-env id val env)))]
      [expr-stmt (e)
        (cons (->js (value-of-expr e env)) env)])))

(define value-of-expr
  (lambda (e env)
    (cases expression e
      [an-expr (t e+)
        (value-of-expr+ (value-of-term t env) e+ env)])))

(define value-of-expr+
  (lambda (acc e+ env)
    (cases expression+ e+
      [add-expr (t rest)
        (value-of-expr+ (+ acc (value-of-term t env)) rest env)]
      [sub-expr (t rest)
        (value-of-expr+ (- acc (value-of-term t env)) rest env)]
      [empty-expr () acc])))

(define value-of-term
  (lambda (tm env)
    (cases term tm
      [a-term (f t+) (value-of-term+ (value-of-factor f env) t+ env)])))

(define value-of-term+
  (lambda (acc t+ env)
    (cases term+ t+
      [mul-term (f rest)
        (value-of-term+ (* acc (value-of-factor f env)) rest env)]
      [div-term (f rest)
        (value-of-term+
         (->js (/ acc (value-of-factor f env))) rest env)]
      [empty-term () acc])))

(define value-of-factor
  (lambda (f env)
    (cases factor f
      [num-factor (n) n]
      [id-factor (id) (apply-env env id)]
      [group-factor (e) (value-of-expr e env)]
      [neg-factor (g) (- (value-of-factor g env))])))

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

;; Uncomment to start REPL automatically
(REPL)
