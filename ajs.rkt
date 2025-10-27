#lang eopl

;; =========================================
;; AJS Interpreter — Part 2:
;; Arithmetic + Constants + Functions
;; =========================================

;; -------- Lexer --------
(define ajs-lex
  '((whitespace (whitespace) skip)
    (comment ("//" (arbno (not #\newline))) skip)
    ;; numbers
    (number (digit (arbno digit)) number)
    (number ((arbno digit) "." digit (arbno digit)) number)
    ;; identifiers: [A-Za-z][A-Za-z0-9_]*  (allow underscore after first letter)
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
        "0" "1" "2" "3" "4" "5" "6" "7" "8" "9"
        "_")))
     symbol)))

;; -------- Grammar --------
(define ajs-grammar
  '(
    (program ((arbno toplevel)) a-program)

    ;; A toplevel item can be either a statement ending with ";" or a function decl
    (toplevel (statement ";") stmt-item)
    (toplevel (fun-decl) fun-item)

    ;; Statements
    (statement ("const" identifier "=" expression) const-decl)
    (statement (expression) expr-stmt)

    ;; Function declarations (no trailing semicolon!)
    (fun-decl
      ("function" identifier "(" (separated-list identifier ",") ")"
       "{" "return" expression ";" "}") a-fun-decl)

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
    (factor (identifier id-tail) id-or-call)
    (factor ("(" expression ")") group-factor)
    (factor ("-" factor) neg-factor)

    (id-tail ("(" (separated-list expression ",") ")") call-tail)
    (id-tail () empty-id-tail)
   ))

;; -------- SLLGEN boilerplate --------
(sllgen:make-define-datatypes ajs-lex ajs-grammar)

(define show-the-datatypes
  (lambda () (sllgen:list-define-datatypes ajs-lex ajs-grammar)))

(define scan&parse
  (sllgen:make-string-parser ajs-lex ajs-grammar))

;; -------- Environment utilities --------
(define empty-env '())

(define extend-env
  (lambda (var val env)
    (cons (cons var val) env)))

(define apply-env
  (lambda (env var)
    (cond
      [(assq var env) => cdr]
      [else (eopl:error 'apply-env "Unbound identifier ~a" var)])))

(define extend-env-multiple
  (lambda (params args env)
    (if (null? params)
        env
        (extend-env (car params) (car args)
                    (extend-env-multiple (cdr params) (cdr args) env)))))

;; -------- Numeric helper --------
(define ->js
  (lambda (n)
    (cond
      [(and (rational? n) (not (integer? n))) (exact->inexact n)]
      [else n])))

;; -------- Procedure datatype --------
(define-datatype proc proc?
  [closure (params (list-of symbol?))
           (body (lambda (x) #t))   ; accept any AST node as body
           (env list?)])

;; -------- Interpreter --------
(define value-of-program
  (lambda (pgm)
    (cases program pgm
      [a-program (items)
        (value-of-toplevels items empty-env)])))

(define value-of-toplevels
  (lambda (lst env)
    (if (null? lst)
        '()
        (let* ([item (car lst)]
               [rest (cdr lst)]
               [result+env (value-of-toplevel item env)]
               [val (car result+env)]
               [new-env (cdr result+env)])
          (cons val (value-of-toplevels rest new-env))))))

(define value-of-toplevel
  (lambda (it env)
    (cases toplevel it
      [stmt-item (st)
        (value-of-statement st env)]
      [fun-item (fd)
        (value-of-fun-decl fd env)])))

(define value-of-fun-decl
  (lambda (fd env)
    (cases fun-decl fd
      [a-fun-decl (id params body)
        (let ([val (closure params body env)])
          (cons val (extend-env id val env)))])))

(define value-of-statement
  (lambda (st env)
    (cases statement st
      [const-decl (id exp)
        (let ([val (->js (value-of-expr exp env))])
          (cons val (extend-env id val env)))]
      [expr-stmt (e)
        (cons (->js (value-of-expr e env)) env)])))

;; -------- Expression evaluation --------
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
      [group-factor (e) (value-of-expr e env)]
      [neg-factor (g) (- (value-of-factor g env))]
      [id-or-call (id tail)
        (cases id-tail tail
          [empty-id-tail ()
            (apply-env env id)]
          [call-tail (args)
            (let* ([proc-val (apply-env env id)]
                   [arg-vals (map (lambda (a) (value-of-expr a env)) args)])
              (apply-proc proc-val arg-vals))])])))

;; -------- Procedure application --------
(define apply-proc
  (lambda (proc-val args)
    (cases proc proc-val
      [closure (params body saved-env)
        (when (not (= (length params) (length args)))
          (eopl:error 'apply "arity mismatch: expected ~a args, got ~a"
                      (length params) (length args)))
        (let ([new-env (extend-env-multiple params args saved-env)])
          (->js (value-of-expr body new-env)))])))

;; -------- Runner / REPL --------

(define (ajs-run s)
  (value-of-program (scan&parse s)))

;; Read all characters until EOF (EOPL-safe)
(define (read-all)
  (let loop ([chars '()])
    (let ([c (read-char)])
      (if (eof-object? c)
          (list->string (reverse chars))
          (loop (cons c chars))))))

(define (REPL)
  (let* ([input (read-all)]
         [pgm (scan&parse input)]
         [vals (value-of-program pgm)])
    (for-each
     (lambda (v)
       (unless (proc? v)         ; don't show closure values
         (display v)
         (newline)))
     vals)))

(REPL)