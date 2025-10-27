#lang eopl

;; =========================================
;; AJS Interpreter — Part 4:
;; Arithmetic + Constants + Functions + Booleans/Conditionals + Recursion
;; =========================================

;; -------- Lexer --------
(define ajs-lex
  '((whitespace (whitespace) skip)
    (comment ("//" (arbno (not #\newline))) skip)
    ;; numbers
    (number (digit (arbno digit)) number)
    (number ((arbno digit) "." digit (arbno digit)) number)
    ;; booleans: return 'true or 'false as symbols
    (bool ((or "true" "false")) symbol)
    ;; identifiers: [A-Za-z][A-Za-z0-9_]* (allow underscore after first letter)
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

    ;; Top-level accepts either:
    ;;   - a simple statement followed by ";"
    ;;   - a compound statement (no ";")
    (toplevel (simple-stmt ";") top-simple)
    (toplevel (compound-stmt) top-comp)
    (toplevel (fun-decl) fun-item)

    ;; Simple statements (must end with ";")
    (simple-stmt ("const" identifier "=" expression) const-decl)
    (simple-stmt (expression) expr-stmt)

    ;; Compound statements (no trailing ";")
    (compound-stmt ("if" "(" expression ")" block opt-else) if-stmt)
    (compound-stmt (block) block-stmt)

    ;; Left-factored optional else to avoid LL(1) conflict on "else"
    (opt-else ("else" else-body) else-some)
    (opt-else () no-else)

    ;; After "else", we either have a block or a nested if
    (else-body (block) else-block)
    (else-body (nested-if) else-if)

    ;; Nested if is itself a compound shape
    (nested-if ("if" "(" expression ")" block opt-else) nested-if-stmt)

    ;; Blocks contain a sequence of either simple-stmt ";" or compound-stmt
    (block ("{" (arbno block-item) "}") a-block)
    (block-item (simple-stmt ";") blk-simple)
    (block-item (compound-stmt) blk-comp)

    ;; Function declarations (no trailing semicolon!)
    (fun-decl
      ("function" identifier "(" (separated-list identifier ",") ")"
       "{" "return" expression ";" "}") a-fun-decl)

    ;; -------- Expressions with booleans/conditionals and + / - --------
    (expression (additive maybe-ternary) an-expr)

    (maybe-ternary ("?" expression ":" expression) ternary-expr)
    (maybe-ternary () no-ternary)

    ;; + / - with lower precedence than ||, &&, comparisons
    (additive (logic-or additive+) a-additive)
    (additive+ ("+" logic-or additive+) add-more)
    (additive+ ("-" logic-or additive+) sub-more)
    (additive+ () no-add)

    ;; logical OR / AND
    (logic-or (logic-and logic-or+) a-logic-or)
    (logic-or+ ("||" logic-and logic-or+) or-more)
    (logic-or+ () no-or)

    (logic-and (comparison logic-and+) a-logic-and)
    (logic-and+ ("&&" comparison logic-and+) and-more)
    (logic-and+ () no-and)

    ;; comparisons
    (comparison (term maybe-comp) a-comparison)
    (maybe-comp (">" term) gt-comp)
    (maybe-comp ("<" term) lt-comp)
    (maybe-comp (">=" term) ge-comp)
    (maybe-comp ("<=" term) le-comp)
    (maybe-comp ("===" term) eq-comp)
    (maybe-comp ("!=" term) ne-comp)
    (maybe-comp () no-comp)

    ;; arithmetic terms
    (term (factor term+) a-term)
    (term+ ("*" factor term+) mul-term)
    (term+ ("/" factor term+) div-term)
    (term+ () empty-term)

    (factor (number) num-factor)
    (factor (bool) bool-factor)
    (factor (identifier id-tail) id-or-call)
    (factor ("(" expression ")") group-factor)
    (factor ("-" factor) neg-factor)
    (factor ("!" factor) not-factor)

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

;; -------- Procedure datatype (with self-name for recursion) --------
(define-datatype proc proc?
  [closure (name symbol?)                       ; function's own identifier
           (params (list-of symbol?))
           (body (lambda (x) #t))               ; accept any AST node as body
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
      [top-simple (st) (value-of-simple-stmt st env)]
      [top-comp   (cs) (value-of-compound-stmt cs env)]
      [fun-item   (fd) (value-of-fun-decl fd env)])))

(define value-of-fun-decl
  (lambda (fd env)
    (cases fun-decl fd
      [a-fun-decl (id params body)
        ;; Self-binding closure for recursion
        (letrec ([val (closure id params body env)])
          (cons val (extend-env id val env)))])))

;; ----- Blocks -----
(define value-of-block
  (lambda (blk env)
    (cases block blk
      [a-block (items)
        (value-of-block-items items env)])))

(define value-of-block-items
  (lambda (items env)
    (if (null? items)
        (cons #f env)
        (let* ([first (car items)]
               [rest  (cdr items)]
               [res+env (value-of-block-item first env)]
               [val     (car res+env)]
               [new-env (cdr res+env)])
          (if (null? rest)
              (cons val new-env)
              (value-of-block-items rest new-env))))))

(define value-of-block-item
  (lambda (bi env)
    (cases block-item bi
      [blk-simple (st) (value-of-simple-stmt st env)]
      [blk-comp   (cs) (value-of-compound-stmt cs env)])))

;; ----- Statements -----
(define value-of-simple-stmt
  (lambda (st env)
    (cases simple-stmt st
      [const-decl (id exp)
        (let ([val (->js (value-of-expr exp env))])
          (cons val (extend-env id val env)))]
      [expr-stmt (e)
        (cons (->js (value-of-expr e env)) env)])))

(define value-of-compound-stmt
  (lambda (cs env)
    (cases compound-stmt cs
      [if-stmt (test blk opt)
        (let ([cond (value-of-expr test env)])
          (if (truthy? cond)
              (value-of-block blk env)
              (cases opt-else opt
                [else-some (eb)
                  (cases else-body eb
                    [else-block (b2) (value-of-block b2 env)]
                    [else-if   (nested) (value-of-nested-if nested env)])]
                [no-else () (cons #f env)])))]
      [block-stmt (blk) (value-of-block blk env)])))

(define value-of-nested-if
  (lambda (nif env)
    (cases nested-if nif
      [nested-if-stmt (test blk opt)
        (let ([cond (value-of-expr test env)])
          (if (truthy? cond)
              (value-of-block blk env)
              (cases opt-else opt
                [else-some (eb)
                  (cases else-body eb
                    [else-block (b2) (value-of-block b2 env)]
                    [else-if   (nested2) (value-of-nested-if nested2 env)])]
                [no-else () (cons #f env)])))])))

;; -------- Expression evaluation --------
(define value-of-expr
  (lambda (e env)
    (cases expression e
      [an-expr (add ternary)
        (let ([val (value-of-additive add env)])
          (cases maybe-ternary ternary
            [ternary-expr (true-expr false-expr)
              (if (truthy? val)
                  (value-of-expr true-expr env)
                  (value-of-expr false-expr env))]
            [no-ternary () val]))])))

;; additive (+ / -)
(define value-of-additive
  (lambda (e env)
    (cases additive e
      [a-additive (left rest)
        (let ([v (value-of-logic-or left env)])
          (value-of-additive+ v rest env))])))

(define value-of-additive+
  (lambda (left rest env)
    (cases additive+ rest
      [add-more (right tail)
        (value-of-additive+ (+ left (value-of-logic-or right env)) tail env)]
      [sub-more (right tail)
        (value-of-additive+ (- left (value-of-logic-or right env)) tail env)]
      [no-add () left])))

;; logical OR / AND
(define value-of-logic-or
  (lambda (e env)
    (cases logic-or e
      [a-logic-or (left rest)
        (let ([v (value-of-logic-and left env)])
          (value-of-logic-or+ v rest env))])))

(define value-of-logic-or+
  (lambda (left rest env)
    (cases logic-or+ rest
      [or-more (right tail)
        (if (truthy? left)
            #t
            (value-of-logic-or+ (value-of-logic-and right env) tail env))]
      [no-or () left])))

(define value-of-logic-and
  (lambda (e env)
    (cases logic-and e
      [a-logic-and (left rest)
        (let ([v (value-of-comparison left env)])
          (value-of-logic-and+ v rest env))])))

(define value-of-logic-and+
  (lambda (left rest env)
    (cases logic-and+ rest
      [and-more (right tail)
        (if (not (truthy? left))
            #f
            (value-of-logic-and+ (value-of-comparison right env) tail env))]
      [no-and () left])))

;; comparisons
(define value-of-comparison
  (lambda (e env)
    (cases comparison e
      [a-comparison (t maybe)
        (let ([v1 (value-of-term t env)])
          (cases maybe-comp maybe
            [gt-comp (t2)  (> v1 (value-of-term t2 env))]
            [lt-comp (t2)  (< v1 (value-of-term t2 env))]
            [ge-comp (t2)  (>= v1 (value-of-term t2 env))]
            [le-comp (t2)  (<= v1 (value-of-term t2 env))]
            [eq-comp (t2)  (equal? v1 (value-of-term t2 env))]
            [ne-comp (t2)  (not (equal? v1 (value-of-term t2 env)))]
            [no-comp () v1]))])))

;; -------- Arithmetic evaluation --------
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
      [bool-factor (b) (if (eq? b 'true) #t #f)]
      [not-factor (g) (not (truthy? (value-of-factor g env)))]
      [group-factor (e) (value-of-expr e env)]
      [neg-factor (g) (- (value-of-factor g env))]
      [id-or-call (id tail)
        (cases id-tail tail
          [empty-id-tail () (apply-env env id)]
          [call-tail (args)
            (let* ([proc-val (apply-env env id)]
                   [arg-vals (map (lambda (a) (value-of-expr a env)) args)])
              (apply-proc proc-val arg-vals))])])))

;; -------- Boolean helpers --------
(define (truthy? v)
  (and v (not (eq? v #f))))

;; -------- Procedure application (self-binding for recursion) --------
(define apply-proc
  (lambda (proc-val args)
    (cases proc proc-val
      [closure (name params body saved-env)
        (when (not (= (length params) (length args)))
          (eopl:error 'apply "arity mismatch: expected ~a args, got ~a"
                      (length params) (length args)))
        (let* ([base-env (extend-env name proc-val saved-env)]
               [new-env  (extend-env-multiple params args base-env)])
          (->js (value-of-expr body new-env)))])))

;; -------- Runner / REPL --------
(define (ajs-run s)
  (value-of-program (scan&parse s)))

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
       (unless (proc? v)
         (display v)
         (newline)))
     vals)))

(REPL)
