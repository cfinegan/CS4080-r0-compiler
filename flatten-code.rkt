#lang racket

;(struct stmt (code vars))
;
;(define (mov-stmt src dest)
;  (stmt ('mov (list src dest))))
;
;(define (add-stmt src dest)
;  (stmt ('add (list src dest))))
;
;(define (ret-stmt)
;  (stmt ('ret empty)))
;
;(define (neg-stmt var)
;  (stmt ('neg (list var))))
;
;(define (read-stmt dest)
;  (stmt ('read (list dest))))

(define (next-tmp-name next-id)
  (string->symbol (string-append "tmp." (number->string next-id))))

;(define (flatten-code expr)
;  (let ([codes! empty])
;
;    (define (append-stmt stmt)
;      (set! codes! (cons stmt codes!)))
;    
;    (define (append-integer n next-name)
;      (set! codes! (cons (mov-stmt n next-name) codes!)))
;
;    (define (append-expr expr next-id)
;      (let ([next-name (next-tmp-name next-id)])
;        (cond [(integer? expr) (append-integer expr next-name)]
;              [(list? expr)
;               (let ([proc (first expr)]
;                     [args (rest expr)])
;                 (cond [(eq? proc 'let)
;                        (let ([vars (first args)]
;                              [subexpr (second args)])
;                          (begin
;                            (for-each (λ (var) (append-stmt (mov-stmt (cdr var) (car var)))) vars)
;                            (append-stmt]

(define (mov-stmt src dest)
  (list 'mov src dest))

(define (add-stmt src dest)
  (list 'add src dest))

(define (ret-stmt)
  (list 'ret))

(define (neg-stmt var)
  (list 'neg var))

(define (read-stmt dest)
  (list 'read dest))

(struct program (assign-stmts vars insts))

(define (flatten-code expr)
  (let ([prog! (program empty empty empty)])
    #f))