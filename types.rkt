#lang racket

(provide
 let-var?
 arith-op?
 boolean-op?
 (struct-out ht)
 (struct-out return-stmt)
 (struct-out assign-stmt)
 (struct-out if-stmt)
 (struct-out program)
 (struct-out unary-expr)
 (struct-out binary-expr))

;; Returns true if argument is a list in the form expected by the let macro.
(define (let-var? v)
  (and (list? v) (= 2 (length v))))


;; Some basic sets outlining what operators are valid for what purposes.
(define (arith-op? op)
  (set-member? '(+ -) op))

(define (boolean-op? op)
  (set-member? '(= < > <= >=) op))

(struct ht (e T) #:transparent)

(struct return-stmt (arg) #:transparent)

(struct assign-stmt (src dest) #:transparent)

(struct if-stmt (cond then otherwise) #:transparent)

(struct program (vars stmts) #:transparent)

(struct unary-expr (op arg) #:transparent)

(struct binary-expr (op src dest) #:transparent)