#lang racket

(provide (all-defined-out))

(define ptr-size 8)

;; Returns true if argument is a list in the form expected by the let macro.
(define (let-var? v)
  (and (list? v) (= 2 (length v))))

;; Some basic sets outlining what operators are valid for what purposes.
(define (arith-op? op)
  (set-member? '(+ -) op))

(define (boolean-op? op)
  (set-member? '(= < > <= >=) op))

;; has-type (expr Type)
(struct ht (e T) #:transparent)

;; exprs after being flattened.
(struct unary-expr (op arg) #:transparent)
(struct binary-expr (op src dest) #:transparent)

;; statements are associated with a program
(struct return-stmt (arg) #:transparent)
(struct assign-stmt (src dest) #:transparent)
(struct if-stmt (cond then otherwise) #:transparent)
(struct program (vars stmts) #:transparent)

;; tags used for data going into the pseudo-asm
(struct int (val) #:transparent)
(struct var (name) #:transparent)
(struct reg (name) #:transparent)
(struct global (name) #:transparent)

;; instructions are associated with an xprogram
;; note: xprograms can also hold 'if-stmt' and 'if-stmt/lives' types
(struct unary-inst (op arg) #:transparent)
(struct binary-inst (op src dest) #:transparent)
(struct xprogram (vars insts live-afters) #:transparent)