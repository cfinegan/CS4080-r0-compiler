#lang racket

(provide (all-defined-out))

;; Returns true if argument is a list in the form expected by the let macro.
(define (let-var? v)
  (and (list? v) (= 2 (length v))))

;; Airth ops are operations which expect 2 numbers and return a number.
(define (arith-op? op)
  (set-member? '(+ -) op))

;; Boolean ops are operations which expect 2 numbers and return a boolean.
(define (boolean-op? op)
  (set-member? '(= < > <= >=) op))

;; has-type (expr Type)
(struct ht (e T) #:transparent)

;; true if input is a vector type descriptor object.
(define (vector-ty? v)
  (and (list? v) (eq? (first v) 'Vector)))

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
(struct deref (reg amount) #:transparent)

;; if-stmt/lives is used by uncover-live to store extra liveness info,
;; but is discarded by assign-homes, which uses if-stmt.
(struct if-stmt/lives (cond then then-lives ow ow-lives) #:transparent)

;; instructions are associated with an xprogram, with the exception
;; of if-stmt and if-stmt/lives, which are not lowered until lower-conds.
(struct unary-inst (op arg) #:transparent)
(struct binary-inst (op src dest) #:transparent)
(struct xprogram (vars insts live-afters) #:transparent)

;; global constants
(define ptr-size 8)
(define root-stack (reg 'r15))
(define arg-registers (vector-map reg #(rdi rsi rdx rcx r8 r9)))