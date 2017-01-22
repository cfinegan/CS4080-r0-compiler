#lang racket

(struct code (vars statements))

(struct return (arg))
(struct add (dest arg1 arg2))
(struct negate (dest arg))

(define (gen-linear-code expr)

  (define (gen-linear-code expr code)
    #f)

  (gen-linear-code expr (code empty empty)))

;; Exports
(provide gen-linear-code)