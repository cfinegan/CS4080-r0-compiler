#lang racket

(provide
 let-var?
 arith-op?
 boolean-op?)

;; Returns true if argument is a list in the form expected by the let macro.
(define (let-var? v)
  (and (list? v) (= 2 (length v))))


;; Some basic sets outlining what operators are valid for what purposes.
(define (arith-op? op)
  (set-member? '(+ -) op))

(define (boolean-op? op)
  (set-member? '(= < > <= >=) op))