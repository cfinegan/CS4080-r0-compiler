#lang racket

(provide replace-syntax)

(define (replace-syntax expr)
  (define r replace-syntax)
  (define (var-args-op? op)
    (set-member? '(+ - * or and) op))
  (match expr
    ; optimize conditionals
    [`(if ,cond ,then ,ow)
     (match cond
       [#t (r then)]
       [#f (r ow)]
       [`(not ,subexpr)
        `(if ,(r subexpr) ,(r ow) ,(r then))]
       [_ `(if ,(r cond) ,(r then) ,(r ow))])]
    ; Breaks var-args into 'pyramid' of calls
    [`(,(? var-args-op? op) ,arg1 ,args ..2)
     `(,op ,(r arg1) ,(r (cons op args)))]
    ; Recursively call self on nested calls.
    [(? list?)
     (map r expr)]
    ; Default
    [_ expr]))