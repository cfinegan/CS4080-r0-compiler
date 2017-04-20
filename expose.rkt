#lang racket

(require "types.rkt")
(require "typeof.rkt")

(provide expose-alloc)

(define (expose-alloc expr)
  (define next-arg-name
    (let ([next-id -1])
      (λ ()
        (set! next-id (add1 next-id))
        (string->symbol (string-append "vec" (number->string next-id))))))
  (let expose ([expr expr])
    (match expr
      [(ht `(vector ,args ...) `(Vector ,tys ...))
       (define bytes (* (length tys) ptr-size))
       (define arg-names (map (λ (_) (next-arg-name)) args))
       (typeof
        (for/fold
         ([body
           `(begin
              (if
               (< (+ (global "free_ptr") ,bytes)
                  (global "fromspace_end"))
               (void)
               (collect ,bytes))
              (let ([vec (allocate ,tys)])
                ,(cons
                  'begin
                  (foldr
                   (λ (i out)
                     (cons `(vector-set! vec ,i ,(list-ref arg-names i)) out))
                   (list 'vec)
                   (range 0 (length tys))))))])
         ([x arg-names] [e args])
          `(let ([,x ,(expose e)]) ,body)))]
      [(ht (? list? e) T)
       (ht (map expose e) T)]
      [_ expr])))