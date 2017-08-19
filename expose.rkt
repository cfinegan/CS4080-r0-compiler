#lang racket/base

(require racket/list
         racket/match
         "types.rkt"
         "typeof.rkt")

(define (expose-alloc expr)
  (match expr
    [(ht `(vector ,args ...) `(Vector ,tys ...))
     (define bytes (* (add1 (length tys)) ptr-size))
     (define arg-names (for/list ([a args]) (gensym 'vec)))
     (define body-begin
       `(begin
          (if (< (+ (global "free_ptr") ,bytes)
                 (global "fromspace_end"))
              (void)
              (collect ,bytes))
          (let ([vec (allocate ,tys)])
            (begin ,@(for/list ([i (range (length tys))])
                       `(vector-set! vec ,i ,(list-ref arg-names i)))
                   vec))))
     (typeof (for/fold ([body body-begin])
                       ([x arg-names] [e args])
               `(let ([,x ,(expose-alloc e)]) ,body)))]
    [(ht (? list? e) T)
     (ht (map expose-alloc e) T)]
    [_ expr]))

(provide expose-alloc)