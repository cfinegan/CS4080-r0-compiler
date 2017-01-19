#lang racket

(define (add a b)
  (+ (eval-expr a)
     (eval-expr b)))

(define (negation n)
  (* (eval-expr n) -1))

(define (sub a b)
  (- (eval-expr a)
     (eval-expr b)))

(define (mult a b)
  (* (eval-expr a)
     (eval-expr b)))

(define (div a b)
  (floor (/ (eval-expr a)
     (eval-expr b))))

(define (eval-expr expr)
  
  (define (eval-subexpr expr)
    (let [(proc (first expr))
          (args (rest expr))]
      (cond [(eq? proc '+) (add (first args) (second args))]
            [(eq? proc '-) (if (null? (second args))
                               (negation (first args))
                               (sub (first args) (second args)))]
            [(eq? proc '*) (mult (first args) (second args))]
            [(eq? proc '/) (div (first args) (second args))]
            [else (error "unrecognized procedure" proc)])))
  
  (cond [(integer? expr) expr]
        [(list? expr) (eval-subexpr expr)]
        [else (error "unrecognized token" expr)]))