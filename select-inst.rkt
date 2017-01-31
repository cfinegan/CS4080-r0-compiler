#lang racket

(define (integer->asm int)
  (string-append "$" (number->string int)))

(define expr? list?)

(define (inst->asm inst)

  (define (expr->asm expr)
    #t)
  
  (match inst
    [(list 'assign src dest)
     #f]))

(define (select-inst program)

  (define (inst->x86* inst)
    (match inst
      [(list 'assign src dest)
       (cond [(eq? src 'read) (error "not implemented!")]
             [(symbol? src) src]
             [(integer? src) (integer->asm src)]
             [(list? src)
              (match src
                [(list '- arg)
             
  (match program
    [(list 'program (list vars ...) (list insts ...))
     (let ([x86-insts
            (map
             (λ (inst)
               (match inst
                 [(