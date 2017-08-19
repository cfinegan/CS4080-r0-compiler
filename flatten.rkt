#lang racket/base

(require
  racket/contract/base
  racket/hash
  racket/list
  racket/match
  syntax/parse/define
  "types.rkt" )

(define-simple-macro (hash-combine h0:expr hs:expr ...)
  (hash-union
   h0 hs ...
   #:combine/key
   (λ (k a b)
     (unless (equal? a b)
       (error 'hash-combine "non-equal values for key ~a: ~a and ~a" k a b))
     a)))

(define (flatten-code expr)
  
  (define next-tmp-name
    (let ([next-id -1])
      (λ ()
        (set! next-id (add1 next-id))
        (string->symbol (string-append "tmp." (number->string next-id))))))
             
  (let flatten-code ([expr expr] [vartab (hash)])
    (match-define (ht e T) expr)
    (match e
      ; primitive
      [(? (or/c integer? boolean?))
       (program (hash) (list (return-stmt e)))]
      ; symbol
      [(? symbol?)
       (define name-ref (hash-ref vartab e #f))
       (if name-ref
           (flatten-code name-ref vartab)
           (program (hash e T)
                    (list (return-stmt e))))] ; TODO: should we crash if we cant find in table?
      ; read expression
      ['(read)
       (define dest-name (next-tmp-name))
       (program (hash dest-name T) 
                (list (assign-stmt 'read dest-name)
                      (return-stmt dest-name)))]
      ; void expression
      ['(void)
       (program #hash() (list (return-stmt 1)))]
      ; begin expression
      [`(begin ,subexprs ..1)
       (define subexpr-progs (map (λ (e) (flatten-code e vartab)) subexprs))
       (define se-prog
         (foldr
          (λ (pr out)
            (match-define (program out-vars (list out-stmts ...)) out)
            (match-define (program pr-vars (list pr-stmts ... (return-stmt pr-ans))) pr)
            (program (hash-combine out-vars pr-vars)
                     (append pr-stmts out-stmts)))
          (program #hash() empty)
          subexpr-progs))
       (program (program-vars se-prog)
                (append (program-stmts se-prog) (list (last (program-stmts (last subexpr-progs))))))]
      ; let expression
      [`(let ([,xs ,es] ...) ,subexpr)
       (define-values (next-vartab var-prog)
         (for/fold ([vartab vartab] [var-prog (program (hash) empty)])
                   ([var-name xs] [var-expr es])
           (match-define (program vars (list stmts ... (return-stmt ans)))
             (flatten-code var-expr vartab))
           (values (hash-set vartab var-name (ht ans (ht-T var-expr)))
                   (program (hash-combine (program-vars var-prog) vars)
                            (append (program-stmts var-prog) stmts)))))
       (define subexpr-prog (flatten-code subexpr next-vartab))
       (program (hash-combine (program-vars var-prog)
                              (program-vars subexpr-prog))
                (append (program-stmts var-prog) (program-stmts subexpr-prog)))]
      ; if expression
      [`(if ,cond ,then ,else)
       (define cond-expr
         (match cond
           [(ht (? (or/c symbol? boolean?)) 'Boolean)
            ; literal is on RHS so that it will be on LHS in cmp operation.
            `(= ,(flatten-code cond vartab) ,(flatten-code (ht #t 'Boolean) vartab))]
           ;; TODO: optimize let case to not require 2 cmps
           [(ht `(let (,(? let-var? vars) ...) ,subexpr) 'Boolean)
            `(=, (flatten-code cond vartab) ,(flatten-code (ht #t 'Boolean) vartab))]
           [(ht `(,op ,exp1 ,exp2) 'Boolean)
            `(,op ,(flatten-code exp1 vartab) ,(flatten-code exp2 vartab))]))
       (match-define
         (list cond-op
               (program ce1-vars (list ce1-stmts ... (return-stmt ce1-ans)))
               (program ce2-vars (list ce2-stmts ... (return-stmt ce2-ans))))
         cond-expr)
       (match-define (program then-vars (list then-stmts ... (return-stmt then-ans)))
         (flatten-code then vartab))
       (match-define (program else-vars (list else-stmts ... (return-stmt else-ans)))
         (flatten-code else vartab))
       (define dest-name (next-tmp-name))
       (program
        (hash-combine (hash dest-name T) ce1-vars ce2-vars then-vars else-vars)
        (append ce1-stmts
                ce2-stmts
                (list (if-stmt
                       `(,cond-op ,ce1-ans ,ce2-ans)
                       (append then-stmts (list (assign-stmt then-ans dest-name)))
                       (append else-stmts (list (assign-stmt else-ans dest-name))))
                      (return-stmt dest-name))))]
      ; arithmetic negation / binary negation
      [`(,(? (λ (op) (or (eq? op '-) (eq? op 'not))) op) ,subexpr)
       (match-define (program vars (list stmts ... (return-stmt ans)))
         (flatten-code subexpr vartab))
       (define dest-name (next-tmp-name))
       (program (hash-combine vars (hash dest-name T))
                (append stmts (list (assign-stmt `(,op ,ans) dest-name)
                                    (return-stmt dest-name))))]
      ; binary arithmetic / boolean operators
      [`(,(? (or/c boolean-op? arith-op?) op) ,L ,R)
       (match-define (program L-vars (list L-stmts ... (return-stmt L-ans)))
         (flatten-code L vartab))
       (match-define (program R-vars (list R-stmts ... (return-stmt R-ans)))
         (flatten-code R vartab))
       (define dest-name (next-tmp-name))
       (program
        (hash-combine L-vars R-vars
                      (make-immutable-hash
                       (filter
                        (λ (p) (symbol? (car p)))
                        (list (cons L-ans (ht-T L))
                              (cons R-ans (ht-T R))
                              (cons dest-name T)))))
        (append L-stmts R-stmts (list (assign-stmt `(,op ,L-ans ,R-ans) dest-name)
                                      (return-stmt dest-name))))]
      ; vector-ref
      [`(vector-ref ,vec ,i)
       (match-define (program vars (list stmts ... (return-stmt ans)))
         (flatten-code vec vartab))
       (define dest-name (next-tmp-name))
       (program
        (hash-combine vars (hash dest-name T))
        (append stmts (list (assign-stmt `(vector-ref ,ans ,i) dest-name)
                            (return-stmt dest-name))))]
      ; vector-set!
      [`(vector-set! ,vec ,i ,arg)
       (match-define (program vec-vars (list vec-stmts ... (return-stmt vec-ans)))
         (flatten-code vec vartab))
       (match-define (program arg-vars (list arg-stmts ... (return-stmt arg-ans)))
         (flatten-code arg vartab))
       (define void-return-name (next-tmp-name))
       (program
        (hash-combine vec-vars arg-vars (hash void-return-name 'Void))
        (append vec-stmts arg-stmts
                (list (assign-stmt `(vector-set! ,vec-ans ,i ,arg-ans) void-return-name)
                      (return-stmt void-return-name))))]
      ; global value
      [`(global ,(? string?))
       (define dest-name (next-tmp-name))
       (program (hash dest-name T)
                (list (assign-stmt e dest-name)
                      (return-stmt dest-name)))]
      ; collect expression
      [`(collect ,bytes)
       (define void-return-name (next-tmp-name))
       (program (hash void-return-name 'Void)
                (list (assign-stmt e void-return-name)
                      (return-stmt void-return-name)))]
      ; allocate expression
      [`(allocate ,tys ...)
       (define dest-name (next-tmp-name))
       (program (hash dest-name T)
                (list (assign-stmt e dest-name)
                      (return-stmt dest-name)))])))

(provide flatten-code)
