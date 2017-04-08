#lang racket

(require "types.rkt")

(provide
 ht
 ht-e
 ht-T
 ht?
 typeof)

(struct ht (e T) #:transparent)

(define (typeof expr)
  (define (fmt-type-error arg expected-type expr)
    (format "typeof: Invalid argument '~a' (expected ~a) in expr: ~a"
            arg expected-type expr))
  (let typeof ([env #hash()] [expr expr])
    (define (recur e) (typeof env e))
    (match expr
      [(? integer?)
       (ht expr 'Integer)]
      [(? boolean?)
       (ht expr 'Boolean)]
      [(? symbol?)
       (ht expr (hash-ref env expr))]
      ['(void)
       (ht '(void) 'Void)]
      ['(read)
       (ht '(read) 'Integer)]
      ; not
      [`(not ,arg)
       (define ty-arg (recur arg))
       (unless (eq? (ht-T ty-arg) 'Boolean)
         (error (fmt-type-error arg 'Boolean expr)))
       (ht `(not ,ty-arg)
           'Boolean)]
      ; begin
      [`(begin ,subexprs ..1)
       (define ty-subs (map recur subexprs))
       (ht (cons 'begin ty-subs)
           (ht-T (last ty-subs)))]
      ; unary negation
      [`(- ,arg)
       (define ty-arg (recur arg))
       (unless (eq? (ht-T ty-arg) 'Integer)
         (error (fmt-type-error arg 'Integer expr)))
       (ht `(- ,ty-arg)
           'Integer)]
      ; boolean comparison
      [`(,(? boolean-op? op) ,arg1 ,arg2)
       (define ty-arg1 (recur arg1))
       (unless (eq? (ht-T ty-arg1) 'Integer)
         (error (fmt-type-error arg1 'Integer expr)))
       (define ty-arg2 (recur arg2))
       (unless (eq? (ht-T ty-arg2) 'Integer)
         (error (fmt-type-error arg2 'Integer expr)))
       (ht `(,op ,ty-arg1 ,ty-arg2)
           'Boolean)]
      ; arith expressions
      [`(,(? arith-op? op) ,arg1 ,arg2)
       (define ty-arg1 (recur arg1))
       (unless (eq? (ht-T ty-arg1) 'Integer)
         (error (fmt-type-error arg1 'Integer expr)))
       (define ty-arg2 (recur arg2))
       (unless (eq? (ht-T ty-arg2) 'Integer)
         (error (fmt-type-error arg2 'Integer expr)))
       (ht `(,op ,ty-arg1 ,ty-arg2)
           'Integer)]
      ; if expression
      [`(if ,cond ,then ,ow)
       (define ty-cond (recur cond))
       (unless (eq? (ht-T ty-cond) 'Boolean)
         (error (fmt-type-error cond 'Boolean expr)))
       (define ty-then (recur then))
       (define ty-ow (recur ow))
       (unless (equal? (ht-T ty-then) (ht-T ty-ow))
         (error "typeof: 'then' and 'else' branches have mismatched types in expr:" expr))
       (ht `(if ,ty-cond ,ty-then ,ty-ow)
           (ht-T ty-then))]
      ; let statement
      [`(let (,(? let-var? vars) ...) ,subexpr)
       (define-values (ty-vars next-env)
         (for/fold ([ty-vars empty] [next-env env])
                   ([var vars])
           (define name (first var))
           (define var-expr (recur (second var)))
           (values
            (cons `(,name ,var-expr) ty-vars)
            (hash-set next-env name (ht-T var-expr)))))
       (define ty-subexpr (typeof next-env subexpr))
       (ht `(let ,ty-vars ,ty-subexpr)
           (ht-T ty-subexpr))]
      ; vector
      [`(vector ,args ..1)
       (define ty-args (map recur args))
       (ht (cons 'vector ty-args)
           (cons 'Vector (map ht-T ty-args)))]
      ; vector-ref
      [`(vector-ref ,vec ,i)
       (define ty-vec (recur vec))
       (match (ht-T ty-vec)
         [`(Vector ,tys ..1)
          (unless (and (exact-nonnegative-integer? i)
                       (< i (length tys)))
            (error (format "typeof: Vector index ~a is out of range in expr: ~a" i expr)))
          (ht `(vector-ref ,ty-vec ,i)
              (list-ref tys i))]
         [else (error (format "typeof: vector-ref expects a Vector, not ~a" vec))])]
      ; vector-set!
      [`(vector-set! ,vec ,i ,arg)
       (define ty-vec (recur vec))
       (define ty-arg (recur arg))
       (match (ht-T ty-vec)
         [`(Vector ,tys ..1)
          (unless (and (exact-nonnegative-integer? i)
                       (< i (length tys)))
            (error (format "typeof: Vector index ~a is out of range in expr: ~a" i expr)))
          (define expect-ty (list-ref tys i))
          (unless (equal? (ht-T ty-arg) expect-ty)
            (error (fmt-type-error arg expect-ty expr)))
          (ht `(vector-set! ,ty-vec ,i ,ty-arg)
              'Void)]
         [else (error (format "typeof: vector-set! expects a Vector, not ~a" vec))])]
      ; error
      [else (error "invalid expression:" expr)]
      )))