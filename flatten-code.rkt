#lang racket


;; dirty pig-disgusting mutable state
(define next-tmp-name
  (let ([next-id! 0])
    (λ ()
      (let ([next-name (string->symbol (string-append "tmp." (number->string next-id!)))])
        (begin (set! next-id! (add1 next-id!))
               next-name)))))

;; creates a new return instruction
(define (return-inst arg)
  (list 'return arg))

;; creates a new assign instruction
(define (assign-inst src dest)
  (list 'assign src dest))

;; creates a new program with specified vars and instructions
(define (program vars insts)
  (cond [(not (list? vars))
         (error "invalid argument (expected list) 'vars':" vars)]
        [(not (list? insts))
         (error "invalid argument (expected list) 'insts':" insts)]
        [else
         (list 'program vars insts)]))

;; gets the 'var' field of a program
(define (program-vars prog)
  (second prog))

;; gets the 'insts' field of a program
(define (program-insts prog)
  (third prog))

;; flatten an integer literal into a program that returns arg
(define (flatten-int arg)
  (program empty (list (return-inst arg))))

;; flatten a variable name into a program that declares that name and returns it.
(define (flatten-var arg)
  (program (list arg) (list (return-inst arg))))

;; flatten a read expression into a program that assigns 'read to a temp variable and returns it
(define (flatten-read)
  (let ([dest-name (next-tmp-name)])
    (program (list dest-name) (list (assign-inst 'read dest-name)
                                    (return-inst dest-name)))))

;; flatten a negation expression into a program that negates arg and returns it
(define (flatten-neg arg)
  (match (flatten-code arg)
    [(list 'program (list vars ...) (list stmts ... (list 'return ans)))
     (let ([dest-name (if (symbol? ans) ans (next-tmp-name))])
       (program (set-union (list dest-name) vars)
                (append stmts (list (assign-inst (list '- ans) dest-name)
                                    (return-inst dest-name)))))]))

;; flatten an a arithmetic expression into a program that applies proc-name to L and R, stores
;; the result in a variable, and returns it.
(define (flatten-arith proc-name L R)
  (match (flatten-code L)
    [(list 'program (list L-vars ...) (list L-stmts ... (list 'return L-ans)))
     (match (flatten-code R)
       [(list 'program (list R-vars ...) (list R-stmts ... (list 'return R-ans)))
        (let ([dest-name (next-tmp-name)])
          (program (filter symbol? (set-union L-vars R-vars (list L-ans R-ans dest-name)))
                   (append L-stmts R-stmts (list (assign-inst (list proc-name L-ans R-ans) dest-name)
                                                 (return-inst dest-name)))))])]))

;; flatten a let expression by breaking the var expressions into programs and appending them
;; to subexpr
(define (flatten-let vars subexpr)

  ;; Converts the (name expr) pair into a program which declares and assigns to var name, but
  ;; does *not* return it
  (define (var->prog var)
    (let ([var-name (first var)]
          [var-expr (second var)])
      (match (flatten-code var-expr)
        [(list 'program (list vars ...) (list stmts ... (list 'return ans)))
         (program vars (append stmts (list (assign-inst ans var-name))))])))
  
  (let ([var-prog (foldl append empty (map var->prog vars))]
        [subexpr-prog (flatten-code subexpr)])
    (program (append (program-vars var-prog) (program-vars subexpr-prog))
             (append (program-insts var-prog) (program-insts subexpr-prog)))))

;; flatten an expression by branching on type and calling appropriate helper procedure
(define (flatten-code expr)
  (cond [(integer? expr) (flatten-int expr)]
        [(symbol? expr) (flatten-var expr)]
        [(list? expr)
         (let ([proc (first expr)]
               [args (rest expr)])
           (cond [(eq? proc 'read)
                  (flatten-read)]
                 [(eq? proc 'let)
                  (flatten-let (first args) (second args))]
                 [(and (eq? proc '-) (= (length args) 1))
                  (flatten-neg (first args))]
                 [(set-member? '(+ - * /) proc)
                  (flatten-arith proc (first args) (second args))]
                 [else (error "unrecognized procedure name:" proc)]))]
        [else (error "unrecognized expression:" expr)]))

;; Export
(provide flatten-code)

;; Test
(flatten-code '(+ 1 (- 3)))
(flatten-code '(let ((x 3) (y 2)) (+ x y)))
(flatten-code '(let ((x 1)) (/ (read) x)))
(flatten-code '(+ 2 3))