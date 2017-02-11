#lang racket

;;;
;;; uniquify
;;; Returns an expression that is syntactically identical to the input expression, but
;;; with all variables given unique names.
(define (uniquify expr)
  
  ;; Mangles a symbol name by appending '_#' to it, where '#' is the number in next-id.
  (define (mangle-name sym next-id)
    (string->symbol (string-append (symbol->string sym) "_" (number->string next-id))))
  
  ;; Returns a new hash table representing a new environment with 'vars' added.
  ;; Symtab maps from names to mangled names.
  (define (symtab-with-vars symtab vars next-id)
    (define (add-var var table)
      (define name (car var))
      (hash-set table name (mangle-name name next-id)))
    (foldl add-var symtab vars))
  
  ;; Returns the symtab value indexed by 'name', or 'name' itself if not in table.
  (define (render-name name symtab)
    (hash-ref symtab name name))
  
  ;; This code really is terrible...
  ;; TODO: Replace with pattern matching?
  (first
   (let uniquify ([expr (list expr)] [next-id 0] [symtab #hash()])
     (define (builder-proc elem lst)
       (cons
        (cond ([integer? elem] elem)
              ([symbol? elem] [render-name elem symtab])
              ([list? elem]
               [let ([proc (first elem)]
                     [args (rest elem)])
                 (if [eq? proc 'let]
                     [let ([vars (first args)]
                           [subexpr (second args)])
                       (uniquify (list proc vars subexpr)
                                 (add1 next-id)
                                 (symtab-with-vars symtab vars next-id))]
                     (uniquify elem next-id symtab))])
              (else (error "unrecognized token:" elem)))
        lst))
     (foldr builder-proc empty expr))))


;; Creates a new return statement.
(struct return-stmt (arg) #:transparent)

;; Creates a new assignment statement.
(struct assign-stmt (src dest) #:transparent)

;; Creates a new program structure.
(struct program (vars stmts) #:transparent)

(struct unary-expr (op arg) #:transparent)

(struct binary-expr (op src dest) #:transparent)

(define (list->expr lst)
  (match lst
    [(list '- arg) (unary-expr 'neg arg)]
    [(list '+ arg1 arg2) (binary-expr 'add arg1 arg2)]
    [(list '- arg1 arg2) (binary-expr 'sub arg2 arg2)]
    [(list '* arg1 arg2) (binary-expr 'mul arg1 arg2)]
    [(list '/ arg1 arg2) (binary-expr 'div arg1 arg2)]))


;;;
;;; flatten-code
;;; Flattens an expression into a series of statements which only reference integers
;;; or variable names.
(define (flatten-code expr)
  
  ;; Always returns the 'next' temporary name. Encapsulates mutable state.
  (define next-tmp-name
    (let ([next-id -1])
      (λ ()
        (set! next-id (add1 next-id))
        (string->symbol (string-append "tmp." (number->string next-id))))))
  
  ;; Self-executing closure around helper procedures prevents recursive calls to flatten-code
  ;; from resetting the tmp-name count.
  (let flatten-code ([expr expr])
    
    ;; Flattens an integer literal into a program that returns arg.
    (define (flatten-int arg)
      (program empty (list (return-stmt arg))))
    
    ;; Flattens a variable name into a program that declares that name and returns it.
    (define (flatten-var arg)
      (program (list arg) (list (return-stmt arg))))
    
    ;; Flattens a read expression into a program that assigns 'read to a variable and returns it.
    (define (flatten-read)
      (define dest-name (next-tmp-name))
      (program (list dest-name) (list (assign-stmt 'read dest-name)
                                      (return-stmt dest-name))))
    
    ;; Flattens a negation expression into a program that negates arg and returns it.
    (define (flatten-neg arg)
      (match (flatten-code arg)
        [(program (list vars ...) (list stmts ... (return-stmt ans)))
         (let ([dest-name (next-tmp-name)])
           (program (set-union (list dest-name) vars)
                    (append stmts (list (assign-stmt (unary-expr 'neg ans) dest-name)
                                        (return-stmt dest-name)))))]))
    
    ;; Flattens an arithmetic expression into a program that applies proc-naem to L and R, stores
    ;; the result in a variable, and returns it.
    (define (flatten-arith proc-name L R)
      (match (flatten-code L)
        [(program (list L-vars ...) (list L-stmts ... (return-stmt L-ans)))
         (match (flatten-code R)
           [(program (list R-vars ...) (list R-stmts ... (return-stmt R-ans)))
            (let ([dest-name (next-tmp-name)])
              (program
               (filter symbol? (set-union L-vars R-vars (list L-ans R-ans dest-name)))
               (append L-stmts R-stmts (list (assign-stmt (list->expr (list proc-name L-ans R-ans)) dest-name)
                                             (return-stmt dest-name)))))])]))
    
    ;; Flattens a let expression by breaking the var expressions into programs and appending them to subexpr.
    (define (flatten-let vars subexpr)
      
      ;; Converts the (name expr) pair into a program which declares and assigns to var name, but does
      ;; not return it.
      (define (var->prog var)
        (let ([var-name (first var)]
              [var-expr (second var)])
          (match (flatten-code var-expr)
            [(program (list vars ...) (list stmts ... (return-stmt ans)))
             (program vars (append stmts (list (assign-stmt ans var-name))))])))
      
      ;; Combines several of the "special" progs generated by var->prog into one program.
      (define (combine-progs progs)
        (let ([vars (foldl append empty (map program-vars progs))]
              [stmts (foldl append empty (map program-stmts progs))])
          (program vars stmts)))
      
      (let ([var-prog (combine-progs (map var->prog vars))]
            [subexpr-prog (flatten-code subexpr)])
        (program (append (program-vars var-prog) (program-vars subexpr-prog))
                 (append (program-stmts var-prog) (program-stmts subexpr-prog)))))
    
    ;; flatten-code procedure body.
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
          [else (error "unrecognized expression:" expr)])))


(struct int (val) #:transparent)

(struct var (name) #:transparent)

(struct reg (name) #:transparent)

(struct unary-inst (op arg) #:transparent)

(struct binary-inst (op src dest) #:transparent)


(struct xprogram (vars insts) #:transparent)

;;;
;;; select-insts
(define (select-insts prog)
  
  (define (arg->val arg)
    (cond [(integer? arg) (int arg)]
          [(symbol? arg) (var arg)]
          [else (error "invalid arg:" arg)]))

  (define (stmt->insts stmt)
    (match stmt
      [(assign-stmt src-expr (? symbol? dest))
       (match src-expr
         [(unary-expr op arg)
          (list (binary-inst 'mov (arg->val arg) (var dest))
                (unary-inst op (var dest)))]
         [(binary-expr op arg1 arg2)
          (list (binary-inst 'mov (arg->val arg1) (var dest))
                (binary-inst op (arg->val arg2) (var dest)))]
         ['read
          (list (unary-inst 'call "read_int")
                (binary-inst 'mov (reg 'rax) (var dest)))]
         [(? symbol? arg)
          (binary-inst 'mov (var arg) (var dest))]
         [(? integer? arg)
          (binary-inst 'mov (int arg) (var dest))])]
      [(return-stmt src-val)
       (unary-inst 'ret (arg->val src-val))]))
  
  (xprogram (program-vars prog) (flatten (map stmt->insts (program-stmts prog)))))



(define ptr-size 8)

(struct deref (reg amount) #:transparent)

(struct xxprogram (stack-size insts) #:transparent)

;;;
;;; assign-homes
(define (assign-homes xprog)
  
  (define var-count (length (xprogram-vars xprog)))
  (define stack-size (* ptr-size (if (even? var-count) var-count (add1 var-count))))
  
  (define var-homes
    (let map-homes ([vars (xprogram-vars xprog)] [index 0] [homes #hash()])
      (if (null? vars)
          homes
          (map-homes (rest vars) (add1 index) (hash-set homes (first vars) (- (* index ptr-size)))))))
  
  (define (var->deref arg)
    (if (var? arg)
        (deref 'rbp (hash-ref var-homes (var-name arg)))
        arg))

  (define (apply-deref inst)
    (match inst
      [(unary-inst op arg) (unary-inst op (var->deref arg))]
      [(binary-inst op src dest) (binary-inst op (var->deref src) (var->deref dest))]))
  
  (xxprogram stack-size (map apply-deref (xprogram-insts xprog))))


;;;
;;; patch-insts
;;;
(define (patch-insts xxprog)
  
  (define stack-size (xxprogram-stack-size xxprog))

  (define (patch inst)
    (match inst
      [(binary-inst op (? deref? src) (? deref? dest))
       (list (binary-inst 'mov src (reg 'rax))
             (binary-inst op (reg 'rax) dest))]
      [_ inst]))

  (xxprogram stack-size (flatten (map patch (xxprogram-insts xxprog)))))


(define u uniquify)
(display "uniquify") (newline)
(u '(- 5))
(u '(+ x 3))
(u '(- 4 y))
(u '(let ([x 3] [y 4]) (+ x y)))
(u '(+ 3 (read)))

(define f flatten-code)
(display "flatten") (newline)
(f 5)
(f '(- 5))
(f '(+ 2 3))
(f '(* 4 5))
(f '(+ 3 (read)))
(f (u '(+ 2 (- 3 (/ 4 (- 5))))))
(f (u '(let ([x (+ 2 3)] [y 1]) (* x (- y)))))

(define s select-insts)
(display "select-insts") (newline)
(s (f (u 5)))
(s (f (u '(+ 4 (read)))))
(s (f (u '(let ([x (+ 2 3)] [y 1]) (* x (- y))))))

(define a assign-homes)
(display "assign-homes") (newline)
(a (s (f (u '(+ 1 2)))))
(a (s (f (u '(+ 4 (read))))))
(a (s (f (u '(let ([x (+ 2 3)] [y 1]) (* x (- y)))))))

(define p patch-insts)
(display "patch-insts") (newline)
(p (a (s (f (u '(+ 3 (read)))))))
(p (a (s (f (u '(let ([x (+ 2 3)] [y 1]) (* x (- y))))))))