#lang racket

;; Mangles a symbol name by appending '_#' to it, where '#' is the number in next-id.
(define (mangle-name sym next-id)
  (string->symbol (string-append (symbol->string sym) "_" (number->string next-id))))

;; Returns a new hash table representing a new environment with 'var' added to it
;; by mangling their names to append 'next-id'.
(define (symtab-with-vars symtab vars next-id)
  (define (add-var var table)
    (let ([name (car var)])
      (hash-set table name (mangle-name name next-id))))
  (foldl add-var symtab vars))

;; Returns the symtab value indexed by 'name', or 'name' itself if 'name' is not a
;; key in the table.
(define (render-name name symtab)
  (hash-ref symtab name name))

;; Returns an expression that is syntactically identical to the input expression, but
;; with all variables given unique names.
(define (uniquify expr)
  
  ;; Recursive helper procedure threads 'next-id' and 'symtab' through the recursive
  ;; process.
  (define (uniquify expr next-id symtab)
    (define (builder-proc elem lst)
      (cons
       (cond ([integer? elem] elem)
             ([symbol? elem] [render-name elem symtab])
             ([list? elem]
              [let ([proc (first elem)]
                    [args (rest elem)])
                (if (eq? proc 'let)
                    (let ([vars (first args)]
                          [subexpr (second args)])
                      (uniquify (list proc vars subexpr)
                                (add1 next-id)
                                (symtab-with-vars symtab vars next-id)))
                    (uniquify elem next-id symtab))])
             (else (error "unrecognized token:" elem)))
       lst))
    (foldr builder-proc empty expr))
  
  (first (uniquify (list expr) 0 #hash())))

;; Exports
(provide uniquify)