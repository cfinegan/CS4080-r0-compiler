#lang racket

;; Mangles a symbol name by appending '_#' to it, where '#' is the number in next-id.
(define (mangle-name sym next-id)
  (string->symbol (string-append (symbol->string sym) "_" (number->string next-id))))

(define (symtab-with-vars symtab vars next-id)
  (define (add-var var table)
    (let ([name (car var)])
      (hash-set table name (mangle-name name next-id))))
  (foldl add-var symtab vars))

(define (render-name name symtab)
  (hash-ref symtab name name))

(define (gen-unique-names expr)
  
  (define (gen-unique-names expr next-id symtab)
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
                      (gen-unique-names (list proc vars subexpr)
                                        (+ 1 next-id)
                                        (symtab-with-vars symtab vars next-id)))
                    (gen-unique-names elem next-id symtab))])
             (else (error "unrecognized token:" elem)))
       lst))
    (foldr builder-proc empty expr))
  
  (first (gen-unique-names (list expr) 0 #hash())))

;; Exports
(provide gen-unique-names)

;; Tests
(gen-unique-names '(let ((x 10) (y 6)) (+ (let ((x 1) (y 4)) y) x)))
