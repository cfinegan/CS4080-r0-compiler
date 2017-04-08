#lang racket

(require "types.rkt")

(provide uniquify)

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
    (for/fold ([table symtab]) ([var vars])
      (define name (car var))
      (hash-set table name (mangle-name name next-id))))
  
  ;; Returns the symtab value indexed by 'name', or 'name' itself if not in table.
  (define (render-name name symtab)
    (hash-ref symtab name name))
  
  (define get-next-id
    (let ([next-id -1])
      (λ ()
        (set! next-id (add1 next-id))
        next-id)))
  
  (let uniquify ([expr expr] [symtab #hash()])    
    (match expr
      [(? integer?) expr]
      [(? boolean?) expr]
      [(? symbol?) (render-name expr symtab)]
      ['(read) '(read)]
      ['(void) '(void)]
      [`(begin ,subexprs ..1)
       (cons 'begin (map (λ (subexpr) (uniquify subexpr symtab)) subexprs))]
      [`(let (,(? let-var? vars) ...) ,subexpr)
       (define next-symtab (symtab-with-vars symtab vars (get-next-id)))
       (define (render-var var)
         `(,(render-name (first var) next-symtab) ,(uniquify (second var) symtab)))
       `(let ,(map render-var vars) ,(uniquify subexpr next-symtab))]
      [`(if ,cond ,then ,otherwise)
       `(if ,(uniquify cond symtab) ,(uniquify then symtab) ,(uniquify otherwise symtab))]
      [(? list?)
       (map (λ (subexpr) (uniquify subexpr symtab)) expr)]
      [_ (error "uniquify - invalid expr:" expr)])))