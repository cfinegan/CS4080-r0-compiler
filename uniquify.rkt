#lang racket/base

(require racket/match
         "types.rkt")

;;; Returns an expression that is syntactically identical to the input expression, but
;;; with all variables given unique names.
(define (uniquify expr)
  
  ;; Mangles a symbol name by appending '_#' to it, where '#' is the number in next-id.
  (define (mangle-name sym next-id)
    (string->symbol (string-append (symbol->string sym) "_" (number->string next-id))))
  
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
      [`(begin ,body ...+)
       `(begin ,@(for/list ([exp body]) (uniquify exp symtab)))]
      [`(let ([,xs ,es] ...) ,subexpr)
       (define next-symtab
         (for/fold ([ht symtab]) ([name xs])
           (hash-set ht name (mangle-name name (get-next-id)))))
       `(let ,(for/list ([x xs] [e es])
                (list (render-name x next-symtab) (uniquify e symtab)))
          ,(uniquify subexpr next-symtab))]
      [`(if ,cond ,then ,otherwise)
       `(if ,(uniquify cond symtab) ,(uniquify then symtab) ,(uniquify otherwise symtab))]
      [(? list?)
       (map (λ (subexpr) (uniquify subexpr symtab)) expr)]
      [_ (error "uniquify - invalid expr:" expr)])))

(provide uniquify)
