#lang racket

(require "types.rkt")

; tag:
; upper 5 bits are size (0 - 31) => (1 - 32).
; mid 27 bits are empty.
; lower 32 bits are the type tags.
; stores bits so that the lowest-order bit is the first type,
; 2nd-lowest-order bit is the 2nd type, etc.

;(define (types->tag tys)
;  (unless (not (empty? tys))
;    (error "Empty type list is not valid for a vector"))
;  (define tag-bits
;    (for/fold ([tag 0])
;              ([ty (reverse tys)])
;      (if (and (list? ty)
;               (eq? (first ty) 'Vector))
;          (add1 (arithmetic-shift tag 1))
;          (arithmetic-shift tag 1))))
;  (bitwise-ior (arithmetic-shift (sub1 (length tys)) 59)
;               tag-bits))

;; tag:
;; lower 32 bits are type tags.
;; next 5 bits are size (0 - 31) => (1 - 32).
;; upper 27 bits are don't cares (but in practice are zero)
;; stores bits so that lowest-order bit is first type,
;; 2nd-lowest-order bit is 2nd type, etc.
(define (types->tag tys)
  (when (empty? tys)
    (error 'types->tag "Empty type list is not valid for a vector"))
  (define tag-bits
    (for/fold ([tag 0])
              ([ty (reverse tys)])
      (if (and (list? ty)
               (eq? (first ty) 'Vector))
          (add1 (arithmetic-shift tag 1))
          (arithmetic-shift tag 1))))
  (bitwise-ior (arithmetic-shift (sub1 (length tys)) 32)
               tag-bits))

;; translates a naked primitive into a typed value
(define (arg->val arg)
  (match arg
    [(? integer?) (int arg)]
    [(? boolean?) (int (if arg 1 0))]
    [(? symbol?) (var arg)]
    [_ (error "invalid arg:" arg)]))

;; translates the arithmetic operators into asm-style op names.
(define (arith-name op)
  (match op
    ['+ 'add]
    ['- 'sub]
    [_ (error "invalid arith-op:" op)]))

;; translates a stmt type into an instruction or list of instructions
(define (stmt->insts stmt)
  (match stmt
    [(assign-stmt src-expr (? symbol? dest))
     (match src-expr
       [`(- ,arg)
        (list (binary-inst 'mov (arg->val arg) (var dest))
              (unary-inst 'neg (var dest)))]
       [`(,(? arith-op? op) ,arg1 ,arg2)
        (list (binary-inst 'mov (arg->val arg1) (var dest))
              (binary-inst (arith-name op) (arg->val arg2) (var dest)))]
       [`(not ,arg)
        (list (binary-inst 'mov (arg->val arg) (var dest))
              (binary-inst 'xor (int 1) (var dest)))]
       [`(,(? boolean-op? op) ,arg1 ,arg2)
        ; x86_64 cmp is reversed, LHS of expr goes in RHS of inst.
        (list (binary-inst 'cmp (arg->val arg2) (arg->val arg1))
              (unary-inst `(set ,op) (var dest)))]
       ['read
        (list (unary-inst 'call "read_int")
              (binary-inst 'mov (reg 'rax) (var dest)))]
       [(? symbol?)
        (binary-inst 'mov (var src-expr) (var dest))]
       [(? integer?)
        (binary-inst 'mov (int src-expr) (var dest))]
       [`(vector-ref ,vec ,i)
        (list (binary-inst 'mov (arg->val vec) (reg 'rax))
              (binary-inst 'mov (deref 'rax (* ptr-size (add1 i))) (var dest)))]
       [`(vector-set! ,vec ,i, arg)
        (list (binary-inst 'mov (arg->val vec) (reg 'rax))
              (binary-inst 'mov (arg->val arg) (deref 'rax (* ptr-size (add1 i))))
              (binary-inst 'mov (int 1) (var dest)))]
       [`(allocate ,tys)
        (list (binary-inst 'mov (global "free_ptr") (arg->val dest))
              (binary-inst 'add (int (* ptr-size (add1 (length tys)))) (global "free_ptr"))
              (binary-inst 'mov (arg->val dest) (reg 'rax))
              (binary-inst 'mov (int (types->tag tys)) (deref 'rax 0)))]
       [`(collect ,bytes)
        (list (binary-inst 'mov (reg 'r15) (vector-ref arg-registers 0))
              (binary-inst 'mov (int bytes) (vector-ref arg-registers 1))
              (unary-inst 'call "gc_collect")
              (binary-inst 'mov (int 1) (var dest)))]
       [`(global ,name)
        (binary-inst 'mov (global name) (arg->val dest))]
       )]
    [(if-stmt `(,cond-op ,L ,R) then-stmts otherwise-stmts)
     (if-stmt
      ; cond
      `(,cond-op ,(arg->val L) ,(arg->val R))
      ; then
      (flatten (map stmt->insts then-stmts))
      ; otherwise
      (flatten (map stmt->insts otherwise-stmts)))]
    [(return-stmt src-val)
     (binary-inst 'mov (arg->val src-val) (reg 'rax))]))

;; select-insts
(define (select-insts prog)
  (match-define (program hash-vars stmts) prog)
  (define vars (hash-keys hash-vars))
  (xprogram hash-vars (flatten (map stmt->insts stmts)) empty))

(provide select-insts)
