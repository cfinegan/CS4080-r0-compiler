#lang racket

(require
  racket/hash
  graph
  "types.rkt"
  "uniquify.rkt"
  "typeof.rkt")

(define (replace-syntax expr)
  (define r replace-syntax)
  (define (var-args-op? op)
    (set-member? '(+ - * or and) op))
  (match expr
    ; or
    [`(or ,arg1 ,arg2)
     `(let ([or.tmp ,(r arg1)])
        (if or.tmp or.tmp ,(r arg2)))]
    ; and
    [`(and ,arg1 ,arg2)
     `(if ,(r arg1) ,(r arg2) #f)]
    ; optimize conditionals
    [`(if ,cond ,then ,ow)
     (match cond
       [#t (r then)]
       [#f (r ow)]
       [`(not ,subexpr)
        `(if ,(r subexpr) ,(r ow) ,(r then))]
       [_ `(if ,(r cond) ,(r then) ,(r ow))])]
    ; Breaks var-args into 'pyramid' of calls
    [`(,(? var-args-op? op) ,arg1 ,args ..2)
     `(,op ,(r arg1) ,(r (cons op args)))]
    ; Recursively call self on nested calls.
    [(? list?)
     (map r expr)]
    ; Default
    [_ expr]))


;;;
;;; expose-alloc
;;;
(define (expose-alloc expr)
  (define next-arg-name
    (let ([next-id -1])
      (λ ()
        (set! next-id (add1 next-id))
        (string->symbol (string-append "vec" (number->string next-id))))))
  (let expose ([expr expr])
    (match expr
      [(ht `(vector ,args ...) `(Vector ,tys ...))
       (define bytes (* (length tys) ptr-size))
       (define arg-names (map (λ (_) (next-arg-name)) args))
       (typeof
        (for/fold
         ([body
           `(begin
              (if
               (< (+ (global "free_ptr") ,bytes)
                  (global "fromspace_end"))
               (void)
               (collect ,bytes))
              (let ([vec (allocate ,tys)])
                ,(cons
                  'begin
                  (foldr
                   (λ (i out)
                     (cons `(vector-set! vec ,i ,(list-ref arg-names i)) out))
                   (list 'vec)
                   (range 0 (length tys))))))])
         ([x arg-names] [e args])
          `(let ([,x ,(expose e)]) ,body)))]
      [(ht (? list? e) T)
       (ht (map expose e) T)]
      [_ expr])))
     

;; ========
;; Creates a new return statement.
(struct return-stmt (arg) #:transparent)

;; Creates a new assignment statement.
(struct assign-stmt (src dest) #:transparent)

(struct if-stmt (cond then otherwise) #:transparent)

;; Creates a new program structure.
(struct program (vars stmts) #:transparent)

(struct unary-expr (op arg) #:transparent)

(struct binary-expr (op src dest) #:transparent)

;;;
;;; flatten-code
;;; Flattens an expression into a series of statements which only reference integers
;;; or variable names.

(define (flatten-code expr)
  
  (define next-tmp-name
    (let ([next-id -1])
      (λ ()
        (set! next-id (add1 next-id))
        (string->symbol (string-append "tmp." (number->string next-id))))))
  
  (define (combine-var-keys k a b)
    (unless (equal? a b)
      (error (format "non-equal values for key ~a: ~a and ~a" k a b)))
    a)
           
  (let flatten-code ([expr expr] [vartab #hash()])
    (match-define (ht e T) expr)
    (match e
      ; primitive
      [(? (or/c integer? boolean?))
       (program #hash() (list (return-stmt e)))]
      ; symbol
      [(? symbol?)
       (define name-ref (hash-ref vartab e #f))
       (if name-ref
           (flatten-code name-ref vartab)
           (program #; #hash((e . T)) (make-immutable-hash (list (cons e T)))
                    (list (return-stmt e))))] ; TODO: should we crash if we cant find in table?
      ; read expression
      ['(read)
       (define dest-name (next-tmp-name))
       (program (make-immutable-hash (list (cons dest-name T)))
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
            (program (hash-union out-vars pr-vars)
                     (append pr-stmts out-stmts)))
          (program #hash() empty)
          subexpr-progs))
       (program (program-vars se-prog)
                (append (program-stmts se-prog) (list (last (program-stmts (last subexpr-progs))))))]
      ; let expression
      [`(let (,(? let-var? vars) ...) ,subexpr)
       (define-values (next-vartab var-prog)
         (for/fold ([vartab vartab] [var-prog (program #hash() empty)])
                   ([var vars])
           (define var-name (first var))
           (define var-expr (second var))
           (match-define (program vars (list stmts ... (return-stmt ans)))
             (flatten-code var-expr vartab))
           (values (hash-set vartab var-name (ht ans (ht-T var-expr)))
                   (program (hash-union (program-vars var-prog) vars)
                            (append (program-stmts var-prog) stmts)))))
       (define subexpr-prog (flatten-code subexpr next-vartab))
       (program (hash-union (program-vars var-prog)
                            (program-vars subexpr-prog)
                            #:combine/key combine-var-keys)
                (append (program-stmts var-prog) (program-stmts subexpr-prog)))]
      ; if expression
      [`(if ,cond ,then ,else)
       (define cond-expr
         (match cond
           [(ht (? (or/c symbol? boolean?)) 'Boolean)
            ; literal is on RHS so that it will be on LHS in cmp operation.
            `(= ,(flatten-code cond vartab) ,(flatten-code (ht #t 'Boolean) vartab))]
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
        (hash-union (make-immutable-hash (list (cons dest-name T)))
                    ce1-vars ce2-vars then-vars else-vars
                    #:combine/key combine-var-keys)
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
       (program (hash-union vars (make-immutable-hash (list (cons dest-name T))))
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
        (hash-union L-vars R-vars
                    (make-immutable-hash
                     (filter
                      (λ (p) (symbol? (car p)))
                      (list (cons L-ans (ht-T L))
                            (cons R-ans (ht-T R))
                            (cons dest-name T))))
                    #:combine/key combine-var-keys)
        (append L-stmts R-stmts (list (assign-stmt `(,op ,L-ans ,R-ans) dest-name)
                                      (return-stmt dest-name))))])))


(struct int (val) #:transparent)

(struct var (name) #:transparent)

(struct reg (name) #:transparent)

(struct unary-inst (op arg) #:transparent)

(struct binary-inst (op src dest) #:transparent)

(struct xprogram (vars insts live-afters) #:transparent)

;;;
;;; select-insts
(define (select-insts prog)
  (match-define (program hash-vars stmts) prog)
  (define vars (hash-keys hash-vars))
  
  (define (arg->val arg)
    (match arg
      [(? integer?) (int arg)]
      [(? boolean?) (int (if arg 1 0))]
      [(? symbol?) (var arg)]
      [_ (error "invalid arg:" arg)]))
  
  (define (arith-name op)
    (match op
      ['+ 'add]
      ['- 'sub]
      [_ (error "invalid arith-op:" op)]))
  
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
          (binary-inst 'mov (int src-expr) (var dest))])]
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
  
  (xprogram vars (flatten (map stmt->insts stmts)) empty))


;;;
;;; uncover-live
;;;
(struct if-stmt/lives (cond then then-lives ow ow-lives) #:transparent)

(define (uncover-live xprog)
  (match-define (xprogram vars all-insts emtpy) xprog)
  
  (define (move-inst? op)
    (set-member? '(mov movzb) op))
  
  #; ; TODO: Do we actually need this? right now it's never called, book recommends it.
  (define (get-vars inst)
    (filter
     var?
     (match inst
       [(unary-inst op arg)
        (list arg)]
       [(binary-inst op arg1 arg2)
        (list arg1 arg2)])))
  
  (define (get-reads inst)
    (filter
     var?
     (match inst
       ; set doesn't read from arg
       [(unary-inst `(set _) arg)
        empty]
       ; pop doesn't read from arg
       [(unary-inst 'pop arg)
        empty]
       ; all other unary insts are assumed to read
       [(unary-inst op arg)
        (list arg)]
       ; move insts don't read arg2
       [(binary-inst (? move-inst?) arg1 arg2)
        (list arg1)]
       ; all other binary insts are assumed to read both args
       [(binary-inst op arg1 arg2)
        (list arg1 arg2)])))
  
  (define (get-writes inst)
    (filter
     var?
     (match inst
       ; push doesn't write to arg
       [(unary-inst 'push arg)
        empty]
       ; all other unary insts are assumed to write
       [(unary-inst op arg)
        (list arg)]
       ; cmp doesn't write to either arg
       [(binary-inst 'cmp arg1 arg2)
        empty]
       ; all other binary insts are assumed to write to arg2
       [(binary-inst op arg1 arg2)
        (list arg2)])))
  
  (define drop1 rest)  
  
  (define-values (insts l-afters)
    (let get-lives ([in-insts all-insts]
                    [in-l-afters (list empty)])
      
      (for/fold ([insts empty]
                 [l-afters in-l-afters])
                ([inst (reverse in-insts)])
        (define l-after (first l-afters))
        
        (define-values (out-inst l-before)
          (match inst
            ; if statements
            [(if-stmt `(,cond-op ,L ,R) then ow)
             (define-values (then-insts then-afters)
               (get-lives then (list l-after)))
             (define-values (ow-insts ow-afters)
               (get-lives ow (list l-after)))
             (values
              (if-stmt/lives `(,cond-op ,L ,R)
                             then-insts
                             (drop1 then-afters)
                             ow-insts
                             (drop1 ow-afters))
              (set-union (first then-afters) (first ow-afters) (filter var? (list L R))))]
            ; all other insts
            [_
             (values
              inst
              (set-union (set-subtract l-after (get-writes inst))
                         (get-reads inst)))]))
        
        (values
         (cons out-inst insts)
         (cons l-before l-afters)))))
  
  ;; add first inst back to insts before returning
  (xprogram vars insts (drop1 l-afters)))


;;;
;;; build-interference
;;;
;; Note: %rax omitted because it's used by compiler as scratch.
(define caller-saved '(rcx rdx r8 r9 r10 r11))
(define callee-saved '(rbx rbp rdi rsi rsp r12 r13 r14 r15))

(define (build-interference xprog)
  
  (match-define (xprogram vars insts live-afters) xprog)
  
  (let ([insts-len (length insts)]
        [la-len (length live-afters)])
    (unless (= insts-len la-len)
      (error
       (format
        "insts (size: ~a) and live-afters (size: ~a) must have same length"
        insts-len la-len))))
  
  (define graph (unweighted-graph/undirected empty))
  
  (let build-inter ([insts insts]
                    [live-afters live-afters])
    (for ([inst insts]
          [l-after live-afters])
      (match inst
        [(binary-inst 'mov src (? var? dest))
         (for ([var l-after])
           (unless (or (equal? var dest) (equal? var src))
             (add-edge! graph (var-name dest) (var-name var))))]
        [(binary-inst op src (? var? dest))
         (for ([var l-after])
           (unless (equal? var dest)
             (add-edge! graph (var-name var) (var-name dest))))]
        [(unary-inst 'call (? string? label))
         (for ([var l-after])
           (for ([reg caller-saved])
             (add-edge! graph reg (var-name var))))]
        [(if-stmt/lives cond then then-lives ow ow-lives)
         (begin
           (build-inter then then-lives)
           (build-inter ow ow-lives)
           (void))]
        [else (void)])))
  
  graph)


(define ptr-size 8)
(struct deref (reg amount) #:transparent)
(struct xxprogram (stack-size insts) #:transparent)

(define alloc-registers #(rbx rdi rsi r12 r13 r14 r15 ;; callee-saved
                              rcx rdx r8 r9 r10 r11 ;; caller-saved
                              ))

;;;
;;; assign-homes
;;;
(define (assign-homes xprog)
  
  ;; TODO: diagnostic prints: keep or remove?
  
  (match-define (xprogram vars insts l-afters) xprog)
  
  (define interference (build-interference xprog))
  
  (define num-valid-registers (vector-length alloc-registers))
  
  (define (color->home color)
    (if (< color num-valid-registers)
        (reg (vector-ref alloc-registers color))
        (deref 'rbp (- (* ptr-size (add1 (- color num-valid-registers)))))))
  
  (define-values (num-colors colorings)
    (coloring/greedy interference))
  
  (display "num colors: ") (display num-colors) (newline)
  
  (define spill-count (max 0 (- num-colors num-valid-registers)))
  (define stack-size (* ptr-size (if (even? spill-count) spill-count (add1 spill-count))))
  
  (display "spill count: ") (display spill-count) (newline)
  (display "stack size: ") (display stack-size) (newline)
  
  (define (get-var-home tok)
    (if (var? tok)
        ;; defaults to zero b/c colorings will be empty in case of no interference.
        (color->home (hash-ref colorings (var-name tok) 0))
        tok))
  
  (define home-insts
    (let assign-homes ([insts insts]
                       [l-afters l-afters])
      (flatten
       (reverse
        (for/fold ([out empty])
                  ([inst insts] [l-after l-afters])
          (cons
           (match inst
             [(unary-inst 'call func)
              (define lives (set-intersect (map get-var-home l-after) (map reg caller-saved)))
              (append (map (λ (var) (unary-inst 'push var)) lives)
                      (if (odd? (length lives))
                          (list (binary-inst 'sub (int ptr-size) (reg 'rsp))
                                inst
                                (binary-inst 'add (int ptr-size) (reg 'rsp)))
                          (list inst))
                      (foldl (λ (var lst) (cons (unary-inst 'pop var) lst)) empty lives))]
             [(unary-inst op arg)
              (unary-inst op (get-var-home arg))]
             [(binary-inst op src dest)
              (binary-inst op (get-var-home src) (get-var-home dest))]
             [(if-stmt/lives `(,cond-op ,L ,R) then then-afters ow ow-afters)
              (if-stmt `(,cond-op ,(get-var-home L) ,(get-var-home R))
                       (assign-homes then then-afters)
                       (assign-homes ow ow-afters))]
             )
           out))))))
  
  (xxprogram stack-size home-insts))


;;;
;;; lower-conds
;;;
(struct label (name) #:transparent)

(define (lower-conds xxprog)
  (match-define (xxprogram stack-size insts) xxprog)
  
  (define next-label
    (let ([next-id -1])
      (λ ()
        (set! next-id (add1 next-id))
        (format "r0L~a" next-id))))
  
  (define (lower-cond inst)
    (match inst
      [(if-stmt `(,op ,L ,R) then-insts ow-insts)
       (define then-label (next-label))
       (define end-label (next-label))
       (list
        ; note: x86_64 cmp is backwards, R must be in left-hand position.
        (binary-inst 'cmp R L)
        (unary-inst `(jmp-if ,op) then-label)
        (map lower-cond ow-insts)
        (unary-inst 'jmp end-label)
        (label then-label)
        (map lower-cond then-insts)
        (label end-label))]
      [_ inst]))
  
  (xxprogram stack-size (flatten (map lower-cond insts))))

;;;
;;; patch-insts
;;;
(define (patch-insts xxprog)
  
  (match-define (xxprogram stack-size insts) xxprog)
  
  (define (patch inst)
    (match inst
      ;; remove trivial moves
      [(binary-inst 'mov src dest)
       (if (equal? src dest)
           empty
           inst)]
      ;; memory cannot be deref'd twice in the same instruction
      [(binary-inst op (? deref? src) (? deref? dest))
       (list (binary-inst 'mov src (reg 'rax))
             (binary-inst op (reg 'rax) dest))]
      ;; cmp instruction can't have literals as second arg
      [(binary-inst 'cmp arg1 (? int? arg2))
       (list (binary-inst 'mov arg2 (reg 'rax))
             (binary-inst 'cmp arg1 (reg 'rax)))]
      ;; set instruction can only reference 8-bit registers
      [(unary-inst `(set ,op) dest)
       (list (unary-inst `(set ,op) (reg 'al))
             (binary-inst 'movzb (reg 'al) dest))]
      [_ inst]))
  
  (xxprogram stack-size (flatten (map patch insts))))


;;;
;;; print-asm
;;;
(define (fmt-asm op . args)
  (string-append "\t" op "\t" (string-join args ", ") "\n"))

(define (fmt-label label-name)
  (define func-prefix (if (eq? (system-type 'os) 'macosx) "_" ""))
  (string-append func-prefix label-name))

(define (int->asm n)
  (string-append "$" (number->string n)))

(define (op->cc op)
  (match op
    ['= "e"]
    ['< "l"]
    ['<= "le"]
    ['> "g"]
    ['>= "ge"]))

(define (op->asm op)
  (match op
    ['neg "negq"]
    ['mov "movq"]
    ['add "addq"]
    ['sub "subq"]
    ['mul "imulq"]
    ['div "idivq"]
    ['call "callq"]
    ['pop "popq"]
    ['push "pushq"]
    ['xor "xorq"]
    ['cmp "cmpq"]
    ['movzb "movzbq"]
    ['jmp "jmp"]
    [`(set ,bool-op)
     (string-append "set" (op->cc bool-op))]
    [`(jmp-if ,bool-op)
     (string-append "j" (op->cc bool-op))]))

(define (arg->asm arg)
  (match arg
    [(int n)
     (int->asm n)]
    [(reg r)
     (string-append "%" (symbol->string r))]
    [(deref r offset)
     (string-append (if (zero? offset) "" (number->string offset)) "(%" (symbol->string r) ")")]
    [(? string? str)
     (fmt-label str)]))

(define (inst->asm inst)
  (match inst
    [(unary-inst op arg)
     (fmt-asm (op->asm op) (arg->asm arg))]
    [(binary-inst op src dest)
     (fmt-asm (op->asm op) (arg->asm src) (arg->asm dest))]
    [(label name)
     (format "~a:\n" (fmt-label name))]))

(define (type->int ty)
  (match ty
    ['Void 0]
    ['Integer 1]
    ['Boolean 2]))

(define (print-asm xxprog ty)
  (define stack-size (xxprogram-stack-size xxprog))
  (define insts (xxprogram-insts xxprog))
  (define r0func-name (fmt-label "r0func"))
  (define ty_void (fmt-label "ty_void"))
  (define ty_integer (fmt-label "ty_integer"))
  (define ty_boolean (fmt-label "ty_boolean"))

  (define (globl-names)
    (define (fmt-globl label)
      (format "\t.globl ~a\n" label))
    (string-append
     (fmt-globl r0func-name)
     (fmt-globl ty_void)
     (fmt-globl ty_integer)
     (fmt-globl ty_boolean)))

  (define asm-prefix
    (string-append
     "\t.text\n"
     (globl-names)
     (format "~a:\n" r0func-name)))
  
  (define stack-prefix
    (string-append
     (fmt-asm "pushq" "%rbp")
     (fmt-asm "movq" "%rsp" "%rbp")
     (if (zero? stack-size) "" (fmt-asm "subq" (int->asm stack-size) "%rsp"))))

  (define print-call
    (string-append
     (fmt-asm "movq" "%rax" "%rdi")
     (fmt-asm "movq" (int->asm (type->int ty)) "%rsi")
     (fmt-asm "callq" (fmt-label "write_any"))))
  
  (define stack-suffix
    (string-append
     (if (zero? stack-size) "" (fmt-asm "addq" (int->asm stack-size) "%rsp"))
     (fmt-asm "popq" "%rbp")))
  
  (define main-return (fmt-asm "retq"))

  (define type-table
    (string-append
     (format "~a:\n" ty_void)
     (format "\t.quad ~a\n" (type->int 'Void))
     (format "~a:\n" ty_integer)
     (format "\t.quad ~a\n" (type->int 'Integer))
     (format "~a:\n" ty_boolean)
     (format "\t.quad ~a\n" (type->int 'Boolean))))
  
  (define final-asm
    (string-append
     asm-prefix
     stack-prefix
     (apply string-append (map inst->asm insts))
     print-call
     stack-suffix
     main-return
     type-table))
  
  final-asm)

;;;
;;; Utils for compiling and runnings ASM code
;;;

;; Creates an ASM string from an input expression.
(define (expr->asm expr)
  (define u-expr (uniquify (replace-syntax expr)))
  (define typed-expr (typeof u-expr))
  (define return-type (ht-T typed-expr))
  (define C-stmts (uncover-live (select-insts (flatten-code typed-expr))))
  (define X-insts (patch-insts (lower-conds (assign-homes C-stmts))))
  (print-asm X-insts return-type))

;; Compiles the program using whatever's currently in the "./bin/" directory.
(define (compile input-expr)
  (define asm-str (expr->asm input-expr))
  (define out-file (open-output-file "bin/r0func.s" #:exists 'replace))
  (display asm-str out-file)
  (close-output-port out-file)
  (system "make"))
;  (define r0prog-last-mod (file-or-directory-modify-seconds "bin/r0prog" #f (λ () 0)))
;  (define asm-last-mod (file-or-directory-modify-seconds "bin/r0func.s" #f (λ () 0)))
;  (unless (< asm-last-mod r0prog-last-mod)
;    (define asm-str (expr->asm input-expr))
;    (define out-file (open-output-file "bin/r0func.s" #:exists 'replace))
;    (display asm-str out-file)
;    (close-output-port out-file))
  
  

;; Runs the current program, optionally taking an input string to send the
;; program as standard input.
(define (run #:in [in-str ""])
  (match-define-values
   (sp stdout stdin #f)
   (subprocess #f #f 'stdout "./bin/r0prog"))
  (thread (λ ()
            (display in-str stdin)
            (close-output-port stdin)))
  (subprocess-wait sp)
  (define st (subprocess-status sp))
  (cond
    [(= 1 st)
     (error (read-line stdout))]
    [(not (zero? st))
     (error "r0 program failed with exit status:" st)]
    [else
     (define a (read stdout))
     (close-input-port stdout)
     a]))

;; Shorthand for compiling and running an expression, optionally with input.
(define (compile/run expr #:in [in-str ""])
  (unless (not (compile expr))
    (run #:in in-str)))
  
               
;;;
;;; TESTS
;;;

(define (r0-eval expr #:in [input ""])
  (define e
    `(let ([read
            (let ([read-stream (open-input-string ,input)])
              (λ () (read read-stream)))])
       ,expr))
  (eval e))

(define (expected? expr #:in [in-str ""])
  (define eval-res (r0-eval expr #:in in-str))
  (define asm-res (compile/run expr #:in in-str))
  (equal? eval-res asm-res))

(struct test-case (expr result in-str) #:transparent)

(define (tc expr result [in-str ""])
  (test-case expr result in-str))

(define (run-test tst)
  (match-define (test-case expr result in-str) tst)
  (equal? (compile/run expr #:in in-str) result))

(define test-cases
  (list
   (tc #t #t)
   (tc #f #f)
   (tc 0 0)
   (tc '(+ 1 2) 3)
   (tc '(- 5) -5)
   ))

(define (run-all-tests)
  (for-each
   (λ (t)
     (match-define (test-case expr result in-str) t)
     (define expr-res (compile/run expr #:in in-str))
     (unless (equal? expr-res result)
       (display
        (format "Test for ~a failed with value ~a (expected ~a)\n"
                expr expr-res result) 
        (current-error-port))))
   test-cases))


#;
(define test-expr
  '(let ([v 1] [w 46])
     (let ([x (+ v 7)])
       (let ([y (+ 4 x)] [z (+ x w)])
         (+ z (- y))))))

#;
(define test-expr
  '(let ([x 1] [y 2])
     (+ x y)))

#;
(define test-expr
  '(let ([x (+ 2 3)] [y (- 5)] [a 55])
     (let ([x (- x y)] [z (+ x y)])
       (let ([w (+ z x)])
         (+ w (- x (+ a 2)))))))

#;
(define test-expr
  '(let ([a (read)] [b (read)] [c (read)] [d (read)])
     (+ a (+ b (+ c d)))))

#;
(define test-expr
  '(let ([a (read)] [b (read)])
     (+ a b)))

#;
(define test-expr
  '(if (let ([x 5] [y 4]) (> x y)) 42 90))

#;
(define test-expr
  '(= 3 (- 4 1)))

#;
(define test-expr
  '(let ([x (+ 2 3)] [y (- 5)] [a 55])
     (let ([x (- x y)] [z (+ x y)])
       (let ([w (if (< x z) (+ 5 z) (- x (+ y 5)))])
         (+ w (- x (+ a 2)))))))

#;
(define test-expr
  '(if (<= 1 2) (+ 1 2) (- 3 2)))

#;
(define test-expr
  '(let ([a (read)] [b (read)])
     (if (= a b)
         123456
         (if (< a b)
             (- b a)
             (- a b)))))

(define test-expr
  '(let ([a 5] [b (= 3 3)])
     (if b a 3)))

#;
(define test-expr
  '(if (= (read) (read))
       123456
       (+ 2 3)))

#;
(define test-expr
  '(let ([a 5] [b 10])
     (if (> a b)
         a
         b)))

#;
(define test-expr
  '(vector-ref (vector-ref (vector (vector 42)) 0) 0))


;(lower-conds (assign-homes (uncover-live (select-insts (flatten-code (uniquify test-expr))))))
;(uncover-live (select-insts (flatten-code (uniquify test-expr))))
;(newline)
;(display (expr->asm test-expr))

;(select-insts (flatten-code (uniquify test-expr)))
;(newline)(newline)
;(uncover-live (select-insts (flatten-code (uniquify test-expr))))


(expose-alloc (typeof (uniquify test-expr)))


(flatten-code (expose-alloc (typeof (uniquify test-expr))))


#;
(compile/run test-expr #:in "")
