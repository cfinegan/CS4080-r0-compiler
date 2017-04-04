#lang racket

(require graph)

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

;; Returns true if argument is a list in the form expected by the let macro.
(define (let-var? v)
  (and (list? v) (= 2 (length v))))

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


;; Some basic sets outlining what operators are valid for what purposes.
(define (arith-op? op)
  (set-member? '(+ -) op))

(define (boolean-op? op)
  (set-member? '(= < > <= >=) op))

;;;
;;; typeof: Returns the type of any well-formed expression.
;;;
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

;;;
;;; expose allocation
;;;
; coming soon!

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
  
  ;; Should have the side effect of erroring if there are type errors in the program.
  (define expr-type (typeof expr))
  
  ;; Always returns the 'next' temporary name. Encapsulates mutable state.
  (define next-tmp-name
    (let ([next-id -1])
      (λ ()
        (set! next-id (add1 next-id))
        (string->symbol (string-append "tmp." (number->string next-id))))))
  
  ;; Self-executing closure around helper procedures prevents recursive calls to flatten-code
  ;; from resetting the tmp-name count.
  (let flatten-code ([expr expr] [vartab #hash()])
    (match expr
      [(? (or/c integer? boolean?))
       (program empty (list (return-stmt expr)))]
      [(? symbol?)
       (define name-ref (hash-ref vartab expr #f))
       (if name-ref
           (flatten-code name-ref vartab)
           (program (list expr) (list (return-stmt expr))))]
      ;; read expression
      [`(read)
       (define dest-name (next-tmp-name))
       (program (list dest-name) (list (assign-stmt 'read dest-name)
                                       (return-stmt dest-name)))]
      ;; let expression
      [`(let (,(? let-var? vars)...) ,subexpr)
       (define-values (next-vartab var-prog)
         (for/fold ([vartab vartab] [var-prog (program empty empty)])
                   ([var vars])
           (define var-name (first var))
           (define var-expr (second var))
           (match-define (program (list vars ...) (list stmts ... (return-stmt ans)))
             (flatten-code var-expr vartab))
           (values (hash-set vartab var-name ans)
                   (program (set-union (program-vars var-prog) vars)
                            (append (program-stmts var-prog) stmts)))))
       (define subexpr-prog (flatten-code subexpr next-vartab))
       (program (set-union (program-vars var-prog) (program-vars subexpr-prog))
                (append (program-stmts var-prog) (program-stmts subexpr-prog)))]
      ;; if expression
      [`(if ,cond ,then ,otherwise)       
       (define cond-expr
         (match cond
           [(? (or/c symbol? boolean?))
            ; literal is on RHS so that it will be on LHS in cmp operation.
            `(= ,(flatten-code cond vartab) ,(flatten-code 1 vartab))]
           [`(,op ,exp1 ,exp2)
            `(,op ,(flatten-code exp1 vartab) ,(flatten-code exp2 vartab))]))
       (match-define
         (list
          cond-op
          (program (list ce1-vars ...) (list ce1-stmts ... (return-stmt ce1-ans)))
          (program (list ce2-vars ...) (list ce2-stmts ... (return-stmt ce2-ans))))
         cond-expr)
       (match-define (program (list then-vars ...) (list then-stmts ... (return-stmt then-ans)))
         (flatten-code then vartab))
       (match-define (program (list otherwise-vars ...) (list otherwise-stmts ... (return-stmt otherwise-ans)))
         (flatten-code otherwise vartab))
       (define dest-name (next-tmp-name))
       (program (set-union ce1-vars ce2-vars then-vars otherwise-vars (list dest-name))
                (append ce1-stmts
                        ce2-stmts
                        (list (if-stmt
                               ;(return-stmt cond-ans) ; note cond is not a list of statements
                               `(,cond-op ,ce1-ans ,ce2-ans)
                               (append then-stmts (list (assign-stmt then-ans dest-name)))
                               (append otherwise-stmts (list (assign-stmt otherwise-ans dest-name))))
                              (return-stmt dest-name))))]
      ;; arithmetic negation / binary negation
      [`(,(? (λ (op) (or (eq? op '-) (eq? op 'not))) op) ,subexpr)
       (match-define (program (list vars ...)  (list stmts ... (return-stmt ans)))
         (flatten-code subexpr vartab))
       (define dest-name (next-tmp-name))
       (program (set-union (list dest-name) vars)
                (append stmts (list (assign-stmt `(,op ,ans) dest-name)
                                    (return-stmt dest-name))))]
      ;; binary arithmetic / boolean operators
      [`(,(? (or/c boolean-op? arith-op?) op) ,L ,R)
       (match-define (program (list L-vars ...) (list L-stmts ... (return-stmt L-ans)))
         (flatten-code L vartab))
       (match-define (program (list R-vars ...) (list R-stmts ... (return-stmt R-ans)))
         (flatten-code R vartab))
       (define dest-name (next-tmp-name))
       (program (filter symbol? (set-union L-vars R-vars (list L-ans R-ans dest-name)))
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
  
  (xprogram (program-vars prog) (flatten (map stmt->insts (program-stmts prog))) empty))


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
           void)]
        [_ void])))
  
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

(define (fmt-funcname func-name)
  (define func-prefix (if (eq? (system-type 'os) 'macosx) "_" ""))
  (string-append func-prefix func-name))

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
  (define op-str
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
  ; adds extra tab if the op name is too short
  (if (< (string-length op-str) 4)
      (string-append op-str "\t")
      op-str))

(define (arg->asm arg)
  (match arg
    [(int n) (int->asm n)]
    [(reg r) (string-append "%" (symbol->string r))]
    [(deref r offset) (string-append (if (zero? offset) "" (number->string offset)) "(%" (symbol->string r) ")")]
    [(? string? str) (fmt-funcname str)]))

(define (inst->asm inst)
  (match inst
    [(unary-inst op arg)
     (fmt-asm (op->asm op) (arg->asm arg))]
    [(binary-inst op src dest)
     (fmt-asm (op->asm op) (arg->asm src) (arg->asm dest))]
    [(label name)
     (format "~a:\n" name)]))

(define (print-asm xxprog)
  (define stack-size (xxprogram-stack-size xxprog))
  (define insts (xxprogram-insts xxprog))
  (define r0func-name (fmt-funcname "r0func"))
  
  (define asm-prefix (string-append "\t.text\n\t.globl " r0func-name "\n" r0func-name ":\n"))
  
  (define stack-prefix (string-append (fmt-asm "pushq" "%rbp")
                                      (fmt-asm "movq" "%rsp" "%rbp")
                                      (if (zero? stack-size) "" (fmt-asm "subq" (int->asm stack-size) "%rsp"))))
  
  (define stack-suffix (string-append (if (zero? stack-size) "" (fmt-asm "addq" (int->asm stack-size) "%rsp"))
                                      (fmt-asm "popq" "%rbp")))
  
  (define main-return (fmt-asm "retq"))
  
  (define final-asm
    (string-append asm-prefix stack-prefix (apply string-append (map inst->asm insts)) stack-suffix main-return))
  
  final-asm)

;;;
;;; Utils for compiling and runnings ASM code
;;;
(define (expr->asm expr)
  (define u-expr (uniquify (replace-syntax expr)))
  (define C-stmts (uncover-live (select-insts (flatten-code u-expr))))
  (define X-insts (patch-insts (lower-conds (assign-homes C-stmts))))
  (print-asm X-insts))

(define (compile-prog input-expr)
  (define asm-str (expr->asm input-expr))
  (define out-file (open-output-file "bin/r0func.s" #:exists 'replace))
  (display asm-str out-file)
  (close-output-port out-file)
  (system "make"))

(define (compile-and-run input-expr)
  (unless (not (compile-prog input-expr))
    (define exit-status
      (system/exit-code (if (eq? (system-type 'os) 'windows)
                            "bin\\r0prog"
                            "./bin/r0prog")))
    (unless (zero? exit-status)
      (error "program failed with exit status:" exit-status))))


;; TODO: Fix runtime.c to print output (instead of returning it from main) and turn this back on!
#;
(define (compile-and-run input-expr)
  
  (define exe-path (if (eq? (system-type 'os) 'windows)
                       "bin\\r0prog"
                       "./bin/r0prog"))
  
  (unless (not (compile-prog input-expr))
    (define-values (sub-proc stdout stdin stderr)
      (subprocess #f #f (current-error-port) (string->path exe-path)))
    (thread (λ ()
              (display "" stdin)
              (close-output-port stdin)))
    (subprocess-wait sub-proc)
    (define exit-status (subprocess-status sub-proc))
    (unless (zero? exit-status)
      (error "error running program:" exit-status))
    (define a (read stdout))
    (close-input-port stdout)
    a))

;;;
;;; TESTS
;;;

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


(define test-expr
  '(let ([a (read)] [b (read)])
     (if (= a b)
         123456
         (if (< a b)
             (- b a)
             (- a b)))))

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



(compile-and-run test-expr)