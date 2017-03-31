#lang racket

(require graph)

(define (replace-syntax expr)
  (define r replace-syntax)
  (define (var-args-op? op)
    (set-member? '(+ - * or and) op))
  (match expr
    ; not
    [`(not ,arg)
     `(if ,(r arg) #f #t)]
    ; or
    [`(or ,arg1 ,arg2)
     `(let ([or.tmp ,(r arg1)])
        (if or.tmp or.tmp ,(r arg2)))]
    ; and
    [`(and ,arg1 ,arg2)
     `(if ,(r arg1) ,(r arg2) #f)]
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

;; Defines types for use in validating program integrity.
(define Integer 'Integer)
(define Boolean 'Boolean)

;(struct ht (type val) #:transparent)
;
;(struct typed-expr (type env expr) #:transparent)
;
;
;(define (typeof- expr)
;
;  (define (fmt-type-error arg expected-type expr)
;    (format "typeof: Invalid argument '~a' (expected ~a) in expr: ~a"
;            arg expected-type expr))
;  
;  (let typeof ([expr expr] [env #hash()])
;    (match expr
;      [(? integer?)
;       (ht Integer expr)]
;      [(? boolean?)
;       (ht Boolean expr)]
;      [(? symbol?)
;       ; crash if symbol doesn't exist in environment.
;       (ht (hash-ref env expr) expr)]
;      [`(read)
;       (ht Integer expr)]
;      [`(not ,arg)
;       (define arg-t (typeof arg env))
;       (unless (eq? Boolean (ht-type arg-t))
;         (error (fmt-type-error arg Boolean expr)))
;       arg-t]
;      ; boolean comparison
;      [`(,(? boolean-op? op) ,args ...)
;       (define args-t
;         (map
;          (λ (arg)
;            (define arg-t (typeof arg env))
;            (unless (eq? Integer (ht-type arg-t))
;              (error (fmt-type-error arg Integer expr)))
;            arg-t)
;          args))
;       (ht Boolean (cons op args-t))]
;      ; arithmetic expression
;      [`(,(? arith-op? op) ,args ...)
;       (define args-t
;         (map
;          (λ (arg)
;            (define arg-t (typeof arg env))
;            (unless (eq? Integer (ht-type arg-t))
;              (error (fmt-type-error arg Integer expr)))
;            arg-t)
;          args))
;       (ht Integer (cons op args-t))]
;      ; if expression
;      [`(if ,cond ,then ,otherwise)
;       (define cond-t (typeof cond env))
;       (unless (eq? Boolean (ht-type cond-t))
;         (error (fmt-type-error cond Boolean expr)))
;       (define then-t (typeof then env))
;       (define otherwise-t (typeof otherwise env))
;       (unless (eq? (ht-type then-t) (ht-type otherwise-t))
;         (error (format "'~a' and '~a' mismatch types in expr: ~a"
;                        then otherwise expr)))
;       (ht (ht-type then-t) `(if ,cond-t then-t otherwise-t))]
;      ; let statement
;      [`(let (,(? let-var? vars) ...) ,subexpr)
;       (error "let: coming soon!")]
;      [_ (error "typeof: Invalid expr:" expr)])))
       


;;;
;;; typeof: Returns the type of any well-formed expression.
;;;
(define (typeof expr)
  (let typeof ([expr expr] [env #hash()])
    (match expr
      [(? integer?) Integer]
      [(? boolean?) Boolean]
      ;; crash if symbol doesn't exist in environment.
      [(? symbol?) (hash-ref env expr)] 
      [`(read) Integer]
      [`(not ,arg)
       (unless (eq? (typeof arg env) Boolean)
         (error (string-append "typeof: Invalid argument (expected Boolean) '" (~a arg) "' in expr: " (~a expr))))
       Boolean]
      ;; boolean comparison
      [`(,(? boolean-op?) ,args ...)
       (for-each
        (λ (arg)
          (unless (eq? (typeof arg env) Integer)
            (error (string-append "typeof: Invalid argument (expected Integer) '" (~a arg) "' in expr: " (~a expr)))))
        args)
       Boolean]
      ;; arithmetic statement
      [`(,(? arith-op?) ,args ...)
       (for-each
        (λ (arg)
          (unless (eq? (typeof arg env) Integer)
            (error (string-append "typeof: Invalid argument (expected Integer) '" (~a arg) "' in expr: " (~a expr)))))
        args)
       Integer]
      ;; if statement
      [`(if ,cond ,then ,otherwise)
       (unless (eq? (typeof cond env) Boolean)
         (error (string-append "typeof: Invalid conditional (expected Boolean) '" (~a cond) "' in expr: " (~a expr))))
       (define then-type (typeof then env))
       (unless (eq? then-type (typeof otherwise env))
         (error (string-append "typeof: Conditional statements '" (~a then) "' and '"
                               (~a otherwise) "' mismatch types in expr: " (~a expr))))
       then-type]
      ;; let statement
      [`(let (,(? let-var? vars) ...) ,subexpr)
       (define next-env
         (for/fold ([table env]) ([var vars])
           (define name (first var))
           (define var-expr (second var))
           (hash-set table name (typeof var-expr env))))
       (typeof subexpr next-env)]
      [_ (error "typeof: Invalid expr:" expr)])))


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
      [(? integer?) (program empty (list (return-stmt expr)))]
      ;; converts #t and #f to integer 1/0.
      [(? boolean?) (program empty (list (return-stmt (if expr 1 0))))]
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
       (match-define (program (list cond-vars ...) (list cond-stmts ... (return-stmt cond-ans)))
         (flatten-code cond vartab))
       (match-define (program (list then-vars ...) (list then-stmts ... (return-stmt then-ans)))
         (flatten-code then vartab))
       (match-define (program (list otherwise-vars ...) (list otherwise-stmts ... (return-stmt otherwise-ans)))
         (flatten-code otherwise vartab))
       (define dest-name (next-tmp-name))
       (program (set-union cond-vars then-vars otherwise-vars (list dest-name))
                (append cond-stmts
                        (list (if-stmt
                               (return-stmt cond-ans) ; note cond is not a list of statements
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

(struct if-inst (cond then thn-lives otherwise ow-lives) #:transparent)

(struct label (name) #:transparent)

(struct xprogram (vars insts live-afters) #:transparent)

;;;
;;; select-insts
(define (select-insts prog)

  (define get-next-label
    (let ([next-label -1])
      (λ ()
        (set! next-label (add1 next-label))
        (string-append "r0L" (number->string next-label)))))

  (define (arg->val arg)
    (match arg
      [(? integer?) (int arg)]
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
          (list (binary-inst 'cmp (arg->val arg2) (arg->val arg1))
                (unary-inst `(set ,op) (var dest)))]
         ['read
          (list (unary-inst 'call "read_int")
                (binary-inst 'mov (reg 'rax) (var dest)))]
         [(? symbol?)
          (binary-inst 'mov (var src-expr) (var dest))]
         [(? integer?)
          (binary-inst 'mov (var src-expr) (var dest))])]
      [(if-stmt (return-stmt cond-ans) then-stmts otherwise-stmts)
       (if-stmt
        ; note: cond is just a value which will be compared with #t when the if-stmt is lowered
        cond-ans
        ; then
        (flatten (map stmt->insts then-stmts))
        ; otherwise
        (flatten (map stmt->insts otherwise-stmts)))]
      [(return-stmt src-val)
       (binary-inst 'mov (arg->val src-val) (reg 'rax))]))
  
  (xprogram (program-vars prog) (flatten (map stmt->insts (program-stmts prog))) empty))

;(struct inst-lst (insts l-afters) #:transparent)
;
;(struct il (insts afters) #:transparent)
;
;(struct if-afters (if then ow) #:transparent)
;
;(struct ha (inst l-after) #:transparent)

;;;
;;; uncover-live
;;;
(define (uncover-live xprog)
  (match-define (xprogram vars all-insts emtpy) xprog)

  (define (move-inst? op)
    (set-member? '(mov movzb) op))
  
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

  (define-values (insts l-afters)
    (for/fold ([insts empty]
               [l-afters (list empty)])
              ([inst (reverse (rest all-insts))])
      (define l-after (first l-afters))
      (define l-before
        (set-union (set-subtract l-after (get-writes inst))
                   (get-reads inst)))
      (values
       (cons inst insts)
       (cons l-before l-afters))))

  ;; add first inst back to insts before returning
  (xprogram vars (cons (first all-insts) insts) l-afters))


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
  
  (for ([inst insts] [l-after live-afters])
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
      [_ void]))

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
  
  (match-define (xprogram vars insts liveness) xprog)

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
    (flatten
     (reverse
      (for/fold ([out empty])
                ([inst insts] [l-afters liveness])
        (cons
         (match inst
           [(unary-inst 'call func)
            (define lives (set-intersect (map get-var-home l-afters) (map reg caller-saved)))
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
           [(if-stmt cond-var then ow)
            (display (third l-afters))
            (error "coming soon!")]
           )
         out)))))

  (xxprogram stack-size home-insts))

;;;
;;; patch-insts
;;;
(define (patch-insts xxprog)

  (match-define (xxprogram stack-size insts) xxprog)

  (define (patch inst)
    (match inst
      ;; remove trivial moves
      [(binary-inst 'mov (? reg? src) (? reg? dest))
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
  (match op
    ['neg "negq"]
    ['mov "movq"]
    ['add "addq"]
    ['sub "subq"]
    ['mul "imulq"]
    ['div "idivq"]
    ['call "callq"]
    #;['ret "ret"] ; TODO: is this even right?
    ['pop "popq"]
    ['push "pushq"]
    ['xor "xorq"]
    ['cmp "cmpq"]
    ['movzb "movzbq"]
    ['jmp "jmpq"]
    [`(set ,bool-op)
     (string-append "set" (op->cc bool-op))]
    [`(jmp-if ,bool-op)
     (string-append "j" (op->cc bool-op))]
    ))

(define (arg->asm arg)
  (match arg
    [(int n) (int->asm n)]
    [(reg r) (string-append "%" (symbol->string r))]
    [(deref r offset) (string-append (if (= offset 0) "" (number->string offset)) "(%" (symbol->string r) ")")]
    [(? string? str) (fmt-funcname str)]))

(define (inst->asm inst)
  (match inst
    [(unary-inst op arg) (fmt-asm (op->asm op) (arg->asm arg))]
    [(binary-inst op src dest) (fmt-asm (op->asm op) (arg->asm src) (arg->asm dest))]))

(define (print-asm xxprog)
  (define stack-size (xxprogram-stack-size xxprog))
  (define insts (xxprogram-insts xxprog))
  (define r0func-name (fmt-funcname "r0func"))

  (define asm-prefix (string-append "\t.text\n\t.globl " r0func-name "\n" r0func-name ":\n"))

  (define stack-prefix (string-append (fmt-asm "pushq" "%rbp")
                                      (fmt-asm "movq" "%rsp" "%rbp")
                                      (if (= 0 stack-size) "" (fmt-asm "subq" (int->asm stack-size) "%rsp"))))

  (define stack-suffix (string-append (if (= 0 stack-size) "" (fmt-asm "addq" (int->asm stack-size) "%rsp"))
                                      (fmt-asm "popq" "%rbp")))

  (define main-return (fmt-asm "retq"))

  (define final-asm
    (string-append asm-prefix stack-prefix (apply string-append (map inst->asm insts)) stack-suffix main-return))

  final-asm)

;;;
;;; Utils for compiling and runnings ASM code
;;;
(define (expr->asm expr)

  (define steps (list uniquify flatten-code select-insts uncover-live
                      assign-homes patch-insts print-asm))

  (for/fold ([prog expr])
            ([step steps])
    (call-with-values (λ () prog) step)))
  
;  (define xprog (uncover-live (select-insts (flatten-code (uniquify expr)))))
;  #;(define interference (build-interference xprog))
;  (print-asm (patch-insts (assign-homes xprog))))

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


(define test-expr
  '(if (let ([x 5] [y 4]) (> x y)) 42 90))

#;
(define test-expr
  '(= 3 (- 4 1)))

#;
(define test-expr
  '(let ([x (+ 2 3)] [y (- 5)] [a 55])
     (let ([x (- x y)] [z (+ x y)])
       (let ([w (if (< x z) (+ 5 z) (- x y))])
         (+ w (- x (+ a 2)))))))


(uncover-live (select-insts (flatten-code (uniquify test-expr))))


(compile-and-run test-expr)