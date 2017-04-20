#lang racket

(require
  racket/hash
  graph
  "types.rkt"
  "uniquify.rkt"
  "typeof.rkt"
  "flatten.rkt")

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


(struct int (val) #:transparent)

(struct var (name) #:transparent)

(struct reg (name) #:transparent)

(struct global (name) #:transparent)

(struct unary-inst (op arg) #:transparent)

(struct binary-inst (op src dest) #:transparent)

(struct xprogram (vars insts live-afters) #:transparent)

(define arg-registers (vector-map reg #(rdi rsi rdx rcx r8 r9)))

(define root-stack (reg 'r15))

;;;
;;; select-insts
;;;
(define (types->tag tys)
  ; tag:
  ; upper 5 bits are size (0 - 31) => (1 - 32).
  ; mid 27 bits are empty.
  ; lower 32 bits are the type tags.
  ; stores bits so that the lowest-order bit is the first type,
  ; 2nd-lowest-order bit is the 2nd type, etc.
  (unless (not (empty? tys))
    (error "Empty type list is not valid for a vector"))
  (define tag-bits
    (for/fold ([tag 0])
              ([ty (reverse tys)])
      (if (and (list? ty)
               (eq? (first ty) 'Vector))
          (add1 (arithmetic-shift tag 1))
          (arithmetic-shift tag 1))))
  (bitwise-ior (arithmetic-shift (sub1 (length tys)) 59)
               tag-bits))

;; select-insts
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

;  (define SIZE-MASK (arithmetic-shift (string->number "11111" 2) 59))
;  (define TAGS-MASK (sub1 (expt 2 32)))
  
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
         [`(allocate ,tys ...)
          (list (binary-inst 'mov (global "free_ptr") (arg->val dest))
                (binary-inst 'add (* ptr-size (add1 (length tys))) (global "free_ptr"))
                (binary-inst 'mov (arg->val dest) (reg 'rax))
                (binary-inst 'mov (int (types->tag tys)) (deref 'rax 0)))]
         [`(collect ,bytes)
          (list (binary-inst 'mov root-stack (vector-ref arg-registers 0))
                (binary-inst 'mov (int bytes) (vector-ref arg-registers 1))
                (unary-inst 'call "gc_collect"))]
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
  
  (xprogram hash-vars (flatten (map stmt->insts stmts)) empty))


;;;
;;; uncover-live
;;;
(struct if-stmt/lives (cond then then-lives ow ow-lives) #:transparent)

(define (uncover-live xprog)
  (match-define (xprogram vars all-insts emtpy) xprog)
  
  (define (move-inst? op)
    (set-member? '(mov movzb) op))
  
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
(define caller-saved '(rcx rdx rdi rsi r8 r9 r10 r11))
(define callee-saved '(rbx rbp rsp r12 r13 r14 r15))

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

;; note: r15 is used for root stack, not for allocation
(define alloc-registers
  #(rbx rdi rsi r12 r13 r14 ;; callee-saved
        rcx rdx r8 r9 r10 r11 ;; caller-saved
        ))

(define current-register-max
  (make-parameter (vector-length alloc-registers)))

;;;
;;; assign-homes
;;;
(define (assign-homes xprog)
  
  ;; TODO: diagnostic prints: keep or remove?
  
  (match-define (xprogram vars insts l-afters) xprog)
  
  (define interference (build-interference xprog))

  #;
  (define num-valid-registers (vector-length alloc-registers))

  (define num-valid-registers (current-register-max))
  
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
(define current-underscore-usage
  (make-parameter (eq? (system-type 'os) 'macosx)))

(define (fmt-asm op . args)
  (string-append "\t" op "\t" (string-join args ", ") "\n"))

(define (fmt-label label-name)
  (define func-prefix (if (current-underscore-usage) "_" ""))
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
     (fmt-asm "pushq" "%rdi")
     (fmt-asm "pushq" "%rsi")
     (fmt-asm "movq" "%rax" "%rdi")
     (fmt-asm "movq" (int->asm (type->int ty)) "%rsi")
     (fmt-asm "callq" (fmt-label "write_any"))
     (fmt-asm "popq" "%rsi")
     (fmt-asm "popq" "%rdi")))
  
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

;; namespace anchor
(define r0-ns (make-base-namespace))

(define (r0-eval expr #:in [input ""])
  (parameterize ([current-input-port (open-input-string input)])
    (eval expr r0-ns)))

(define (expected? expr #:in [in-str ""])
  (define eval-res (r0-eval expr #:in in-str))
  (define asm-res (compile/run expr #:in in-str))
  (equal? eval-res asm-res))

(struct tc (expr in-str) #:transparent)

(define test-cases
  `(#t
    #f
    0
    1
    -1
    (- 1)
    ,(tc '(read) "40")
    (+ 21 55)
    ,(tc '(+ (read) (read)) "20 4")
    (- 128 12)
    (let ([x 5] [y 6]) (+ x y))
    ,(tc '(let ([x (read)] [y (read)]) (+ x y)) "5 6")
    (= 0 0)
    (= 5 40)
    (not #t)
    (not #f)
    (not (= 1 0))
    (< 1 2)
    (< 2 1)
    (<= 1 2)
    (<= 2 2)
    (<= 2 1)
    (> 1 2)
    (> 2 1)
    (>= 1 2)
    (>= 1 1)
    (>= 2 1)
    (if #t 500 60)
    (if #f 120 6)
    (if (= 0 1) 50 1)
    (if (= 20 20) (+ 1 2) 4000)
    ,(tc '(if (= (read) (read)) 1 2) "20 100")
    (if (not (= 50 1)) 2 3)
    (if (not (= 2 1)) (if (>= 4 5) 501 502) 503)
    ,(tc '(if (= (read) (read)) 123456 (+ 2 3)) "5 5")
    ,(tc '(if (= (read) (read)) 123456 (+ 2 3)) "5 10")
    (let ([x (+ 2 3)] [y (- 5)] [a 55])
     (let ([x (- x y)] [z (+ x y)])
       (let ([w (if (< x z) (+ 5 z) (- x (+ y 5)))])
         (+ w (- x (+ a 2))))))
    ))

(define (run-all-tests)
  (for-each
   (λ (test)
     (display test) (newline)
     (match test
       [(tc expr in-str)
        (unless (expected? expr #:in in-str)
          (display (format "failed test: ~a with input: ~a\n" expr in-str)))]
       [_
        (unless (expected? test)
          (display (format "failed test: ~a\n" test)))]))
   test-cases))


(run-all-tests)

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

#;
(define test-expr
  '(let ([a (read)] [b (read)])
     (= a b)))

#;
(define test-expr
  '(let ([a 5] [b (= 3 3)])
     (if b a 3)))


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


;(define flat-code (flatten-code (expose-alloc (typeof (uniquify test-expr)))))
;flat-code
;(newline)
;(select-insts flat-code)


#;
(compile/run test-expr #:in "10 10")
