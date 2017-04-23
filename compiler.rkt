#lang racket

(require
  graph
  "types.rkt"
  "uniquify.rkt"
  "typeof.rkt"
  "flatten.rkt"
  "expose.rkt"
  "select-insts.rkt"
  "replace-syntax.rkt"
  "uncover-live.rkt")

;;;
;;; build-interference
;;;
;; Note: %rax omitted because it's used by compiler as scratch.
(define caller-saved (map reg '(rcx rdx rdi rsi r8 r9 r10 r11)))
(define callee-saved (map reg '(rbx rbp rsp r12 r13 r14 r15)))

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
        ;; move instruction
        [(binary-inst 'mov src (? var? dest))
         (for ([var l-after])
           (unless (or (equal? var dest) (equal? var src))
             (add-edge! graph dest var)))]
        ;; all other binary-instructions
        [(binary-inst op src (? var? dest))
         (for ([var l-after])
           (unless (equal? var dest)
             (add-edge! graph var dest)))]
        ;; function call
        #;[(unary-inst 'call (? string? label))
         ;; always interfere with caller-saves
         (for ([var l-after])
           (for ([reg caller-saved])
             (add-edge! graph reg var)))
         ;; if collecting garbage, vectors interfere with callee-saves
         (unless (not (equal? label "gc_collect"))
           (for ([var l-after])
             (unless (not (vector-ty? (hash-ref vars (var-name var))))
               (for ([reg callee-saved])
                 (add-edge! graph reg var)))))]
        ;; if statement
        [(if-stmt/lives cond then then-lives ow ow-lives)
         (begin
           (build-inter then then-lives)
           (build-inter ow ow-lives)
           (void))]
        [else (void)])))
  
  graph)

(struct xxprogram (stack-size insts) #:transparent)

;; note: r15 is used for root stack, not for allocation
(define alloc-registers
  #(rbx rdi rsi r12 r13 r14 ;; callee-saved
        rcx rdx r8 r9 r10 r11 ;; caller-saved
        ))

(define current-register-max
  (make-parameter (vector-length alloc-registers)))

(define verbose-output?
  (make-parameter #t))

;;;
;;; assign-homes
;;;
(define (assign-homes xprog)  
  (match-define (xprogram vars insts l-afters) xprog)
  (define interference (build-interference xprog))
  (define num-valid-registers
    (min (current-register-max) (vector-length alloc-registers)))

  (define (color->home color)
    (if (< color num-valid-registers)
        (reg (vector-ref alloc-registers color))
        (deref 'rbp (- (* ptr-size (add1 (- color num-valid-registers)))))))
  
  (define-values (num-colors colorings)
    (coloring/greedy interference))

  ;; if num-colors is zero (no interference) and num-valid-registers is
  ;; zero, then assume 1 spill because the graph library can't tell the
  ;; difference between zero variables and 1 variable.
  (define spill-count
    (if (and (zero? num-colors) (zero? num-valid-registers))
        1
        (max 0 (- num-colors num-valid-registers))))

  (define stack-size
    (* ptr-size (if (even? spill-count)
                    spill-count
                    (add1 spill-count))))

;  (displayln colorings)
;  (newline)
;  (displayln
;   (filter
;    (λ (p) (var? (car p)))
;    (hash->list colorings)))

  (unless (not (verbose-output?))
    (displayln (format "num colors: ~a" num-colors))
    (displayln (format "spill count: ~a" spill-count))
    (displayln (format "stack size: ~a" stack-size)))
  
  (define (get-var-home tok)
    (if (var? tok)
        ;; defaults to zero b/c colorings will be empty in case of no interference.
        (color->home (hash-ref colorings tok 0))
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
             [(unary-inst 'call name)
              ; live values which are of type vector
              (define live-vecs
                (if (equal? name "gc_collect")
                    (set-intersect
                     (set-union caller-saved callee-saved)
                     (map get-var-home
                          (filter (λ (v) (vector-ty? (hash-ref vars (var-name v))))
                                  l-after)))
                    empty))
              ; live values of non-vector type
              (define lives
                (set-subtract
                 live-vecs
                 (set-intersect (map get-var-home l-after) caller-saved)))
              ; add push/pops for live registers to call inst.
              (list
               (if (empty? live-vecs) empty
                   (list
                    (binary-inst 'add (int (* ptr-size (length live-vecs))) (reg 'r15))
                    (map (λ (idx) (binary-inst 'mov
                                               (list-ref live-vecs idx)
                                               (deref 'r15 (- (* ptr-size (add1 idx))))))
                         (range (length live-vecs)))))
               (map (λ (var) (unary-inst 'push var)) lives)
               (if (odd? (length lives))
                   (list
                    (binary-inst 'sub (int ptr-size) (reg 'rsp))
                    inst
                    (binary-inst 'add (int ptr-size) (reg 'rsp)))
                   inst)
               (foldl (λ (var lst) (cons (unary-inst 'pop var) lst)) empty lives)
               (if (empty? live-vecs) empty
                   (list
                    (map (λ (idx) (binary-inst 'mov
                                               (deref 'r15 (- (* ptr-size (add1 idx))))
                                               (list-ref live-vecs idx)))
                         (reverse (range (length live-vecs))))
                    (binary-inst 'sub (int (* ptr-size (length live-vecs))) (reg 'r15)))))]
             [(unary-inst op arg)
              (unary-inst op (get-var-home arg))]
             [(binary-inst op src dest)
              (binary-inst op (get-var-home src) (get-var-home dest))]
             [(if-stmt/lives `(,cond-op ,L ,R) then then-afters ow ow-afters)
              (if-stmt `(,cond-op ,(get-var-home L) ,(get-var-home R))
                       (assign-homes then then-afters)
                       (assign-homes ow ow-afters))])
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
      ;; memory cannot be deref'd twice in the same instruction
      [(binary-inst op (? deref? src) (? deref? dest))
       (list (binary-inst 'mov src (reg 'rax))
             (binary-inst op (reg 'rax) dest))]
      ;; remove trivial moves
      [(binary-inst 'mov src dest)
       (if (equal? src dest)
           empty
           inst)]
      ;; cmp instruction can't have literals as second arg
      [(binary-inst 'cmp arg1 (? int? arg2))
       (list (binary-inst 'mov arg2 (reg 'rax))
             (binary-inst 'cmp arg1 (reg 'rax)))]
      ;; set instruction can only reference 8-bit registers
      [(unary-inst `(set ,op) dest)
       (list (unary-inst `(set ,op) (reg 'al))
             (if (deref? dest)
                 (list (binary-inst 'movzb (reg 'al) (reg 'rax))
                       (binary-inst 'mov (reg 'rax) dest))
                 (binary-inst 'movzb (reg 'al) dest)))]
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
  (define typed-expr (expose-alloc (typeof u-expr)))
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
  (parameterize ([current-output-port (open-output-nowhere)])
    (system "make")))
  

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

; namespace anchor
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
    (if (let ([x 5] [y 4]) (> x y)) 42 90)
    ,(tc '(if (= (read) (read)) 1 2) "20 100")
    (if (= (let ([x 5]) (+ x 0)) 5) (+ 2 3) (- 5))
    (if (not (= 50 1)) 2 3)
    (if (not (= 2 1)) (if (>= 4 5) 501 502) 503)
    ,(tc '(if (= (read) (read)) 123456 (+ 2 3)) "5 5")
    ,(tc '(if (= (read) (read)) 123456 (+ 2 3)) "5 10")
    ,(tc '(let ([a (read)] [b (read)]) (= a b)) "2 10")
    (let ([x (+ 2 3)] [y (- 5)] [a 55])
      (let ([x (- x y)] [z (+ x y)])
        (let ([w (if (< x z) (+ 5 z) (- x (+ y 5)))])
          (+ w (- x (+ a 2))))))
    (let ([v 1] [w 46])
      (let ([x (+ v 7)])
        (let ([y (+ 4 x)] [z (+ x w)])
          (+ z (- y)))))
    (let ([a 5] [b (= 3 3)])
      (if b a 3))
    ))

(define (run-all-tests)
  (for-each
   (λ (test)
     (displayln test)
     (match test
       [(tc expr in-str)
        (unless (expected? expr #:in in-str)
          (displayln (format "failed test: ~a with input: ~a" expr in-str) (current-error-port)))]
       [_
        (unless (expected? test)
          (displayln (format "failed test: ~a" test) (current-error-port)))])
     (newline))
   test-cases))


(run-all-tests)
#;
(parameterize ([current-register-max 0])
  (run-all-tests))



(define test-expr
  '(vector-ref (vector-ref (vector (vector 42)) 0) 0))
#;
(define test-expr '(vector 42 43))



(define u-expr (uniquify (replace-syntax test-expr)))
(define typed-expr (expose-alloc (typeof u-expr)))
(define return-type (ht-T typed-expr))
(assign-homes (uncover-live (select-insts (flatten-code typed-expr))))
