#lang racket/base

(require
  (for-syntax racket/base)
  racket/contract/base
  racket/contract/region
  racket/list
  racket/match
  racket/port
  racket/set
  racket/string
  racket/system
  syntax/parse/define
  graph
  "types.rkt"
  "uniquify.rkt"
  "typeof.rkt"
  "flatten.rkt"
  "expose.rkt"
  "select-insts.rkt"
  "replace-syntax.rkt"
  "uncover-live.rkt")

(define-simple-macro (for/filter (v:id lst:expr) when:expr ...+)
  (for/list ([v lst] #:when (let () when ...)) v))

;;;
;;; build-interference
;;;
;; Note: %rax omitted because it's used by compiler as scratch.
(define caller-saved (map reg '(rcx rdx rdi rsi r8 r9 r10 r11)))
(define callee-saved (map reg '(rbx r12 r13 r14 r15)))

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
  #(rbx r12 r13 r14 ;; callee-saved
        rcx rdx rdi rsi r8 r9 r10 r11 ;; caller-saved
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

  (when (verbose-output?)
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
             ;; call inst
             [(unary-inst 'call name)
              ; live values which are of type vector
              (define live-vecs
                (if (equal? name "gc_collect")
                    (set-intersect
                     (set-union caller-saved callee-saved)
                     (map get-var-home
                          (for/filter (v l-after)
                            (vector-ty? (hash-ref vars (var-name v))))))
                    empty))
              ; live values of non-vector type
              (define lives
                (set-subtract
                 (set-intersect (map get-var-home l-after) caller-saved)
                 live-vecs))
              ; add push/pops for live registers to call inst.
              (list
               (if (empty? live-vecs) empty
                   (list
                    (binary-inst 'add (int (* ptr-size (length live-vecs))) (reg 'r15))
                    (for/list ([idx (range (length live-vecs))])
                      (binary-inst 'mov
                                   (list-ref live-vecs idx)
                                   (deref 'r15 (- (* ptr-size (add1 idx))))))))
               (for/list ([var lives]) (unary-inst 'push var))
               (if (odd? (length lives))
                   (list
                    (binary-inst 'sub (int ptr-size) (reg 'rsp))
                    inst
                    (binary-inst 'add (int ptr-size) (reg 'rsp)))
                   inst)
               (reverse (for/list ([var lives]) (unary-inst 'pop var)))
               (if (empty? live-vecs) empty
                   (list
                    (for/list ([idx (reverse (range (length live-vecs)))])
                      (binary-inst 'mov
                                   (deref 'r15 (- (* ptr-size (add1 idx))))
                                   (list-ref live-vecs idx)))
                    (binary-inst 'sub (int (* ptr-size (length live-vecs))) (reg 'r15)))))]
             ;; other unary insts
             [(unary-inst op arg)
              (unary-inst op (get-var-home arg))]
             ;; binary inst
             [(binary-inst op src dest)
              (binary-inst op (get-var-home src) (get-var-home dest))]
             ;; if statement
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
      [(binary-inst op (? (or/c deref? global?) src) (? (or/c deref? global?) dest))
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
(define current-use-underscore?
  (make-parameter (eq? (system-type 'os) 'macosx)))

(define (fmt-asm op . args)
  (string-append "\t" op "\t" (string-join args ", ") "\n"))

(define (fmt-label label-name)
  (define func-prefix (if (current-use-underscore?) "_" ""))
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
     (fmt-label str)]
    [(global name)
     (format "~a(%rip)" (fmt-label name))]))

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
    ['Boolean 2]
    ;; TODO: proper vector printing
    [(? vector-ty?) 1]))

(define (print-asm xxprog ty)
  (define stack-size (xxprogram-stack-size xxprog))
  (define insts (xxprogram-insts xxprog))
  (define r0func-name (fmt-label "r0func"))
  (define ty_void (fmt-label "ty_void"))
  (define ty_integer (fmt-label "ty_integer"))
  (define ty_boolean (fmt-label "ty_boolean"))
  (define ty_vector (fmt-label "ty_vector"))

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

  (define callee-prefix
    (apply
     string-append
     (map
      (λ (reg) (fmt-asm "pushq" (arg->asm reg)))
      callee-saved)))

  (define rootstack-prefix
    (inst->asm (binary-inst 'mov (global "rootstack_begin") (reg 'r15))))
          
  (define print-call
    (string-append
     (fmt-asm "movq" "%rax" "%rdi")
     (fmt-asm "movq" (int->asm (type->int ty)) "%rsi")
     (fmt-asm "callq" (fmt-label "write_any"))))

  (define callee-suffix
    (apply
     string-append
     (map
      (λ (reg) (fmt-asm "popq" (arg->asm reg)))
      (reverse callee-saved))))
  
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
     callee-prefix
     rootstack-prefix
     (apply string-append (map inst->asm insts))
     print-call
     callee-suffix
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
  (unless (directory-exists? "./bin")
    (make-directory "./bin"))
  (define out-file (open-output-file "bin/r0func.s" #:exists 'replace))
  (display asm-str out-file)
  (close-output-port out-file)
  (parameterize ([current-output-port (open-output-nowhere)])
    (system "make")))
  

;; Runs the current program, optionally taking an input string to send the
;; program as standard input.
(define (run #:args [args empty] #:in [in-str ""])
  (define-values (sp stdout stdin stderr)
    (apply subprocess #f #f #f "./bin/r0prog" args))
  (thread (λ ()
            (display in-str stdin)
            (close-output-port stdin)))
  (subprocess-wait sp)
  (define st (subprocess-status sp))
  (unless (zero? st)
    (displayln (port->string stderr #:close? #f) (current-error-port))
    (eprintf "r0 program failed with exit status: ~a\n" st))
  (close-input-port stderr)
  (define a (read stdout))
  (close-input-port stdout)
  a)

;; Shorthand for compiling and running an expression, optionally with input.
(define (compile/run expr #:in [in-str ""] . cl-args)
  (unless (not (compile expr))
    (apply run cl-args #:in in-str)))
  
               
;;;
;;; TESTS
;;;
(module+ test
  (require chk)
  ;; Basic namespace for r0-eval.
  (define r0-ns (make-base-namespace))
  ;; Used to get an "expected" result for test expressions. This relies on the
  ;; fact that r0 syntax is a strict subset of Racket.
  (define (r0-eval expr #:in [input ""])
    (parameterize ([current-input-port (open-input-string input)])
      (eval expr r0-ns)))
  ;; Runs a test and complains if its output doesn't match the expected.
  (define/contract (go* args in-str exp)
    ((listof string?) string? any/c . -> . void?)
    (compile exp)
    (define-values (sp stdout stdin stderr)
      (apply subprocess #f #f #f "./bin/r0prog" args))
    (thread (λ ()
              (display in-str stdin)
              (close-output-port stdin)))
    (subprocess-wait sp)
    (define st (subprocess-status sp))
    (unless (zero? st)
      (displayln (port->string stderr #:close? #f) (current-error-port))
      (eprintf "r0 program failed with exit status: ~a\n" st))
    (close-input-port stderr)
    (with-chk (['source exp]
               ['register-max (current-register-max)])
      (chk*
       (chk #:? zero? st)
       (define a (read stdout))
       (define a-val (if (eof-object? a) (void) a))
       (chk #:eq equal? a-val (r0-eval exp #:in in-str))))
    (close-input-port stdout))
  ;; Macro so the test cases don't need to all be quoted (yawn).
  (define-syntax (go stx)
    (syntax-parse stx
      [(_ (~optional (~seq #:in in-str:expr) #:defaults ([in-str #'""]))
          (~optional (~seq #:args args:expr) #:defaults ([args #'empty]))
          e)
       #'(go* args in-str (quote e))]))
  ;; Runs all the tests.
  (define (run-all) 
    (go #t)
    (go #f)
    (go 0)
    (go 1)
    (go -1)
    (go (void))
    (go (+ 2 3))
    (go (- 1))
    (go #:in "40" (read))
    (go (+ 21 55))
    (go #:in "20 4" (+ (read) (read)))
    (go (- 128 12))
    (go (let ([x 5] [y 6]) (+ x y)))
    (go #:in "5 6" (let ([x (read)] [y (read)]) (+ x y)))
    (go (= 0 0))
    (go (= 1 1))
    (go (= 5 40))
    (go (not #t))
    (go (not #f))
    (go (not (= 1 0)))
    (go (< 1 2))
    (go (< 2 1))
    (go (<= 1 2))
    (go (<= 2 2))
    (go (<= 2 1))
    (go (>= 1 2))
    (go (>= 2 2))
    (go (>= 2 1))
    (go (> 1 2))
    (go (< 1 2))
    (go (>= 1 2))
    (go (>= 2 2))
    (go (>= 2 1))
    (go (if #t 500 60))
    (go (if #f 120 6))
    (go (if (= 0 1) 50 1))
    (go (if (= 20 20) (+ 1 2) 4000))
    (go (if (let ([x 5] [y 4]) (> x y)) 42 90))
    (go #:in "20 100" (if (= (read) (read)) 1 2))
    (go (if (= (let ([x 5]) (+ x 0)) 5) (+ 2 3) (- 5)))
    (go (if (not (= 2 1)) (if (>= 4 5) 501 502) 503))
    (go #:in "5 5" (if (= (read) (read)) 123456 (+ 2 3)))
    (go #:in "5 10" (if (= (read) (read)) 123456 (+ 2 3)))
    (go #:in "2 10" (let ([a (read)] [b (read)]) (= a b)))
    (go (let ([x (+ 2 3)] [y (- 5)] [a 55])
          (let ([x (- x y)] [z (+ x y)])
            (let ([w (if (< x z) (+ 5 z) (- x (+ y 5)))])
              (+ w (- x (+ a 2)))))))
    (go (let ([v 1] [w 46])
          (let ([x (+ v 7)])
            (let ([y (+ 4 x)] [z (+ x w)])
              (+ z (- y))))))
    (go (let ([a 5] [b (= 3 3)]) (if b a 3)))
    (go (vector-ref (vector-ref (vector (vector 42)) 0) 0)))
  ;; Invoke the tests.
  (parameterize ([verbose-output? #f])
    (run-all)
    (parameterize ([current-register-max 0])
      (run-all))))

;; vector set test fails right now.
#;
(compile/run '(let ([v (vector 42)])
                (begin (vector-set! v 0 52)
                       (vector-ref v 0))))
