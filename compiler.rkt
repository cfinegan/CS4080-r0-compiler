#lang racket

(require graph)

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

  (define (let-var? v)
    (and (list? v) (= 2 (length v)) (symbol? (first v))))

  (define (unary-op? sym)
    (eq? sym '-))

  (define (binary-op? sym)
    (set-member? '(+ -) sym))

  (let uniquify ([expr expr] [symtab #hash()])
    (define (name? var)
      (hash-has-key? symtab var))
    
    (define (valid-arg? var)
      (or/c name? integer? list?))
    
    (match expr
      [(? integer? n) n]
      [(? symbol? sym) (render-name sym symtab)]
      ['(read) '(read)]
      [(list 'let (list (? let-var? vars) ...) subexpr)
       (define next-symtab (symtab-with-vars symtab vars (get-next-id)))
       (define (render-var var)
         (list (render-name (first var) next-symtab) (uniquify (second var) symtab)))
       (list 'let (map render-var vars) (uniquify subexpr next-symtab))]
      [(list (? unary-op? op) (? valid-arg? arg))
       (list op (uniquify arg symtab))]
      [(list (? binary-op? op) (? valid-arg? arg1) (? valid-arg? arg2))
       (list op (uniquify arg1 symtab) (uniquify arg2 symtab))]
      [_ (error "uniquify - invalid expr:" expr)])))


;; Creates a new return statement.
(struct return-stmt (arg) #:transparent)

;; Creates a new assignment statement.
(struct assign-stmt (src dest) #:transparent)

;; Creates a new program structure.
(struct program (vars stmts) #:transparent)

(struct unary-expr (op arg) #:transparent)

(struct binary-expr (op src dest) #:transparent)

(define (list->expr lst)
  (match lst
    [(list '- arg) (unary-expr 'neg arg)]
    [(list '+ arg1 arg2) (binary-expr 'add arg1 arg2)]
    [(list '- arg1 arg2) (binary-expr 'sub arg1 arg2)]
    #;[(list '* arg1 arg2) (binary-expr 'mul arg1 arg2)]
    #;[(list '/ arg1 arg2) (binary-expr 'div arg1 arg2)]
    [_ (error "invalid flattened exprssion:" lst)]))


;;;
;;; flatten-code
;;; Flattens an expression into a series of statements which only reference integers
;;; or variable names.
(define (flatten-code expr)
  
  ;; Always returns the 'next' temporary name. Encapsulates mutable state.
  (define next-tmp-name
    (let ([next-id -1])
      (λ ()
        (set! next-id (add1 next-id))
        (string->symbol (string-append "tmp." (number->string next-id))))))
  
  ;; Self-executing closure around helper procedures prevents recursive calls to flatten-code
  ;; from resetting the tmp-name count.
  (let flatten-code ([expr expr] [vartab #hash()])
    
    ;; Flattens an integer literal into a program that returns arg.
    (define (flatten-int arg)
      (program empty (list (return-stmt arg))))
    
    ;; Flattens a variable name into a program that declares that name and returns it.
    (define (flatten-var arg)
      (program (list arg) (list (return-stmt arg))))
    
    ;; Flattens a read expression into a program that assigns 'read to a variable and returns it.
    (define (flatten-read)
      (define dest-name (next-tmp-name))
      (program (list dest-name) (list (assign-stmt 'read dest-name)
                                      (return-stmt dest-name))))
    
    ;; Flattens a negation expression into a program that negates arg and returns it.
    (define (flatten-neg arg)
      (match-define (program (list vars ...) (list stmts ... (return-stmt ans))) (flatten-code arg vartab))
      (define dest-name (next-tmp-name))
      (program (set-union (list dest-name) vars)
               (append stmts (list (assign-stmt (unary-expr 'neg ans) dest-name)
                                   (return-stmt dest-name)))))
    
    ;; Flattens an arithmetic expression into a program that applies proc-naem to L and R, stores
    ;; the result in a variable, and returns it.
    (define (flatten-arith proc-name L R)
      (match-define (program (list L-vars ...) (list L-stmts ... (return-stmt L-ans))) (flatten-code L vartab))
      (match-define (program (list R-vars ...) (list R-stmts ... (return-stmt R-ans))) (flatten-code R vartab))
      (define dest-name (next-tmp-name))
      (program (filter symbol? (set-union L-vars R-vars (list L-ans R-ans dest-name)))
               (append L-stmts R-stmts (list (assign-stmt (list->expr (list proc-name L-ans R-ans)) dest-name)
                                             (return-stmt dest-name)))))
    
    ;; Flattens a let expression by breaking the var expressions into programs and appending them to subexpr.
    (define (flatten-let vars subexpr)
      
      (define-values (next-vartab var-prog)
        (for/fold ([vartab vartab] [var-prog (program empty empty)])
                  ([var vars])
          (define var-name (first var))
          (define var-expr (second var))
          (match-define (program (list vars ...) (list stmts ... (return-stmt ans))) (flatten-code var-expr vartab))
          (values (hash-set vartab var-name ans)
                  (program (set-union (program-vars var-prog) vars)
                           (append (program-stmts var-prog) stmts)))))
      
      (define subexpr-prog (flatten-code subexpr next-vartab))

      (program (set-union (program-vars var-prog) (program-vars subexpr-prog))
               (append (program-stmts var-prog) (program-stmts subexpr-prog))))

    
    ;; flatten-code procedure body.
    (cond [(integer? expr) (flatten-int expr)]
          [(symbol? expr)
           (define name-ref (hash-ref vartab expr #f))
           (if name-ref
               (flatten-code name-ref vartab)
               (flatten-var expr))]
           ;(flatten-var expr)]
          [(list? expr)
           (let ([proc (first expr)]
                 [args (rest expr)])
             (cond [(eq? proc 'read)
                    (flatten-read)]
                   [(eq? proc 'let)
                    (flatten-let (first args) (second args))]
                   [(and (eq? proc '-) (= (length args) 1))
                    (flatten-neg (first args))]
                   [(set-member? '(+ - * /) proc)
                    (flatten-arith proc (first args) (second args))]
                   [else (error "unrecognized procedure name:" proc)]))]
          [else (error "unrecognized expression:" expr)])))


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
    (cond [(integer? arg) (int arg)]
          [(symbol? arg) (var arg)]
          [else (error "invalid arg:" arg)]))

  (define (stmt->insts stmt)
    (match stmt
      [(assign-stmt src-expr (? symbol? dest))
       (match src-expr
         [(unary-expr op arg)
          (list (binary-inst 'mov (arg->val arg) (var dest))
                (unary-inst op (var dest)))]
         [(binary-expr op arg1 arg2)
          (list (binary-inst 'mov (arg->val arg1) (var dest))
                (binary-inst op (arg->val arg2) (var dest)))]
         ['read
          (list (unary-inst 'call "read_int")
                (binary-inst 'mov (reg 'rax) (var dest)))]
         [(? symbol? arg)
          (binary-inst 'mov (var arg) (var dest))]
         [(? integer? arg)
          (binary-inst 'mov (int arg) (var dest))])]
      [(return-stmt src-val)
       (binary-inst 'mov (arg->val src-val) (reg 'rax))]))
  
  (xprogram (program-vars prog) (flatten (map stmt->insts (program-stmts prog))) empty))


;;;
;;; uncover-live
;;;
(define (uncover-live xprog)

  (define (reads-dest? op)
    (not (eq? op 'mov)))
  
  (define drop1 rest)
  (define insts (xprogram-insts xprog))
  (define vars (xprogram-vars xprog))
  (define liveness
    (for/fold ([out (list empty)]) ([inst (reverse (drop1 insts))])
      (cons
       (filter
        var?
        (match inst
          [(unary-inst op arg)
           (set-union (first out) (list arg))]
          [(binary-inst op src dest)
           (if (reads-dest? op)
               (set-union (first out) (list src dest))
               (set-union (set-remove (first out) dest) (list src)))]))
       out)))
  (xprogram vars insts liveness))


;;;
;;; build-interference
;;;
(define (build-interference xprog)

  ; note: excluding %rax from caller-saved for now because it's used to special purposes.
  (define caller-saved '(rcx rdx r8 r9 r10 r11))
  (define callee-saved '(rbx rbp rdi rsi rsp r12 r13 r14 r15))
  
  (define vars (xprogram-vars xprog))
  (define insts (xprogram-insts xprog))
  (define live-afters (xprogram-live-afters xprog))

  (unless (= (length insts) (length live-afters))
    (error "insts and live-afters must have the same length"))

  (define graph (unweighted-graph/undirected empty))

  (for ([var vars])
    (add-vertex! graph var))
  (for ([reg caller-saved])
    (add-vertex! graph reg))
  (for ([reg callee-saved])
    (add-vertex! graph reg))

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

;;;
;;; assign-homes
(define (assign-homes xprog)
  
  (define var-count (length (xprogram-vars xprog)))
  (define stack-size (* ptr-size (if (even? var-count) var-count (add1 var-count))))
  
  (define var-homes
    (let map-homes ([vars (xprogram-vars xprog)] [index 0] [homes #hash()])
      (if (null? vars)
          homes
          (map-homes (rest vars) (add1 index) (hash-set homes (first vars) (- (* index ptr-size)))))))
  
  (define (var->deref arg)
    (if (var? arg)
        (deref 'rbp (hash-ref var-homes (var-name arg)))
        arg))

  (define (apply-deref inst)
    (match inst
      [(unary-inst op arg) (unary-inst op (var->deref arg))]
      [(binary-inst op src dest) (binary-inst op (var->deref src) (var->deref dest))]))
  
  (xxprogram stack-size (map apply-deref (xprogram-insts xprog))))


;;;
;;; patch-insts
;;;
(define (patch-insts xxprog)
  
  (define stack-size (xxprogram-stack-size xxprog))

  (define (patch inst)
    (match inst
      [(binary-inst op (? deref? src) (? deref? dest))
       (list (binary-inst 'mov src (reg 'rax))
             (binary-inst op (reg 'rax) dest))]
      [_ inst]))

  (xxprogram stack-size (flatten (map patch (xxprogram-insts xxprog)))))


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

(define (op->asm op)
  (match op
    ['neg "negq"]
    ['mov "movq"]
    ['add "addq"]
    ['sub "subq"]
    ['mul "imulq"]
    ['div "idivq"]
    ['call "callq"]
    ['ret "ret"]))

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

  (define stack-prefix (if (= 0 stack-size) ""
                           (string-append (fmt-asm "pushq" "%rbp")
                                          (fmt-asm "movq" "%rsp" "%rbp")
                                          (fmt-asm "subq" (int->asm stack-size) "%rsp"))))

  (define stack-suffix (if (= 0 stack-size) ""
                           (string-append (fmt-asm "addq" (int->asm stack-size) "%rsp")
                                          (fmt-asm "popq" "%rbp"))))

  (define main-return (fmt-asm "retq"))

  (define final-asm
    (string-append asm-prefix stack-prefix (apply string-append (map inst->asm insts)) stack-suffix main-return))

  final-asm)

;;;
;;; Utils for compiling and runnings ASM code
;;;
(define (expr->asm expr)
  (print-asm (patch-insts (assign-homes (select-insts (flatten-code (uniquify expr)))))))

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


(define test-expr
  '(let ([v 1] [w 46])
     (let ([x (+ v 7)])
       (let ([y (+ 4 x)] [z (+ x w)])
         (+ z (- y))))))
#;
(define test-expr
  '(let ([x 1] [y 2])
     (+ x y)))

(define test-xprog (uncover-live (select-insts (flatten-code (uniquify test-expr)))))

test-xprog

(define interference (build-interference test-xprog))