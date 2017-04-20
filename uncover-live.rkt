#lang racket

(provide uncover-live)

(require "types.rkt")

;; gets the variables read by an instruction.
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
     [(binary-inst 'mov arg1 arg2)
      (list arg1)]
     ; all other binary insts are assumed to read both args
     [(binary-inst op arg1 arg2)
      (list arg1 arg2)])))

;; gets the variables written to by an instruction.
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

;; short-hand for dropping the first item of a list
(define drop1 rest)  

(define (uncover-live xprog)
  (match-define (xprogram vars all-insts emtpy) xprog)
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