#lang racket

(require "gen-unique-names.rkt")
(require "gen-linear-code.rkt")

(define expr '(let ((x 10) (y 6)) (+ (let ((x 1) (y 4)) y) x)))

(gen-linear-code (gen-unique-names expr))