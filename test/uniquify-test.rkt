#lang racket

(require rackunit)
(require "../gen-unique-names.rkt")

(test-begin
 (check-equal? (gen-unique-names '(let ((x 10) (y 6)) (+ (let ((z 1) (y 4)) y) x)))
               '(let ((x_0 10) (y_0 6)) (+ (let ((z_1 1) (y_1 4)) y_1) x_0))))