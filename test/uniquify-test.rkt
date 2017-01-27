#lang racket

(require rackunit)
(require "../uniquify.rkt")

(test-begin
 (check-equal? (uniquify '(let ((x 10) (y 6)) (+ (let ((z 1) (y 4)) y) x)))
               '(let ((x_0 10) (y_0 6)) (+ (let ((z_1 1) (y_1 4)) y_1) x_0))))