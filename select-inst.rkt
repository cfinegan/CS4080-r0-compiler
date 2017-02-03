#lang racket

(struct int (val) #:transparent)

(struct var (name) #:transparent)

(struct mov-inst (src dest) #:transparent)

(struct ret-inst (var) #:transparent)

(struct add-inst (src dest) #:transparent)

(struct sub-inst (src dest) #:transparent)

(struct neg-inst (var) #:transparent)

(struct mul-inst (src dest) #:transparent)

(struct div-inst (src dest) #:transparent)