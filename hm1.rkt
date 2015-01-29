#lang plai
(define eight-principles
  (list
   "Know your rights."
   "Acknowledge your sources."
   "Protect your work."
   "Avoid suspicion."
   "Do your own work."
   "Never falsify a record or permit another person to do so."
   "Never fabricate data, citations, or experimental results."
   "Always tell the truth when discussing your work with your instructor."))

(define-type Tree
    [leaf]
    [node (val number?)
          (left Tree?)
          (right Tree?)])

(define (smallest g)
   ;;
  (type-case Tree g
    [leaf() +inf.0]
    [node (val left right) (min val (smallest left)(smallest right))]
    ))


(define (negate g)
  (type-case Tree g
   [leaf() leaf?]
   [node(val left right) (node (- 0 val) left right)]))

(define (contains? t num)
  (type-case Tree t
    [leaf() #f]
    [node(val left right) (cond
                            [(equal? num val) #t]
                            [else (cond
                                    [(contains? left num) #t]
                                    [else (contains? right num)])])]))

(define (sorted? t)
  (type-case Tree t
    [leaf() #f]
    [node(val left right) (cond
                            [(< (smallest(negate left)) (- 0 val)) #f]
                            [(> (smallest(negate right)) (- 0 val)) #f]
                            [else #f])]))
(define (cnt t)
  (type-case Tree t
    [leaf() 0]
    [node(val left right) (+ (+ 1 (cnt left)) (cnt right))]))
  
 
(define (is-braun? t)
  (type-case Tree t
    [leaf() #t]
    [node(val left right) (cond
                            [(equal? (is-braun? left) #f) #f]
                            [(equal? (is-braun? right) #f) #f]
                            [(< (cnt left) (cnt right)) #f]
                            [else #t])]))

(define (make-sorted-braun n)
  (cond
    [(= 1 n) node(n (leaf) (leaf))]
    [else node((quotient n 2) make-sorted-braun((quotient n 4))
                              make-sorted-braun( (* 3 (quotient n 4))))]))   
          
          
          
(test (smallest (node 5 (leaf) (leaf))) 
      5.0)
(test (negate (node 5 (leaf) (leaf)))
      (node -5 (leaf) (leaf)))
(test (contains? (node 5 (leaf) (leaf)) 6) #f)
(test (cnt (node 2
      (node 1
            (node 0 (leaf) (leaf))
            (leaf))
      (node 3 (leaf) (leaf)))) 
      4)
(test (is-braun? (node 2
      (node 1
            (node 0 (leaf) (leaf))
            (leaf))
      (node 3 (leaf) (leaf)))) 
      #t)