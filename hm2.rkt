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

(define-type WAE
  [num (n number?)]
  [add (lhs WAE?)
       (rhs WAE?)]
  [sub (lhs WAE?)
       (rhs WAE?)]
  [with (name symbol?)
        (named-expr WAE?)
        (body WAE?)]
  [id (name symbol?)])

(define/contract (free-ids a-wae)
  (-> WAE? list?)
  (type-case WAE a-wae
    [num (n) '()]
    [add (lhs rhs) (give-order (append (free-ids lhs) (free-ids rhs)))]
    [sub (lhs rhs) (give-order (append (free-ids lhs) (free-ids rhs)))]
    [with (name named-expr body) (if (member name (free-ids body)) 
                                    (give-order (append 
                                          (remove name (remove-duplicates (free-ids body)))
                                          (free-ids named-expr)))
                                    (give-order (append 
                                          (free-ids body)
                                          (free-ids named-expr))) 
                                       )]
    [id (name) (list name)]))

(define/contract (give-order a-list)
  (-> list? list?)
  (sort (remove-duplicates a-list)  symbol<?))

(define/contract (binding-ids a-wae)
  (-> WAE? list?)
  (type-case WAE a-wae
    [num (n) '()]
    [add (lhs rhs) (give-order (append (binding-ids lhs) (binding-ids rhs)))]
    [sub (lhs rhs) (give-order (append (binding-ids lhs) (binding-ids rhs)))]
    [with (name named-expr body) (give-order (append
                                              (list name)
                                              (binding-ids body)
                                              (binding-ids named-expr)))]
    [id (name) '()]))
 
(define/contract (bound-ids a-wae)
  (-> WAE? list?)
  (type-case WAE a-wae
    [num (n) '()]
    [add (lhs rhs) (give-order (append (bound-ids lhs) (bound-ids rhs)))]
    [sub (lhs rhs) (give-order (append (bound-ids lhs) (bound-ids rhs)))]
    [with (name named-expr body) (if (member name (free-ids body)) 
                                    (give-order (append 
                                          (list name)
                                          (bound-ids named-expr)
                                          (bound-ids body)))
                                    (give-order ( append
                                                       (bound-ids named-expr)
                                                       (bound-ids body))) 
                                       )]
    [id (name) '()]))

(define/contract (shadowed-variable? a-wae)
  (-> WAE? boolean?)
  (type-case WAE a-wae
    [num (n) #f]
    [add (lhs rhs) (or (shadowed-variable? lhs) (shadowed-variable? rhs)) ]
    [sub (lhs rhs) (or (shadowed-variable? lhs) (shadowed-variable? rhs)) ]
    [with (name named-expr body) (cond
                                   [(member name (bound-ids body)) #t]
                                   [else (or
                                          (shadowed-variable? named-expr)
                                          (shadowed-variable? body))])]
    [id (name) #f]))

(print-only-errors)
; test cases start from simple ones
(test (shadowed-variable?
  (with 'x (with 'y (num 1) (with 'y (num 2) (id 'y))) (num 3)))
      #t)
(test (free-ids  (id 'x))
     (list 'x))
(test (binding-ids  (id 'x))
     '())
(test (bound-ids  (id 'x))
     '())
(test (shadowed-variable?  (id 'x))
     #f)

(test (free-ids (with 'x (id 'y) (id 'z)))
      (list 'y 'z))
(test (binding-ids (with 'x (id 'y) (id 'z)))
      (list 'x))
(test (bound-ids (with 'x (id 'y) (id 'z)))
      '())
(test (shadowed-variable? (with 'x (id 'y) (id 'z)))
      #f)

(test (free-ids (with 'x (id 'x) (id 'y)))
      (list 'x 'y))
(test (binding-ids (with 'x (id 'x) (id 'y)))
      (list 'x))
(test (bound-ids (with 'x (id 'x) (id 'y)))
      '())
(test (shadowed-variable? (with 'x (id 'x) (id 'y)))
      #f)

(test (free-ids (with 'x (num 2) (id 'x)))
      '())
(test (binding-ids (with 'x (num 2) (id 'x)))
      '(x))
(test (bound-ids (with 'x (num 2) (id 'x)))
      '(x))
(test (shadowed-variable? (with 'x (num 2) (id 'x)))
      #f)



(test (free-ids (with 'x (num 1) (with 'y (id 'x) (id 'y))))
      '())
(test (binding-ids (with 'x (num 1) (with 'y (id 'x) (id 'y))))
      '(x y))
(test (bound-ids (with 'x (num 1) (with 'y (id 'x) (id 'y))))
      '(x y))
(test (shadowed-variable? (with 'x (num 1) (with 'y (id 'x) (id 'y))))
      #f)


(test (free-ids (with 'x (with 'y (num 2) (id 'y)) (id 'y)))
      (list 'y))
(test (binding-ids (with 'x (with 'y (num 2) (id 'y)) (id 'y)))
      (list 'x 'y))
(test (bound-ids (with 'x (with 'y (num 2) (id 'y)) (id 'y)))
      (list 'y))
(test (shadowed-variable? (with 'x (with 'y (num 2) (id 'y)) (id 'y)))
      #f)

(test (free-ids (with 'x (num 1) (with 'x (add (id 'x) (id 'x)) (num 5))))
      '())
(test (binding-ids (with 'x (num 1) (with 'x (add (id 'x) (id 'x)) (num 5))))
      '(x))
(test (bound-ids (with 'x (num 1) (with 'x (add (id 'x) (id 'x)) (num 5))))
      '(x))
(test (shadowed-variable? (with 'x (num 1) (with 'x (add (id 'x) (id 'x)) (num 5))))
      #f)

(test (shadowed-variable? (add (id 'x) (id 'x)))
      #f)
 
(test (free-ids (with 'a (num 17) (sub (add (id 'y) (id 'z)) (id 'x)))) 
      '(x y z))
(test (binding-ids (with 'a (num 17) (sub (add (id 'y) (id 'z)) (id 'x)))) 
      '(a))
(test (bound-ids (with 'a (num 17) (sub (add (id 'y) (id 'z)) (id 'x)))) 
      '())
(test (shadowed-variable? (with 'a (num 17) (sub (add (id 'y) (id 'z)) (id 'x)))) 
      #f)
 
(test (free-ids (with 'a (num 17) (with 'b (num 11) (add (id 'a) (id 'x))))) 
      '(x))
(test (binding-ids (with 'a (num 17) (with 'b (num 11) (add (id 'a) (id 'x))))) 
      '(a b))
(test (bound-ids (with 'a (num 17) (with 'b (num 11) (add (id 'a) (id 'x))))) 
      '(a))
(test (shadowed-variable? (with 'a (num 17) (with 'b (num 11) (add (id 'a) (id 'x))))) 
      #f)

 
(test (shadowed-variable? (with 'y
                                (num 1)
                          (with 'x
                                (num 2)
                                (with 'y
                                      (num 3)
                                      (id 'y)))))

      #t)

(test (free-ids
       (with 'x (with 'y (num 10) (num 10)) (with 'y (num 10) (id 'y))))
             '() )
(test (binding-ids 
       (with 'x (with 'y (num 10) (num 10)) (with 'y (num 10) (id 'y))))
            '(x y) )
(test (bound-ids 
       (with 'x (with 'y (num 10) (num 10)) (with 'y (num 10) (id 'y))))
             '(y) )
(test (shadowed-variable? 
       (with 'x (with 'y (num 10) (num 10)) (with 'y (num 10) (id 'y))))
             #f )

(test (free-ids
       (with 'y (with 'y (num 10) (num 10)) (with 'y (num 10) (id 'y))))
             '() )
(test (binding-ids
       (with 'y (with 'y (num 10) (num 10)) (with 'y (num 10) (id 'y))))
             '(y))
(test (bound-ids
       (with 'y (with 'y (num 10) (num 10)) (with 'y (num 10) (id 'y))))
             '(y) )
(test (shadowed-variable? 
       (with 'y (with 'y (num 10) (num 10)) (with 'y (num 10) (id 'y))))
             #t )




      