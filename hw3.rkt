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
 
(define-type FnWAE
  [num (n number?)]
  [add (lhs FnWAE?)
       (rhs FnWAE?)]
  [sub (lhs FnWAE?)
       (rhs FnWAE?)]
  [with (name symbol?)
        (named-expr FnWAE?)
        (body FnWAE?)]
  [id (name symbol?)]
  [app (fun-name symbol?)
       (args (listof FnWAE?))])

(define-type FunDef
  [fundef (fun-name symbol?)
          (arg-names (listof symbol?))
          (body FnWAE?)])


(define (deffun-fun-name a-fundef)
  ; FunDef -> symbol
 (type-case FunDef a-fundef
   [fundef (fun-name arg-names body) fun-name]))

(define (deffun-body a-fundef)
  ; FunDef -> FnWAE
 (type-case FunDef a-fundef
   [fundef (fun-name arg-names body) body]))

(define (deffun-arg-names a-fundef)
  ; FunDef -> (listof symbol?)
 (type-case FunDef a-fundef
   [fundef (fun-name arg-names body) arg-names]))


(define/contract (lookup-fundef name fundefs)
  (-> symbol? (listof FunDef?) FunDef?)
  (cond
   [(empty? fundefs)
    (error 'interp "undefined function")]
   [else
    (if (symbol=? name (fundef-fun-name
                        (first fundefs)))
        (first fundefs)
        (lookup-fundef name (rest fundefs)))]))





(define/contract (subst a-wae sub-ids vals)
  (-> FnWAE?  (listof symbol?)  (listof number?) FnWAE?)
  (type-case FnWAE a-wae
    [num (n) a-wae]
    [add (l r) (add (subst l sub-ids vals)
                    (subst r sub-ids vals))]
    [sub (l r) (sub (subst l sub-ids vals)
                    (subst r sub-ids vals))]
    [with (bound-id named-expr body-expr)
          (with bound-id
                (subst named-expr sub-ids vals)
                (if (symbol=? bound-id (first sub-ids))
                    body-expr
                    (subst body-expr sub-ids vals)))]
    [id (name) (if (member name  sub-ids) 
                   (num (list-ref vals 
                                  (- (length sub-ids) (length (member name sub-ids)))))
                  
                   a-wae)]
   [app (fun-name arg)
         (app fun-name (map subst 
                            arg 
                            (make-list (length arg) sub-ids) 
                            (make-list (length arg) vals)))]))


   
(define (interp a-wae fundefs)
; interp FnWAE list-of-FunDef -> num/error
  (type-case FnWAE a-wae
    [num (n) n]
    [add (l r) ( + (interp l fundefs)
                   (interp r fundefs))]
    [sub (l r) ( - (interp l fundefs)
                   (interp r fundefs))]
    [with (name named-expr body) (interp 
                                  (subst body (list name) (list (interp named-expr fundefs)))
                                  fundefs)] 
    [id (name) (error 'interp "free ") ]
    [app (name args)
         (local [(define a-fundef
                   (lookup-fundef name fundefs))]
           (if (= (length args) (length (deffun-arg-names a-fundef)))
               (cond 
                 [(empty? args) (interp (fundef-body a-fundef) '())]
                 [else   
                  (interp
                     ( subst (fundef-body a-fundef)
                             (fundef-arg-names a-fundef)
                             (map (lambda (x) (interp x fundefs)) args))              
                     fundefs )])
               (error 'interp "wrong arity")))]))

(define (check-pieces expression size what)
  (unless (and (list? expression)
               (= (length expression) size))
    (parse-error what expression)))

(define (parse-error what expression)
  (error 'parser
         "expected: ~a, found:\n~a"
         what
         (pretty-format expression 30)))

(define (parse sexps)
  ;(-> any/c  FnWAE?)
 ; parse '{} -> FnWAE 
  (cond 
    [(number? sexps) (num sexps)]
    [(symbol? sexps) (id sexps)]
    [(list? sexps) (cond 
                     
                     [(symbol=?  (first sexps) '+) (add (parse (second sexps))  (parse (third sexps)))]
                     [(symbol=?  (first sexps) '-) (sub (parse (second sexps))  (parse (third sexps)))]
                     [(symbol=?  (first sexps) 'with) (with 
                                                       (list-ref (list-ref sexps 1) 0)
                                                       (parse (list-ref (list-ref sexps 1) 1))
                                                       (parse (list-ref sexps 2)))]
                     [else
                      (app (first sexps) (map parse (rest sexps)))])]))


(define (parse-defn sexps)
  ;(-> any/c  FunDef?)
 ; parse-defn '{fundef} -> FunDef)
  (case (first sexps)
    [(deffun)
     (fundef (first (second sexps))
                    (check-for-dupli (rest (second sexps)))
                    (parse (third sexps)))]))
 

(define/contract (check-for-dupli fun-args)
  (-> (listof symbol?) (listof symbol?))
  (if (=  (length fun-args)  (length (remove-duplicates fun-args)))
      fun-args
      (error 'parse-defn "bad syntax")))
   
(print-only-errors)

  
(test (parse-defn '{deffun {f x y} {+ x y}})
    (fundef 'f '(x y) (add (id 'x) (id 'y))))

(test (parse '{f 1 2})
      (app 'f (list (num 1) (num 2))))

(test (parse '{+ {f} {f}})
      (add (app 'f '()) (app 'f '())))

(test (interp (parse '{f})
                (list (parse-defn '{deffun {f} 5})))
        5)

(test (interp (parse '{+ {f} {f}})
                (list (parse-defn '{deffun {f} 5})))
        10)
(test (interp (parse '{f 1 2})
                (list (parse-defn '{deffun {f x y} {+ x y}})))
        3)
(test (interp (parse '{f 1 2})
                (list 
                 (parse-defn '{deffun {f x y} {+ x y}})
                 (parse-defn '{deffun {g x y} {+ x y}})))
        3)
(test/exn (interp (parse '{f 1 2})
                (list 
                 (parse-defn '{deffun {g x y} {+ x y}})
                 (parse-defn '{deffun {h x y} {+ x y}})))
        "undefined function")

(test (interp (parse '{f 1 2 3})
                (list (parse-defn '{deffun {f x y z} {+ {+ x y} z}})))
        6)

(test/exn (interp (parse '{f 1})
                    (list (parse-defn '{deffun {f x y} {+ x y}})))
            "wrong arity")

(test (interp (parse '{f 1})
                (list (parse-defn '{deffun {f x} 1})))
           1)

(test/exn (interp (parse '{with {x y} 1})
                    (list))
            "free")


(test (parse 1)
      (num 1))
(test (parse 'x) 
      (id 'x))
(test (parse '(+ 1 2))
      (add (num 1) (num 2)))
(test (parse '(- 1 2))
      (sub (num 1) (num 2)))
(test (parse '(with (x 1) (+ x x)))
      (with 'x (num 1) (add (id 'x) (id 'x))))
(test (parse '( x 1)) 
      (app 'x (list (num 1)))) 


(test (parse-defn '{deffun {f x y} x})
      (fundef 'f '(x y) (id 'x)))
(test (parse-defn '{deffun {f x y} {+ x y}}) 
      (fundef 'f '(x y) (add (id 'x) (id 'y))))
(test/exn (parse-defn '{deffun {f x x} x})
          "bad syntax")
(test (parse-defn '{deffun {f} 5}) 
      (fundef 'f '() (num 5)))
(test (parse-defn '{deffun {f x}
                     {- 20 { + { + x x}
                               {+ x x}}}})
      (fundef
       'f
       '(x)
       (sub
        (num 20)
        (add (add (id 'x) (id 'x)) (add (id 'x) (id 'x))))))    


(test (interp (add (num 1) (num 3)) empty)
      
      4)
(test (interp (add (num 1) (num 1))
              (list 
               (fundef 'f '(x)
                       (add (id 'x) (num 3))))) 
      2)

(test (interp (parse '(f 1)) 
              (list 
               (parse-defn '(deffun (f x) (+ x 3)))))
      4)
(test (interp (app 'f (list (num 10)))
              (list 
               (fundef 'f (list 'x) 
                       (sub (num 20)
                            (app 'twice (list (id 'x)))))
               (fundef 'twice (list 'y)
                       (add (id'y) (id 'y)))))
      0)
(test (interp (parse '{f 1 2}) 
              (list (parse-defn '{deffun {f x y} {+ x y}})))
      3)
(test/exn (interp (parse '{f 1})
                  (list (parse-defn '{deffun {f x y} {+ x y}})))
          "wrong arity")
(test (interp (parse '{f 1 2 3})
              (list (parse-defn '{deffun {f x y z} {+ x {+ y z}}})))
      6)
(test (interp (parse '(f {+ 5 5})) (list (parse-defn '{deffun {f x} {+ x x}})))
      20)
(test (interp (parse '{f 10 13}) (list (parse-defn '{deffun {f f x} {+ f x}})))
      23)
(test (interp (parse '{with {x {+ 1 2}}
                            {+ x x}}) empty)
      6)
(test (interp (parse '{+ {with {x {+ 1 2}}
                               {+ x x}}
                         {with {x {- 4 3}}
                               {+ x x}}}) empty)
      8)
(test (interp (parse '{+ {with {x {+ 1 2}}
                               {+ x x}}
                         {with {y {- 4 3}}
                               {+ y y}}}) empty)
      8)
(test (interp (parse '{with {x {+ 1 2}}
                            {with {x {- 4 3}}
                                  {+ x x}}}) empty)
      2)
(test (interp (parse '{with {x {+ 1 2}}
                            {with {y {- 4 3}}
                                  {+ x x}}}) empty)
      6)

(test (lookup-fundef 'f (list (fundef 'f '(x) (add (id 'x) (num 3))))) 
      (fundef 'f '(x) (add (id 'x) (num 3))))
(test (lookup-fundef 'f (list (fundef 'f '(x) (add (id 'x) (num 3))) 
                              (fundef 'twice '(x) (add (id 'x) (id 'x)))))
      (fundef 'f '(x) (add (id 'x) (num 3))))
(test (interp (parse '(f 1 2)) 
              (list (parse-defn '(deffun (f x y) (+ x y))) 
                    (parse-defn '(deffun (f x y) (- x y)))))
      3)


(test (interp (parse '{f 1 2})
              (list (parse-defn '{deffun {f x y} {g y x}})
                    (parse-defn '{deffun {g x y} x})))
      2)

(test (interp (parse '{f 1 2})
              (list (parse-defn '{deffun {f x y} {+ y x}})))
      3)

(test (interp (parse '{f 1 2})
              (list (parse-defn '{deffun {f x y} {g y x}})
                    (parse-defn '{deffun {g x y} y})))
      1)
(test (interp (parse '{f {f 1 2} {f 3 2}})
              (list (parse-defn '{deffun {f x y} {g y x}})
                    (parse-defn '{deffun {g x y} {+ y x}})))
      8)

(test/exn (interp (parse '{f 1 2})
                  (list (parse-defn '{deffun {f x y z} {+ x y}})))
          "wrong arity")
(test/exn (interp (parse '{f 1 2 3})
                  (list (parse-defn '{deffun {f x y} {+ x y}})))
          "wrong arity")
 
(test/exn (parse-defn '{deffun {f x z y y z} x})
          "bad syntax")
(test (subst (id 'x) (list 'y) (list 5)) (id 'x))


(test/exn (interp (parse '{with {x y} 1})
                  (list))
          "free")

(test/exn (interp (parse '{f 1 2})
                  (list (parse-defn '{deffun {g x y} y})))
          "undefined")

(test (interp (parse '{f 1 2})
              (list (parse-defn '{deffun {f x y} {g x y 3}})
                    (parse-defn '{deffun {g x y z} {bar x {+ y z}}})
                    (parse-defn '{deffun {bar x y} {+ x y}})))
      6)  
(test (interp (parse '{f {with {x 3} {+ x x}} 2})
              (list (parse-defn '{deffun {f x y} {+ x y}})))
      8)

