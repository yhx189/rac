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
 
(define mult-and-neg-deffuns
  (list `{deffun {neg? x} {helper? x x}}
        `{deffun {helper? p n} {if0 p 1
                                    {if0 n 1
                                         {if0 {- p 1} 1
                                          {if0 {+ n 1} 0
                                               {helper? {- p 1} {+ n 1}}}}}}}
                              
        `{deffun {mult x y} {if0
                             {neg? y}
                             {- 0 {mult-helper x {abs y}}} 
                             {mult-helper x y}}}
        `{deffun {mult-helper x y} {if0 y 0 {if0 
                                            {- y 1}
                                            x
                                            {if0 
                                             {equal-two? y} 
                                             {+ x x} 
                                             {+ x {mult-helper x {- y 1}}}}}}}
        
        `{deffun {equal-two? x} {if0 {- x 2} 0 1}}
        `{deffun {abs x} {if0 {neg? x} {- 0 x} x}}
        ))

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
  [if0 (x FnWAE?)
       (y FnWAE?)
       (z FnWAE?)]
  [app (fun-name symbol?)
       (args (listof FnWAE?))])

(define-type FunDef
  [fundef (fun-name symbol?)
          (arg-names (listof symbol?))
          (body FnWAE?)])

(define-type DefrdSub
  [mtSub]
  [aSub (sub-name symbol?)
        (num number?)
        (rest-ds DefrdSub?)])


(define/contract (lookup-fundef name fundefs)
  (-> symbol? (listof FunDef?) FunDef?)
  (cond
   [(empty? fundefs)
    (error 'interp-expr "undefined function ~s" name)]
   [else
    (if (symbol=? name (fundef-fun-name
                        (first fundefs)))
        (first fundefs)
        (lookup-fundef name (rest fundefs)))]))


(define (lookup name ds)
  (type-case DefrdSub ds
    [mtSub () (error 'lookup "free variable ~s" name)]
    [aSub (sub-name num rest-ds)
          (if (symbol=? sub-name name)
              num
              (lookup name rest-ds))]))


(define/contract (interp-expr a-fnwae fundefs)
  (-> FnWAE? (listof FunDef?) number?)
  (interp a-fnwae fundefs (mtSub)))

(define/contract (interp a-fnwae fundefs ds)
  (-> FnWAE? (listof FunDef?) DefrdSub? number?)
; interp FnWAE list-of-FunDef -> num/error
  (type-case FnWAE a-fnwae
    [num (n) n]
    [add (l r) ( + (interp l fundefs ds)
                   (interp r fundefs ds))]
    [sub (l r) ( - (interp l fundefs ds)
                   (interp r fundefs ds))]
    [with (name named-expr body) (interp 
                                  body 
                                  fundefs
                                  (aSub name (interp named-expr fundefs ds) ds))] 
    [id (name) (lookup name ds) ]
    [if0 (x y z)(cond
                  [(equal? 0 (interp x fundefs ds)) (interp y fundefs ds)]
                  [else (interp z fundefs ds)])]
    [app (name args)
         (local [(define a-fundef (lookup-fundef name fundefs))]
           (if (equal? (length args) (length (fundef-arg-names a-fundef)))
               ;(cond 
                 ;[(empty? args) (interp (fundef-body a-fundef) '() ds)]
                 ;[else   
                  (interp
                   (fundef-body a-fundef)    
                   fundefs
                   (append-sub
                    (fundef-arg-names a-fundef) 
                    (map (lambda (x) (interp x fundefs ds)) args)
                    (mtSub)))
               (error 'interp-expr "wrong arity")))])) 

(define/contract (append-sub names numbers rest-ds)
  (-> (listof symbol?) (listof number?) DefrdSub? DefrdSub?)
  (cond 
    [(empty? names) rest-ds]
    [(empty? numbers) rest-ds]
    [else (aSub 
     (first names) 
     (first numbers)
     (append-sub (rest names) (rest numbers) rest-ds))]
  ))
 

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
                     [(symbol=? (first sexps) 'if0) (if0 
                                                     (parse (first (rest sexps)))
                                                     (parse (second (rest sexps)))
                                                     (parse (third (rest sexps))))]
                                                                                                       
                     [else
                      (app (first sexps) (map parse (rest sexps)))])]))


(define (parse-defn sexps)
  ;(-> any/c  FunDef?)
 ; parse-defn '{fundef} -> FunDef)
  (case (first sexps)
    [(deffun)
     (fundef 
      (first (second sexps))
      (check-for-dupli (rest (second sexps)))
      (parse (third sexps)))]))
 

(define/contract (check-for-dupli fun-args)
  (-> (listof symbol?) (listof symbol?))
  (if (=  (length fun-args)  (length (remove-duplicates fun-args)))
      fun-args
      (error 'parse-defn "bad syntax")))
   
(print-only-errors)
(test (interp-expr (parse '{neg? 5})
                 (map parse-defn mult-and-neg-deffuns))
        1)
(test (interp-expr (parse '{neg? -5})
                 (map parse-defn mult-and-neg-deffuns))
        0)

(test (interp-expr (parse '{neg? 0})
                 (map parse-defn mult-and-neg-deffuns))
        1)
(test (interp-expr (parse '{mult 3 -5})
                 (map parse-defn mult-and-neg-deffuns))
        -15)

(test (interp-expr (parse '{mult 50 0})
                 (map parse-defn mult-and-neg-deffuns))
        0)
(test (interp-expr (parse '{mult {with {x 5} {+ x 3}} {+ 4 5}})
                 (map parse-defn mult-and-neg-deffuns))
        72)
 
(test (parse-defn '{deffun {f x y} {+ x y}})
    (fundef 'f '(x y) (add (id 'x) (id 'y))))

(test (parse '{f 1 2})
      (app 'f (list (num 1) (num 2))))

(test (parse '{+ {f} {f}})
      (add (app 'f '()) (app 'f '())))

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
(test (parse '(  x 1)) 
      (app 'x (list (num 1)))) 
(test (parse '( + x 1)) 
      (add (id 'x) (num 1)))

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

(test (interp-expr (parse '{f})
                (list (parse-defn '{deffun {f} 5})))
        5)

(test (interp-expr (parse '{+ {f} {f}})
                (list (parse-defn '{deffun {f} 5})))
        10)
(test (interp-expr (parse '{f 1 2})
                (list (parse-defn '{deffun {f x y} {+ x y}})))
        3)
(test (interp-expr (parse '{f 1 2})
                (list 
                 (parse-defn '{deffun {f x y} {+ x y}})
                 (parse-defn '{deffun {g x y} {+ x y}})))
        3)
(test/exn (interp-expr (parse '{f 1 2})
                (list 
                 (parse-defn '{deffun {g x y} {+ x y}})
                 (parse-defn '{deffun {h x y} {+ x y}})))
        "undefined function")

(test (interp-expr (parse '{f 1 2 3})
                (list (parse-defn '{deffun {f x y z} {+ {+ x y} z}})))
        6)

(test/exn (interp-expr (parse '{f 1})
                    (list (parse-defn '{deffun {f x y} {+ x y}})))
            "wrong arity")

(test (interp-expr (parse '{f 1})
                (list (parse-defn '{deffun {f x} 1})))
           1)

(test/exn (interp-expr (parse '{with {x y} 1})
                    (list))
            "free")




(test (interp-expr (add (num 1) (num 3)) empty)
      
      4)
(test (interp-expr (add (num 1) (num 1))
              (list 
               (fundef 'f '(x)
                       (add (id 'x) (num 3))))) 
      2)

(test (interp-expr (parse '(f 1)) 
              (list 
               (parse-defn '(deffun (f x) (+ x 3)))))
      4)
(test (interp-expr (app 'f (list (num 10)))
              (list 
               (fundef 'f (list 'x) 
                       (sub (num 20)
                            (app 'twice (list (id 'x)))))
               (fundef 'twice (list 'y)
                       (add (id'y) (id 'y)))))
      0)
(test (interp-expr (parse '{f 1 2}) 
              (list (parse-defn '{deffun {f x y} {+ x y}})))
      3)
(test/exn (interp-expr (parse '{f 1})
                  (list (parse-defn '{deffun {f x y} {+ x y}})))
          "wrong arity")
(test (interp-expr (parse '{f 1 2 3})
              (list (parse-defn '{deffun {f x y z} {+ x {+ y z}}})))
      6)
(test (interp-expr (parse '(f {+ 5 5})) (list (parse-defn '{deffun {f x} {+ x x}})))
      20)
(test (interp-expr (parse '{f 10 13}) (list (parse-defn '{deffun {f f x} {+ f x}})))
      23)
(test (interp-expr (parse '{with {x {+ 1 2}}
                            {+ x x}}) empty)
      6)
(test (interp-expr (parse '{+ {with {x {+ 1 2}}
                               {+ x x}}
                         {with {x {- 4 3}}
                               {+ x x}}}) empty)
      8)
(test (interp-expr (parse '{+ {with {x {+ 1 2}}
                               {+ x x}}
                         {with {y {- 4 3}}
                               {+ y y}}}) empty)
      8)
(test (interp-expr (parse '{with {x {+ 1 2}}
                            {with {x {- 4 3}}
                                  {+ x x}}}) empty)
      2)
(test (interp-expr (parse '{with {x {+ 1 2}}
                            {with {y {- 4 3}}
                                  {+ x x}}}) empty)
      6)

(test (lookup-fundef 'f (list (fundef 'f '(x) (add (id 'x) (num 3))))) 
      (fundef 'f '(x) (add (id 'x) (num 3))))
(test (lookup-fundef 'f (list (fundef 'f '(x) (add (id 'x) (num 3))) 
                              (fundef 'twice '(x) (add (id 'x) (id 'x)))))
      (fundef 'f '(x) (add (id 'x) (num 3))))
(test (interp-expr (parse '(f 1 2)) 
              (list (parse-defn '(deffun (f x y) (+ x y))) 
                    (parse-defn '(deffun (f x y) (- x y)))))
      3)

(test (interp-expr
  (parse '(f 1 2))
  (list (parse-defn '(deffun (f x y) (with (x 4) (+ x y))))))
      6)

(test (interp-expr
  (parse '(f 1 2))
  (list (parse-defn '{deffun {f x y} {with {x 4} {+ x y}}})))
      6)
(test (interp-expr (parse '{f 1 2})
              (list (parse-defn '{deffun {f x y} {g y x}})
                    (parse-defn '{deffun {g x y} x})))
      2)

(test (interp-expr (parse '{f 1 2})
              (list (parse-defn '{deffun {f x y} {+ y x}})))
      3)

(test (interp-expr (parse '{f 1 2})
              (list (parse-defn '{deffun {f x y} {g y x}})
                    (parse-defn '{deffun {g x y} y})))
      1)
(test (interp-expr (parse '{f {f 1 2} {f 3 2}})
              (list (parse-defn '{deffun {f x y} {g y x}})
                    (parse-defn '{deffun {g x y} {+ y x}})))
      8)

(test/exn (interp-expr (parse '{f 1 2})
                  (list (parse-defn '{deffun {f x y z} {+ x y}})))
          "wrong arity")
(test/exn (interp-expr (parse '{f 1 2 3})
                  (list (parse-defn '{deffun {f x y} {+ x y}})))
          "wrong arity")
 
(test/exn (parse-defn '{deffun {f x z y y z} x})
          "bad syntax")


(test/exn (interp-expr (parse '{with {x y} 1})
                  (list))
          "free")

(test/exn (interp-expr (parse '{f 1 2})
                  (list (parse-defn '{deffun {g x y} y})))
          "undefined")

(test (interp-expr (parse '{f 1 2})
              (list (parse-defn '{deffun {f x y} {g x y 3}})
                    (parse-defn '{deffun {g x y z} {bar x {+ y z}}})
                    (parse-defn '{deffun {bar x y} {+ x y}})))
      6)  
(test (interp-expr (parse '{f {with {x 3} {+ x x}} 2})
              (list (parse-defn '{deffun {f x y} {+ x y}})))
      8)


(test (interp-expr
  (parse '(f 1 2))
  (list (parse-defn '(deffun (f x y) (with (x 4) (+ x y))))))
      6)
