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
 

(define n-to-f `{fun {n}
                     {fun {f} 
                          {fun {x} 
                               {with {n-to-f-helper
                                      {fun {n-to-f-helper n}
                                           {if0 {n}
                                                {x}
                                                {f {n-to-f-helper n-to-f-helper {- n 1}}}}}}
                                     {n-to-f-helper n-to-f-helper n}}}}})
(define f-to-n `{fun {f}
                     {f {fun {x} {+ x 1}} 0} })
                     
                    
(define plus `{fun {f1 f2}
                   {fun {f} {fun {x}
                                 {{fun {xx}
                                       {f1 {f} {xx}}} 
                                  {f2 {f} {x}}}}}})

(define times `{fun {f1 f2} 
                    {fun {f} {fun {x}
                                  {f1 {f2 {f} } {x}}}}}) 
                                


(define-type FAE
  [num (n number?)]
  [add (lhs FAE?) (rhs FAE?)]
  [sub (lhs FAE?) (rhs FAE?)]
  [id (name symbol?)]
  [if0 (test FAE?) (then FAE?) (else FAE?)]
  [fun (param symbol?) (body FAE?)]
  [app (fun FAE?) (arg FAE?)])


(define-type FAE-Value
  [numV (n number?)]
  [closureV (param symbol?)
        (body FAE?)
        (ds DefrdSub?)])

(define-type DefrdSub
  [mtSub]
  [aSub (sub-name symbol?)
        (val FAE-Value?)
        (rest-ds DefrdSub?)])

(define (lookup name ds)
  (type-case DefrdSub ds
    [mtSub () (error 'lookup "free identifier ~s" name)]
    [aSub (sub-name num rest-ds)
          (if (symbol=? sub-name name)
              num
              (lookup name rest-ds))]))

(define (num-op op)
         (lambda (x y)
           (numV (op (numV-n x) (numV-n y)))))
(define num+ (num-op +))
(define num- (num-op -))

(define (interp-expr a-fae)
 
  (type-case FAE-Value (interp a-fae (mtSub))
    [numV (n)  n]
    [closureV (param body ds) 'procedure]))

(define/contract (interp a-fae ds)
   (-> FAE? DefrdSub? FAE-Value?)
  (type-case FAE a-fae
    [num (n) (numV n)]
    [add (l r) (local [(define l-val (interp l ds))
                       (define r-val (interp r ds))]
                 (type-case FAE-Value l-val
                   [closureV (param body ds) (error 'interp-expr "numeric operation expected number~s" body)]
                   [numV (ln) (type-case FAE-Value r-val
                               [closureV (param body ds)
                                         (error 'interp-expr "numeric operation expected number")]
                               [numV (rn) (num+ l-val r-val)])]))]
    [sub (l r) (local [(define l-val (interp l ds))
                       (define r-val (interp r ds))]
                 (type-case FAE-Value l-val
                   [closureV (param body ds) (error 'interp-expr "numeric operation expected number")]
                   [numV (ln) (type-case FAE-Value r-val
                               [closureV (param body ds)
                                         (error 'interp-expr "numeric operation expected number")]
                               [numV (rn) (num- l-val r-val)])]))]
    [id (name) (lookup name ds)]
    [fun (param body-expr) 
         (closureV param body-expr ds)]
    [if0 (test then else)
         (local [(define x (interp test ds))]
         (type-case FAE-Value x
           [closureV (param body ds) (interp else ds)]
           [numV (n)
            (if (= 0 n)
             (interp then ds)
             (interp else ds))]))]
    [app (fun-expr arg-expr)
         (local [(define fun-val
                   (interp fun-expr ds))
                 (define arg-val
                   (interp arg-expr ds))]
           (type-case FAE-Value fun-val
             [numV (n) (error 'interp-expr "application expected procedure")]
             [closureV (fun-v-param fun-v-body fun-v-ds)
                       (interp fun-v-body
                               (aSub fun-v-param
                                     arg-val
                                     fun-v-ds))]))]))
 

(define (parse sexps)
  ;(-> sexpr  FAE?)
 ; parse '{} -> FAE 
  (cond 
    [(number? sexps) (num sexps)]
    [(symbol? sexps) (id sexps)]
    [(list? sexps) (cond 
                     
                     [(equal?  (first sexps) '+) (add (parse (second sexps))  (parse (third sexps)))]
                     [(equal?  (first sexps) '-) (sub (parse (second sexps))  (parse (third sexps)))]
                     [(equal?  (first sexps) 'with) (app
                                                     (fun (first (second sexps)) (parse (third sexps)))
                                                     (parse (second (second sexps))))]
                     
                     [(equal? (first sexps) 'if0) (if0 
                                                     (parse (first (rest sexps)))
                                                     (parse (second (rest sexps)))
                                                     (parse (third (rest sexps))))]
                     [(equal? (first sexps) 'fun)(case (length (second sexps))
                                                     [(1) (fun 
                                                           (first (second sexps)) 
                                                           (parse (third sexps)))]
                                                     [else (fun
                                                            (first (second sexps))
                                                            (parse (list
                                                                    (first sexps)
                                                                    (rest (second sexps))
                                                                    (third sexps))))])]
                     
                     [else
                      (case (length sexps)
                        [(1)  (parse (first sexps))]
                        
                        [else  (app
                                (parse (drop-right sexps 1))
                                (parse (last sexps))
                                )])])]))
                       


   
(print-only-errors)
(test (parse '{a b c})
      (app 
       (app (id 'a) (id 'b))
       (id 'c) ))
(test (parse '{a b c d e})
      (app 
       (app 
        (app
         (app (id 'a) (id 'b))
        (id 'c))
       (id 'd))
       (id 'e)))
(test (interp-expr (parse `{ {fun {x y z m} {+ x {+ x {+ x {+ x x}}}}} 3 {fun {x} x} 5 6}))
      15)
(test (parse '{fun {a b} {+ a b}})
      (fun 'a (fun 'b (add (id 'a) (id 'b)))))


(test (parse 	'{fun {a b c} {- a {+ b c}}})
      (fun
       'a
       (fun
        'b
        (fun 'c (sub (id 'a) (add (id 'b) (id 'c)))))))
(test (parse 	'{{fun {a b c} {- a {+ b c}}} {1 2 3}})
      (app
 (fun
  'a
  (fun
   'b
   (fun 'c (sub (id 'a) (add (id 'b) (id 'c))))))
 (app (app (num 1) (num 2)) (num 3))))
(test (interp-expr (if0 (fun 'a (id 'b))
                        (num 0) (num 1)))
      1)
(test (interp-expr (num 10)) 10)
(test (interp-expr (fun 'x (id 'x))) 'procedure)
(test/exn (interp-expr (parse `{+ {{fun {x} 3} 2}
                                  { 1 2}}))
          "application expected procedure")

(test (interp-expr (parse `{with {twice {fun {y} {+ y y}}}
    {with {f {fun {x} {- 20 {twice x}}}}
        {f 3}}}    ))
      14)

(test (interp-expr (app (app (app (parse n-to-f)
                             (num 8))
                        (fun 'XX (num 0)))
                   (num 0)))
      0)

(test (interp-expr (parse '{{fun {x} {- 20 {{fun {y}{+ y y}}
                                            x}}}
                            3}))
      14)
(test/exn (interp-expr (app (app (id 'x) (id 'y)) (fun 'x (id 'x))))
          "free identifier")

(test (interp-expr (parse `{,n-to-f  1}))
      'procedure)
(test (interp-expr (parse `{{{,n-to-f 3} {fun {x} {+ x x}}} 3}))
        24)
(test (interp-expr (parse `{,f-to-n {,n-to-f  30}}))
      30)
(test (interp-expr (parse `{,f-to-n {,plus {,n-to-f 5} {,n-to-f 1}}}))
      6)
(test (interp-expr (parse `{,f-to-n {,plus {,n-to-f 1} {,n-to-f 0}}}))
      1)
(test (interp-expr (parse `{,f-to-n {,times {,n-to-f 0} {,n-to-f 1}}}))
      0)
(test (interp-expr (parse `{,f-to-n {,times {,n-to-f 0} {,n-to-f 5}}}))
      0)
(test (interp-expr (parse `{,f-to-n {,times {,n-to-f 5} {,n-to-f 1}}}))
      5)
(test (interp-expr (parse `{,f-to-n {,times {,n-to-f 50} {,n-to-f 3}}}))
      150)
(test (interp-expr (parse `{,f-to-n {,plus {
                                            ,times {,n-to-f 3} {,n-to-f 5}}
                                           { ,times {,n-to-f 2} {,n-to-f 3}}}
                                           }))
      21)

(test/exn (interp-expr (parse `{1 {+ {fun {x} x} 4}}))
          "numeric operation expected number")
(test/exn (interp-expr (parse `{+ {fun {x} x} 0}))
          "numeric operation expected number")
(test  (interp-expr (app (fun 'f (fun 'x (id 'x))) (num 1)))
       'procedure)
(test  (interp-expr  (parse '{{fun {x} {fun {y} {+ x y}}} 2}))
       'procedure)
(test (interp-expr (parse `{{fun {x y} {+ { + x y} 2}} 1 2}))
5)
(test/exn (interp-expr (parse '{with {foo {fun {x} x}}
                                     {+ {fun {m} m} {+ {foo y}{1 2}}}}))
          
          "free identifier")
(test/exn (interp-expr (parse '{with {foo {fun {x} x}}
                                     {+ {1 2} {+ {foo y}{1 2}}}}))
          
          "application expected procedure")