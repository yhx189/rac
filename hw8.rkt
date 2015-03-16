#lang plai-typed
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
 
(define-type TFAE
  [num (n : number)]
  [bool (b : boolean)]
  [add (l : TFAE) (r : TFAE)]
  [sub (l : TFAE) (r : TFAE)]
  [eql (l : TFAE) (r : TFAE)]
  [id (name : symbol)]
  [ifthenelse (tst : TFAE) (thn : TFAE) (els : TFAE)]
  [fun (arg : symbol) (typ : Type) (body : TFAE)]
  [app (rator : TFAE) (rand : TFAE)]
  [consl (fst : TFAE) (rst : TFAE)]
  [firstl (lst : TFAE)]
  [restl (lst : TFAE)]
  [nil (typ : Type)]
  [mtl? (lst : TFAE)])

(define-type Type 
  [numT]
  [boolT]
  [arrowT (dom : Type) (codom : Type)]
  [listT (typ : Type)])

(define-type TypeEnv
  [mtEnv]
  [aBind (name : symbol)
         (type : Type)
         (rest : TypeEnv)])

(define type-check-expr : (TFAE -> Type)
  (lambda (fae)
    (typecheck fae (mtEnv))))

(define lookup-type : (symbol TypeEnv -> Type)
  (lambda (name env)
    (type-case TypeEnv env
      [mtEnv () (error 'typecheck
                       "type-error unbound identifier")]
      [aBind (name2 type rest)
             (if (equal? name name2)
                 type
                 (lookup-type name rest))])))

(define typecheck : (TFAE TypeEnv -> Type)
  (lambda (fae env)
    (type-case TFAE fae
      
      [num (n) (numT)]
      [bool (b) (boolT)]
      [add (l r)
           (type-case Type (typecheck l env)
             [numT ()
                   (type-case Type (typecheck r env)
                     [numT () (numT)]
                     [else (error 'typecheck
                                  "type-error add expects a num")])]
             [else (error 'typecheck
                          "type-error add expects a num")])]
      [sub (l r)
           (type-case Type (typecheck l env)
             [numT ()
                   (type-case Type (typecheck r env)
                     [numT () (numT)]
                     [else (error 'typecheck
                                  "type-error sub expects a num")])]
             [else (error 'typecheck
                          "type-error sub expects a num")])]
      [id (name) (lookup-type name env)]
      [fun (name arg-type body)
        (arrowT arg-type
                (typecheck body (aBind name
                                       arg-type
                                       env)))]
      [app (fn arg)
           (type-case Type (typecheck fn env)
             [arrowT (arg-type result-type)
                     (if (equal? arg-type
                                 (typecheck arg env))
                         result-type
                         (error
                          'typecheck
                          "type-error arg mismatch"))]
             [else (error 'typecheck
                          "type-error app expects a function")])]
      [eql (l r)
           (type-case Type (typecheck l env)
             [numT ()
                   (type-case Type (typecheck r env)
                     [numT () (boolT)]
                     [else (error 'typecheck
                                  "type-error eql expects a num")])]
             [else (error 'typecheck
                          "type-error eql expects a num")])]
      [ifthenelse (tst thn els)
                  (type-case Type (typecheck tst env)
                    [boolT ()
                           (if (equal? (typecheck thn env)
                                       (typecheck els env))
                               (typecheck thn env)
                               (error 'typecheck "type-error then and else not equal"))]
                    [else (error 'typecheck "type-error if expects boolean")])]
      [consl (fst rst)
             (type-case Type (typecheck rst env)
               [listT (rstType)
                      (if (equal? rstType (typecheck fst env))
                          (listT rstType)
                          (error 'typecheck "type-error consl: first and rest type not match"))]
               [else 
                
                          (error 'typecheck "type-error consl: first and rest type not match")])]
      [firstl (lst)
              (type-case Type (typecheck lst env)
               [listT (rstType)
                      rstType]
               [else 
                (error 'typecheck "type-error firstl: not a list")])]
      [restl (lst)
              (type-case Type (typecheck lst env)
               [listT (rstType)
                      (listT rstType)]
               [else 
                (error 'typecheck "type-error restl: not a list")])]
      [nil (typ)
           (listT typ)]
      [mtl? (lst)
           (type-case Type (typecheck lst env)
             [listT (rstType)
                      (boolT)]
             [else (error 'typecheck "type-error mtl: not a list")])])))
              
      
 (test (lookup-type 'x (aBind 'x (arrowT (numT) (numT)) (mtEnv)))
      (arrowT (numT) (numT)))

(test/exn (lookup-type 'y (aBind 'x (arrowT (numT) (numT)) (mtEnv)))
      "type-error")


(test (type-check-expr (num 5))
      (numT))
(test (type-check-expr (bool #t))
      (boolT))

(test (type-check-expr (ifthenelse (bool #t) (num 5) (num 6)))
      (numT))
(test (type-check-expr (nil (numT)))
      (listT (numT)))
(test (type-check-expr (consl (num 5) (nil (numT))))
      (listT (numT)))
(test (type-check-expr (firstl (consl (num 5) (nil (numT)))))
      (numT))
(test (type-check-expr (restl (consl (num 5) (nil (numT)))))
      (listT (numT)))

(test (type-check-expr (eql  (num 5) (num 4)))
      (boolT))

(test (type-check-expr (fun 'x  (numT) (add (id 'x) (num 5))))
      (arrowT (numT) (numT)))

(test (type-check-expr (fun 'x  (boolT) (ifthenelse (id 'x) (num  3) (num 5))))
      (arrowT (boolT) (numT)))

(test (type-check-expr (app (fun 'x  (boolT) (ifthenelse (id 'x) (num 3) (num 5))) (bool #t)))
      (numT))

(test (type-check-expr (app (fun 'x  (numT) (add (id 'x) (num 5))) (num 5)))
      (numT))
 
(test (type-check-expr (app (fun 'x  (numT) (sub (id 'x) (num 5))) (num 5)))
      (numT))
 
(test (type-check-expr (consl (bool #t) (consl (bool #t) (nil (boolT)))))
      (listT (boolT))) 
(test (type-check-expr (mtl? (consl (bool #t) (consl (bool #t) (nil (boolT))))))
      (boolT)) 

(test/exn (type-check-expr (fun 'x  (boolT) (add (id 'x) (num 5))))
      "type-error")
(test/exn (type-check-expr (app (fun 'x  (numT) (add (id 'y) (num 5))) (num 5)))
       "type-error")
 (test/exn (type-check-expr (ifthenelse (bool #t) (num 5) (bool #t)))
      "type-error") 

 

(test/exn (type-check-expr (ifthenelse (num 5) (num 5) (num 6)))
      "type-error")
(test/exn (type-check-expr (firstl (consl (num 2) (consl (bool true) (nil (boolT))))))
      "type-error")
