#lang plaitypus

(print-only-errors #t)

(define-type TLFAE
  [num (n : number)]
  [bool (b : boolean)]
  [add (l : TLFAE) (r : TLFAE)]
  [sub (l : TLFAE) (r : TLFAE)]
  [eql (l : TLFAE) (r : TLFAE)]
  [id (name : symbol)]
  [ifthenelse (tst : TLFAE) (thn : TLFAE) (els : TLFAE)]
  [fun (arg : symbol) (typ : Type) (body : TLFAE)]
  [app (rator : TLFAE) (rand : TLFAE)]
  [consl (fst : TLFAE) (rst : TLFAE)]
  [firstl (lst : TLFAE)]
  [restl (lst : TLFAE)]
  [nil (typ : Type)]
  [mtl? (lst : TLFAE)]
  [makevector (size : TLFAE) (initial : TLFAE)]
  [set (vec : TLFAE) (index : TLFAE) (val : TLFAE)]
  [lengthl (col : TLFAE)]
  [get (col : TLFAE) (index : TLFAE)])

(define-type Type
  [numberT]
  [booleanT]
  [arrowT (dom : Type) (codom : Type)]
  [listT (typ : Type)]
  [vectorT (typ : Type)])

(define-type TypeEnv
  [mtEnv]
  [aBind (name : symbol)
         (type : Type)
         (rest : TypeEnv)])


; PARSER
(define parse : (s-expression -> TLFAE)
  (lambda (s-exp)
    (cond
      [(s-exp-number? s-exp)
       (num (s-exp->number s-exp))]
      [(s-exp-symbol? s-exp)
       (case (s-exp->symbol s-exp)
         [(true)  (bool #t)]
         [(false) (bool #f)]
         [else (id (s-exp->symbol s-exp))])]
      [(s-exp-list? s-exp)
       (define as-list (s-exp->list s-exp))
       (cond [(empty? as-list)
              (error 'parse "the empty list is not a valid TLFAE")]
             [(s-exp-symbol? (first as-list))
              (case (s-exp->symbol (first as-list))
                [(+)
                 (check-pieces as-list "add" 3)
                 (add (parse (second as-list))
                      (parse (third as-list)))]
                [(-)
                 (check-pieces as-list "sub" 3)
                 (sub (parse (second as-list))
                      (parse (third as-list)))]
                [(=)
                 (check-pieces as-list "eql" 3)
                 (eql (parse (second as-list))
                      (parse (third as-list)))]
                [(if)
                 (check-pieces as-list "if" 4)
                 (ifthenelse (parse (second as-list))
                             (parse (third as-list))
                             (parse (fourth as-list)))]
                [(fun)
                 (check-pieces as-list "fun" 3)
                 (unless (s-exp-list? (second as-list))
                   (error 'parse "expected parameter list"))
                 (define param-list (s-exp->list (second as-list)))
                 (check-pieces param-list "parameter list" 3)
                 (unless (s-exp-symbol? (first param-list))
                   (error 'parse "expected symbol as parameter name"))
                 (unless (and (s-exp-symbol? (second param-list))
                              (equal? ': (s-exp->symbol (second param-list))))
                   (error 'parse "expected `:`"))
                 (fun (s-exp->symbol (first param-list))
                      (parse-type (third param-list))
                      (parse (third as-list)))]
                [(cons)
                 (check-pieces as-list "cons" 3)
                 (consl (parse (second as-list))
                        (parse (third as-list)))]
                [(first)
                 (check-pieces as-list "first" 2)
                 (firstl (parse (second as-list)))]
                [(rest)
                 (check-pieces as-list "rest" 2)
                 (restl (parse (second as-list)))]
                [(nil)
                 (check-pieces as-list "nil" 2)
                 (nil (parse-type (second as-list)))]
                [(empty?)
                 (check-pieces as-list "empty?" 2)
                 (mtl? (parse (second as-list)))]
                [(make-vector)
                 (check-pieces as-list "make-vector" 3)
                 (makevector (parse (second as-list))
                             (parse (third as-list)))]
                [(set)
                 (check-pieces as-list "set" 4)
                 (set (parse (second as-list))
                      (parse (third as-list))
                      (parse (fourth as-list)))]
                [(length)
                 (check-pieces as-list "length" 2)
                 (lengthl (parse (second as-list)))]
                [(get)
                 (check-pieces as-list "get" 3)
                 (get (parse (second as-list))
                      (parse (third as-list)))]
                [else (parse-app as-list)])]
             [else (parse-app as-list)])]
      [else
       (error 'parse "expected TLFAE")])))

(define parse-app : ((listof s-expression) -> TLFAE)
  (lambda (s-exps)
    (check-pieces s-exps "app" 2)
    (app (parse (first  s-exps))
         (parse (second s-exps)))))

(define parse-type : (s-expression -> Type)
  (lambda (s-exp)
    (cond [(and (s-exp-symbol? s-exp)
                (equal? 'number (s-exp->symbol s-exp)))
           (numberT)]
          [(and (s-exp-symbol? s-exp)
                (equal? 'boolean (s-exp->symbol s-exp)))
           (booleanT)]
          [(s-exp-list? s-exp)
           (define as-list (s-exp->list s-exp))
           (case (length as-list)
             [(2)
              (unless (s-exp-symbol? (first as-list))
                (error 'parse "expected `listof` or `vectorof`"))
              (case (s-exp->symbol (first as-list))
                [(listof)
                 (listT (parse-type (second as-list)))]
                [(vectorof)
                 (vectorT (parse-type (second as-list)))]
                [else
                 (error 'parse "expected `listof` or `vectorof`")])]
             [(3)
              (unless (and (s-exp-symbol? (second as-list))
                           (equal? '-> (s-exp->symbol (second as-list))))
                (error 'parse "expected `->`"))
              (arrowT (parse-type (first as-list))
                      (parse-type (third as-list)))]
             [else (error 'parse-type "expected type")])]
          [else (error 'parse-type "expected type")])))

(define check-pieces : ((listof s-expression) string number -> void)
  (lambda (s-exps expected n-pieces)
    (unless (= n-pieces (length s-exps))
      (error 'parse
             (string-append (string-append "expected " expected)
                            (string-append " got " (to-string s-exps)))))))


;; typechecker!
(define typecheck : (TLFAE TypeEnv -> Type)
  (lambda (a-tlfae gamma)
    (type-case TLFAE a-tlfae
      [num (n)
           ; axiom/base_case: if we see a number, it's type is (numberT)
           (numberT)]
      [bool (b)
            ; axiom/base_case: if we see a boolean, it's type is (booleanT)
            (booleanT)]
      [add (l r)
           ; RULE: l and r are numbers => (add l r) is a number

           ; first, check that the left and right are numbers (using the given gamma)
           ; recall gamma is our mapping of variables to types
           (unless (numberT? (typecheck l gamma))
             (error 'typecheck "expected number"))
           (unless (numberT? (typecheck r gamma))
             (error 'typecheck "expected number"))
           ; if we pass those checks, we should get a number
           (numberT)]
      [sub (l r)
           ; this is IDENTICAL to typechecking for add
           ; so just typecheck it as an add lol -> to be fancy later, u can also just make it a helper xoxo
           (typecheck (add l r) gamma)]
      [eql (l r)
           ; RULE: l and r are numbers => (eql l r) is a boolean
           (unless (numberT? (typecheck l gamma))
             (error 'typecheck "expected number"))
           (unless (numberT? (typecheck r gamma))
             (error 'typecheck "expected number"))
           (booleanT)]
      [id (name)
          ; we need to check gamma for some binding (mapping) from our desired id to some type
          ; if we don't find one, then no type!
          ; call a helper to do this
          (lookup-type name gamma)]
      [ifthenelse (tst thn els)
                  ; RULE: tst is a boolean, thn and els are τ => (if tst then els) is a τ

                  ; check that tst is a boolean
                  (unless (booleanT? (typecheck tst gamma))
                    (error 'typecheck "expected boolean"))

                  ; check that thn and els match
                  (define thn-type (typecheck thn gamma))
                  (define els-type (typecheck els gamma))

                  (unless (equal? thn-type els-type)
                    (error 'typecheck "type mismatch"))

                  ; return the type of thn (or equivalently, of els)
                  thn-type]
      [fun (arg typ body)
           ; RULE: (id is τ_1 in gamma => arg is τ_2) => function is (τ_1 -> τ_2)
           ; so here, the type of the parameter is passed in as an argument!
           (arrowT typ
                   
                   ; typecheck the body, using gamma with the arg-type binding added
                   (typecheck body (aBind arg typ gamma)))]
      [app (rator rand)
           ; RULE: (rator is (τ_2 -> τ_3) AND rand is τ_2) => app is τ_3

           (define fun-type (typecheck rator gamma))
           (define arg-type (typecheck rand gamma))

           (type-case Type fun-type
             [arrowT (tau2 tau3)
                     ; make sure the arg-type is tau2
                     (unless (equal? arg-type tau2)
                       (error 'typecheck "type mismatch"))
                     ; if the arg-type is tau2, then we can return tau3 as the overall type
                     tau3]
             [else
              ; if rator isn't a function, error!
              (error 'typecheck "expected function")])]
      [nil (typ)
           ; axiom/base case: output (listof typ)
           (listT typ)]
      [consl (fst rst)
             ; RULE: (fst is τ AND rst is (listof τ)) => cons is (listof τ)
             (define fst-type (typecheck fst gamma))
             (define rst-type (typecheck rst gamma))

             (type-case Type rst-type
               [listT (tau)
                      ; make sure first has type tau
                      (unless (equal? tau fst-type)
                        (error 'typecheck "type mismatch"))

                      (listT tau)]
               [else
                ; error if rst is not a list
                (error 'typecheck "expected list")])]

      [firstl (lst)
              ; RULE: lst is (listof τ) => (first lst) is τ
              (define lst-type (typecheck lst gamma))
              (type-case Type lst-type
                [listT (tau)
                       ; if we havee a list, just return that type
                       tau]
                [else
                 ; error if lst is not a list
                 (error 'typecheck "expected list")])]
      [restl (lst)
             ; RULE: lst is (listof τ) => (rest lst) is (listof τ)
             
             (define lst-type (typecheck lst gamma))
             (type-case Type lst-type
               [listT (tau)
                      (listT tau)]
               [else
                ; error if lst is not a list
                (error 'typecheck "expected list")])]
      [mtl? (lst)
            ; RULE: lst is (listof τ) => (mtl? lst) is boolean
            (define lst-type (typecheck lst gamma))

            (type-case Type lst-type
              [listT (tau)
                     ; if we have a list, just return a boolean
                     (booleanT)]
              [else
               ; error if lst is not a list
               (error 'typecheck "expected list")])]

      [makevector (size initial)
                  ; RULE: (size is number AND initial is τ) => (vectorof τ)

                  ; make sure size is a number
                  (define size-type (typecheck size gamma))
                  (unless (equal? (numberT) size-type)
                    (error 'typecheck "expected number"))

                  ; set type to be a vector of whatever initial's type is
                  (define tau (typecheck initial gamma))
                  (vectorT tau)]
      [set (vec index val)
           ; RULE: (vec is (vectorof τ) AND index is number AND val is τ) => τ
           (define vec-type (typecheck vec gamma))
           (define index-type (typecheck index gamma))

           (unless (equal? (numberT) index-type)
             (error 'typecheck "expected number"))

           (type-case Type vec-type
             [vectorT (tau)
                       
                      ; if we have a vector, just return that type, make sure val matches 
                      (define val-type (typecheck val gamma))
                      (unless (equal? val-type tau)
                        (error 'typecheck "type mismatch"))
                      tau]
             [else
              ; error if vec is not a vector
              (error 'typecheck "expected vector")])]
      [lengthl (col)
               (define col-type (typecheck col gamma))
               (type-case Type col-type
                 [listT (tau)
                        (numberT)]
                 [vectorT (tau)
                          (numberT)]
                 [else
                  ; error if vec is not a vector
                  (error 'typecheck "expected list or vector")])]

      [get (col index)
           (define index-type (typecheck index gamma))

           (unless (equal? (numberT) index-type)
             (error 'typecheck "expected number"))

           (define col-type (typecheck col gamma))
           (type-case Type col-type
             [listT (tau)
                    tau]
             [vectorT (tau)
                      tau]
             [else
              (error 'typecheck "expected list or vector")])])))

; get takes a list or a vector as its first argument, an index as its second, and returns the element at that
; index in the list or vector.
     

; helper
(define lookup-type : (symbol TypeEnv -> Type) ; so this function takes in name and type environment, and should return a type
  (lambda (name gamma) ; take in name and gamma
    (type-case TypeEnv gamma
      [mtEnv () (error 'typecheck "free identifier")] ; if gamma is empty, then we know we didn't find the type
      ; so we have a free identifier -- it wasn't defined before!
      [aBind (n type rst) ; if we have at least one binding, recurse through to find the id with matching name
             (if (equal? name n)
                 type
                 (lookup-type name rst))])))

(define (typecheck-expr a-tlfae)
  (typecheck a-tlfae (mtEnv)))
;; ----------------------------------------------------------------------

(test (typecheck-expr (parse `5))
      (parse-type `number))
(test (typecheck-expr (parse `true))
      (parse-type `boolean))
(test (typecheck-expr (parse `false))
      (parse-type `boolean))

(test (typecheck-expr (parse `{+ 2 3}))
      (parse-type `number))
(test (typecheck-expr (parse `{- 2 3}))
      (parse-type `number))
(test (typecheck-expr (parse `{+ 1 {- 2 3}}))
      (parse-type `number))

(test (typecheck-expr (parse `{= 1 {- 2 3}}))
      (parse-type `boolean))
(test (typecheck-expr (parse `{= 1 1}))
      (parse-type `boolean))
(test (typecheck-expr (parse `{= 5 (+ 2 3)}))
      (parse-type `boolean))

(test (typecheck-expr (parse `{if false 2 3}))
      (parse-type `number))
(test (typecheck-expr (parse `{if {= {+ 1 2} 3} false true}))
      (parse-type `boolean))
(test (typecheck-expr (parse `{if {= {+ 1 2} 3} 0 100}))
      (parse-type `number))




(test (typecheck-expr (parse `{fun {x : number} {+ x 5}}))
      (parse-type `(number -> number)))

(test (typecheck-expr (parse `{{fun {x : number} {+ x 5}}
                               5}))
      (parse-type `number))  ; here we apply our function, so we expect a number


(test/exn (typecheck-expr (parse `{+ 1 {fun {x : number} {+ x 5}}}))
          "expected number") ; this should error! we can't add numberT and arrowT (function)

(test/exn (typecheck-expr (parse `{5 7}))
          "expected function") ; {5 7} is like trying to apply 5 as a function and that's not real lmao


(test (typecheck-expr (parse `{fun {f : (number -> number)}
                                   {fun {x : number} {f x}}}))
      (parse-type `((number -> number) -> (number -> number))))

(test/exn (typecheck-expr (parse `{{fun {f : (number -> number)}
                                        {fun {x : number} {f x}}}
                                   3}))
          "type mismatch") ; we are expecting to pass in a function, specifically (arrowT (numberT) (numberT)), but we give it a number 3

(test (typecheck-expr (parse `{{fun {f : (number -> number)}
                                    {fun {x : number} {f x}}}
                               {fun {x : number} {+ x 5}}}))
      (parse-type `(number -> number))) ; this is valid bc we pass in a valid function , ad so we output the expected return type

(test/exn (typecheck-expr (parse `{{fun {f : (number -> number)}
                                        {fun {x : number} {f x}}}
                                   {fun {y : (number -> number)}
                                        {y 8}}}))
          "type mismatch") ; we passed in a function, but this is the wrong kind of function
; we expected (arrowT (numberT) (numberT)), but we got something that takes in a function (arrowT) as its arg, instead of a numberT

(test (typecheck-expr (parse `{{{fun {f : (number -> number)}
                                     {fun {x : number} {f x}}}
                                {fun {x : number} {+ x 5}}}
                               5}))
      (parse-type `number))



(test (typecheck-expr (parse `{nil number}))
      (parse-type `(listof number)))

(test (typecheck-expr (parse `{nil boolean}))
      (parse-type `(listof boolean)))


; add tests for everything after NIL


; cons
(test (typecheck-expr (parse `{cons {{{fun {f : (number -> number)}
                                           {fun {x : number} {f x}}}
                                      {fun {x : number} {+ x 5}}}
                                     5}
                                    {nil number}}))
      (parse-type `(listof number)))

(test/exn (typecheck-expr (parse `{cons {{{fun {f : (number -> number)}
                                               {fun {x : number} {f x}}}
                                          {fun {x : number} {+ x 5}}}
                                         5}
                                        {nil boolean}}))
          "type mismatch")

(test/exn (typecheck-expr (parse `{cons {{{fun {f : (number -> number)}
                                               {fun {x : number} {f x}}}
                                          {fun {x : number} {+ x 5}}}
                                         5}
                                        2

                                        }))
          "expected list")

                      
; first
(test (typecheck-expr (parse `{first {cons {{{fun {f : (number -> number)}
                                                  {fun {x : number} {f x}}}
                                             {fun {x : number} {+ x 5}}}
                                            5}
                                           {nil number}}}))
      (parse-type `number))

(test/exn (typecheck-expr (parse `{first {cons {{{fun {f : (number -> number)}
                                                      {fun {x : number} {f x}}}
                                                 {fun {x : number} {+ x 5}}}
                                                5}
                                               {nil boolean}}}))
          "type mismatch")

(test/exn (typecheck-expr (parse `{first 5}))
          "expected list")

; rest
(test (typecheck-expr (parse `{rest {cons {{{fun {f : (number -> number)}
                                                 {fun {x : number} {f x}}}
                                            {fun {x : number} {+ x 5}}}
                                           5}
                                          {nil number}}}))
      (parse-type `(listof number)))

(test/exn (typecheck-expr (parse `{rest {cons {{{fun {f : (number -> number)}
                                                     {fun {x : number} {f x}}}
                                                {fun {x : number} {+ x 5}}}
                                               5}
                                              {nil boolean}}}))
          "type mismatch")

(test/exn (typecheck-expr (parse `{rest 5}))
          "expected list")

; empty?
(test (typecheck-expr (parse `{empty? {cons {{{fun {f : (number -> number)}
                                                   {fun {x : number} {f x}}}
                                              {fun {x : number} {+ x 5}}}
                                             5}
                                            {nil number}}}))
      (parse-type `boolean))

(test/exn (typecheck-expr (parse `{empty? {cons {{{fun {f : (number -> number)}
                                                       {fun {x : number} {f x}}}
                                                  {fun {x : number} {+ x 5}}}
                                                 5}
                                                {nil boolean}}}))
          "type mismatch")

(test/exn (typecheck-expr (parse `{empty? 5}))
          "expected list")

; make-vector
(test (typecheck-expr (parse `{make-vector 2 {cons {{{fun {f : (number -> number)}
                                                          {fun {x : number} {f x}}}
                                                     {fun {x : number} {+ x 5}}}
                                                    5}
                                                   {nil number}}}))
      (parse-type `(vectorof (listof number))))

(test/exn (typecheck-expr (parse `{make-vector {nil number} {cons {{{fun {f : (number -> number)}
                                                                         {fun {x : number} {f x}}}
                                                                    {fun {x : number} {+ x 5}}}
                                                                   5}
                                                                  {nil number}}}))
          "expected number")

; set
(test (typecheck-expr (parse `{set
                               {make-vector 2 {cons {{{fun {f : (number -> number)}
                                                           {fun {x : number} {f x}}}
                                                      {fun {x : number} {+ x 5}}}
                                                     5}
                                                    {nil number}}}
                               2
                               {nil number}}))
      (parse-type `(listof number)))

(test/exn (typecheck-expr (parse `{set {make-vector {nil number} {cons {{{fun {f : (number -> number)}
                                                                              {fun {x : number} {f x}}}
                                                                         {fun {x : number} {+ x 5}}}
                                                                        5}
                                                                       {nil number}}}
                                       {nil number}
                                       {nil number}}

                                 ))
          "expected number")

(test/exn (typecheck-expr (parse `{set {cons {{{fun {f : (number -> number)}
                                                    {fun {x : number} {f x}}}
                                               {fun {x : number} {+ x 5}}}
                                              5}
                                             {nil number}}
                                       2
                                       {nil number}}

                                 ))
          "expected vector")

; get-list/vector
(test (typecheck-expr (parse `{get
                               {cons {{{fun {f : (number -> number)}
                                            {fun {x : number} {f x}}}
                                       {fun {x : number} {+ x 5}}}
                                      5}
                                     {nil number}}
                               10}

                             )
                      )
      (parse-type `number))

(test (typecheck-expr (parse `{get
                               {make-vector 2 {cons {{{fun {f : (number -> number)}
                                                           {fun {x : number} {f x}}}
                                                      {fun {x : number} {+ x 5}}}
                                                     5}
                                                    {nil number}}}
                               10}))
      (parse-type `(listof number)))

(test/exn (typecheck-expr (parse `{get
                                   {cons {{{fun {f : (number -> number)}
                                                {fun {x : number} {f x}}}
                                           {fun {x : number} {+ x 5}}}
                                          5}
                                         {nil number}}
                                   {nil number}}))
          "expected number")

(test/exn (typecheck-expr (parse `{get
                                   {make-vector {nil number} {cons {{{fun {f : (number -> number)}
                                                                          {fun {x : number} {f x}}}
                                                                     {fun {x : number} {+ x 5}}}
                                                                    5}
                                                                   {nil number}}}
                                   {nil number}}))
          "expected number")

(test/exn (typecheck-expr (parse `{get 30000
                                       10}))
          "expected list or vector")


(test (typecheck-expr (parse `{get {nil number}
                                       10}))
      (parse-type `number))
      

; length-list/vector
(test (typecheck-expr (parse `{length
                               {cons {{{fun {f : (number -> number)}
                                            {fun {x : number} {f x}}}
                                       {fun {x : number} {+ x 5}}}
                                      5}
                                     {nil number}}}))
      (parse-type `number))

(test (typecheck-expr (parse `{length
                               {make-vector 2 {cons {{{fun {f : (number -> number)}
                                                           {fun {x : number} {f x}}}
                                                      {fun {x : number} {+ x 5}}}
                                                     5}
                                                    {nil number}}}}))
      (parse-type `number))


(test/exn (typecheck-expr (parse `{length 30000}))
          "expected list or vector")

(test (typecheck-expr (parse `{length {nil number}}))
      (parse-type `number))