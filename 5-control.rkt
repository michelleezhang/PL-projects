#lang plai

;<EFAE> = <num>
;       | {+ <EFAE> <EFAE>}
;       | {- <EFAE> <EFAE>}
;       | <id>
;       | {fun {<id>} <EFAE>}
;       | {<EFAE> <EFAE>} ;; function application
;       | {if0 <EFAE> <EFAE> <EFAE>}
;       | {throw <id> <EFAE>}
;       | {try <EFAE1> {catch {tag <id1> as <id2>} <EFAE2>}}

(define-type EFAE
  [num (n number?)]
  [add (lhs EFAE?) (rhs EFAE?)]
  [sub (lhs EFAE?) (rhs EFAE?)]
  [id (name symbol?)] 
  [fun (param symbol?) (body EFAE?)] ; create fun (param) body
  [app (fun-expr EFAE?) (arg-expr EFAE?)] ; execute fun-exp with arg-exp
  [if0 (tst EFAE?) (thn EFAE?) (els EFAE?)]
  [throw (tag symbol?) (throw-expr EFAE?)]
  [try-catch (try-body EFAE?) (tag symbol?) (exn-name symbol?) (catch-body EFAE?)])


(define-type EFAE-Value
  [numV (n number?)]
  [closureV (param-name symbol?)
            (body EFAE?)
            (ds DefSub?)]
  ;[throwV (tag symbol?) (throw-expr EFAE?)]
  )

(define-type DefSub
  [mtSub]
  [aSub  (name symbol?)
         (value EFAE-Value?)
         (rest DefSub?)])

; parser

(define (parse s-exp)
  (cond
    [(number? s-exp)
     (num s-exp)]
    [(symbol? s-exp)
     (id s-exp)]
    [(list? s-exp)
     (when (empty? s-exp)
       (error 'parse "the empty list is not a valid EFAE"))
     (case (first s-exp)
       [(+)
        (check-pieces s-exp "add" 3)
        (add (parse (second s-exp))
             (parse (third s-exp)))]
       [(-)
        (check-pieces s-exp "sub" 3)
        (sub (parse (second s-exp))
             (parse (third s-exp)))]
       [(fun)
        (check-pieces s-exp "fun" 3)
        (check-pieces (second s-exp) "parameter" 1)
        (fun (first (second s-exp)) ; (second s-exp) is a list, so call first to access the actual item
             (parse (third s-exp)))]
       [(if0)
        
        (check-pieces s-exp "if0" 4)
        (if0 (parse (second s-exp))
             (parse (third s-exp))
             (parse (fourth s-exp)))]
       [(throw)
        (check-pieces s-exp "throw" 3)
        (throw (second s-exp)
               (parse (third s-exp)))]
       [(try)
        (check-pieces s-exp "try-catch" 3)
        (try-catch (parse (second s-exp))
                   (second (second (third s-exp)))
                   (fourth (second (third s-exp)))
                   (parse (third (third s-exp))))]  
       [else
        (check-pieces s-exp "app" 2)
        (app (parse (first s-exp))
             (parse (second s-exp)))] ; app or error
       )]))

(define (check-pieces s-exp expected n-pieces)
  (unless (and (list? s-exp)
               (= n-pieces (length s-exp)))
    (error 'parse "expected ~a got ~a" expected s-exp)))



;; interp-test : s-expression -> KFAE-Value?
(define (interp-expr an-efae)
  (interp an-efae (mtSub)
          (lambda (final-val)
            (type-case EFAE-Value final-val
              [numV (n) n]
              [closureV (param-name body ds)
                        'function])
           ; final-val
              )
          (lambda (tag ret-val)
            (error 'interp "missing catch") ;??
            )))

; so k is an expression that returns whatever u give it
; ret-k returns an error

;; interp : KFAE? DefSub? (KFAE-Value? -> KFAE-Value?) (KFAE-Value? -> KFAE-Value?) -> KFAE-Value?
(define (interp a-kfae ds k ret-k)
  (type-case EFAE a-kfae
    [num (n) (k (numV n))]
    [id (name) (k (lookup name ds))]
    [fun (param-name body) (k (closureV param-name body ds))]
    [add (l r) (numop + l r ds k ret-k)]
    [sub (l r) (numop - l r ds k ret-k)]
    [app (fun-expr arg-expr)
         (interp fun-expr ds
                 (lambda (fun-val)
                   (interp arg-expr ds
                           (lambda (arg-val)
                             (type-case EFAE-Value fun-val
                               [closureV (param-name body closed-ds)
                                         (interp body
                                                 (aSub param-name arg-val closed-ds)
                                                 ;k
                                                 (lambda (ret-val)
                                                   (k ret-val))
                                                 ret-k
;                                                 (lambda (ret-val)
;                                                   (k ret-val))
                                                 )]
                               [else (error 'interp "expected function, got ~a" fun-val)]))
                           ret-k))
                 ret-k)]
    [if0 (tst thn els)
         (interp tst ds
                 (lambda (tst)
                   (if (and (numV? tst) (equal? (numV 0) tst))
                       (interp thn ds k ret-k)
                       (interp els ds k ret-k)))
                 ret-k)]
    [throw (tag throw-expr)
           ; first, interpret the throw-expr
           (interp throw-expr ds
                   ; if our throw-expr works, go to ret-k and apply our throw-expr
                   (lambda (throw-expr)
                     (ret-k tag throw-expr))
                   
                   ; otherwise move on to ret-k 
;                   (lambda (tag throw-expr)
;                     (ret-k tag throw-expr))
                   ret-k)]
    [try-catch (try-body tag exn-name catch-body)
               ; first, interpret the try-body
               (interp try-body ds
                       ; if our try body works, then yay! apply the try-body to k
                       (lambda (i-try-body)
                         (k i-try-body))
                       (lambda (tag-throw i-try-body)
                         ; otherwise, we had an exception! so interp the catch body
                         (if (equal? tag-throw tag)
                             (interp catch-body (aSub exn-name i-try-body ds)
                                     k ; atp, try-body is throw val 
                                     ret-k)
                             (ret-k tag-throw i-try-body))))]))

;; numop : (number? number? -> number?) KFAE? KFAE? DefSub?
;;         (KFAE-Value? -> KFAE-Value?)
;;         (KFAE-Value? -> KFAE-Value?)
;;            -> KFAE-Value?
(define (numop op l r ds k ret-k)
  (interp l ds
          (lambda (l-val)
            (interp r ds
                    (lambda (r-val)
                      (unless (numV? l-val)
                        (error 'interp "expected number, got ~a" l-val))
                      (unless (numV? r-val)
                        (error 'interp "expected number, got ~a" r-val))
                      (k (numV (op (numV-n l-val) (numV-n r-val)))))
                    ret-k))
          ret-k))

;; lookup : symbol? DefSub? -> KFAE-Value?
(define (lookup name ds)
  (type-case DefSub ds
    [mtSub () (error "free identifier")]
    [aSub (name2 value rest)
          (if (equal? name name2)
              value
              (lookup name rest))]))


(test (interp-expr (parse '{try {if0 {throw a 0} 1 2}
                                {catch {tag a as b} {+ 5 10}}}))
      15)

(test (interp-expr (parse '{try {if0 {throw a 0} 1 2}
                                {catch {tag a as b} 7}}))
      7)

(test (interp-expr (parse `{+ 2 {try {+ 4 {throw x 5}}
                                     {catch {tag x as e} {+ 3 e}}}}))

      10)

(test (interp-expr (parse `{try {+ 2 {try {+ 3 {throw y 5}}
                                          {catch {tag x as e} {+ 6 e}}}}
                                {catch {tag y as e} {+ 10 e}}}))
      15)

;{with {x E1} E2} -> {{fun {x} E2} E1}

(test (interp-expr (parse `{{fun {f} {try {throw a {+ {f 3} 10}}
                                     {catch {tag a as j} {+ j 5}}}}
                                {fun {x} {throw a {+ x 1}}}})) 9)

(test (interp-expr
       (parse
        `(try
          (try (throw b (throw a 1)) (catch (tag a as x) 2))
          (catch (tag b as x) 3)))) 2)

(test/exn (interp-expr (parse `{try {throw a 1} {catch {tag a as b} {throw a 1}}}))
"missing catch")

(test (interp-expr (parse `{if0 0 1 2}))
      1)