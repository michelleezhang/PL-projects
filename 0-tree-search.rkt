#lang plai

(define-type Tree
    [positive-leaf (val natural?)]
    [negative-leaf (val natural?)]
    [interior-node (left Tree?) (right Tree?)])

; contains? takes a tree and an integer and determines if that integer is present in the tree
; first, check if the positive-leaf matches the integer
; next, check if the negative-leaf matches the integer
; if not, call contains? on the two subtrees (recurses)
(define (contains? tree integer)
  (type-case Tree tree
    [positive-leaf (val) (and (equal? val integer) (>= integer 0))]
    [negative-leaf (val) (and (equal? val (* -1 integer)) (<= integer 0))]
    [interior-node (left right) (or (contains? left integer) (contains? right integer))]
    )
)

; smallest takes a tree and returns the smallest value it contains
; check the left branch and the right branch
; recursively return smallest leaves
(define (smallest tree)
  (type-case Tree tree
    [positive-leaf (val) val]
    [negative-leaf (val) (* -1 val)] 
    [interior-node (left right) (min (smallest left) (smallest right))]
  )
)

; balance takes a tree and returns whether the sum of its leaves is 0
; this function uses a helper that calculates the sum of the leaves
; then the main function returns whether the tree is balanced based on that sum
; (in the case of a single leaf, it only returns true if that leaf is 0)
(define (sum tree)
  (type-case Tree tree
    [positive-leaf (val) val]
    [negative-leaf (val) (* -1 val)] 
    [interior-node (left right) (+ (sum left) (sum right))]
  )
)
    
(define (balanced? tree)
  (type-case Tree tree
    [positive-leaf (val) (equal? val 0)]
    [negative-leaf (val) (equal? val 0)]
    [interior-node (left right) (equal? (+ (sum left) (sum right)) 0)]
  )
)

; deep-balanced? takes a tree and returns whether all its interior nodes are balanced
; a single leaf is trivially balanced
; if we have an interior node, check if both children are leaves, in which case, check if they sum to 0
; otherwise, check if the left and right branches together sum to 0
(define (deep-balanced? tree)
  (type-case Tree tree
    [positive-leaf (val) true]
    [negative-leaf (val) true]
    [interior-node (left right)
                   (if (and (or (positive-leaf? left) (negative-leaf? left)) (or (positive-leaf? right) (negative-leaf? right)))
                       (equal? (+ (sum left) (sum right)) 0)
                       (and (equal? (sum left) 0) (equal? (sum right) 0)))]
  )
)

; negate takes a tree and returns a tree where the value of each leaf of negated
(define (negate tree)
  (type-case Tree tree
    [positive-leaf (val) (negative-leaf val)] 
    [negative-leaf (val) (positive-leaf val)] 
    [interior-node (left right) (interior-node (negate left) (negate right))]
  )
)

; add takes a tree and an integer and returns a tree where the integer is added to each leaf 
(define (add tree integer)
  (type-case Tree tree
    [positive-leaf (val) (if (>= (+ val integer) 0) (positive-leaf (+ val integer)) (negative-leaf (* -1 (+ val integer))))]
    [negative-leaf (val) (if (>= (+ (* -1 val) integer) 0) (positive-leaf (+ (* -1 val) integer)) (negative-leaf (* -1 (+ (* -1 val) integer))))]
    [interior-node (left right) (interior-node (add left integer) (add right integer))] 
  )
)

; positive-thinking takes a tree and returns the same tree but with all of the negative leaves removed
; if there are only negative nodes, return false
; if we have a positive leaf, add it
; if we have a negative leaf, return false
; if we have a node, recurse:
; call positive-thinking on the left and right branches
; if both are false, then both are negative leaves, so return false
; if only one is false then it was a negative leaf, so return the other (non-negative) branch
; otherwise, both are non-negative, so add the entire node
(define (positive-thinking tree)
  (type-case Tree tree
    [positive-leaf (val) (positive-leaf val)]
    [negative-leaf (val) false]
    [interior-node (left right)
                   (local
                     [(define tree1 (positive-thinking left)) (define tree2 (positive-thinking right))]
                     (cond
                       [(and (false? tree1) (false? tree2)) false]
                       [(false? tree1) tree2]
                       [(false? tree2) tree1]
                       [else (interior-node tree1 tree2)]))]))

; trees for testing
(define wonk_tree (interior-node (interior-node (interior-node (negative-leaf 5)
                                                               (positive-leaf 1000))
                                                (positive-leaf 600032))
                                 (interior-node (positive-leaf 1)
                                                (negative-leaf 2000000))))
(define pos_tree (interior-node (interior-node (interior-node (positive-leaf 100)
                                                              (positive-leaf 10))
                                               (positive-leaf 54))
                                (interior-node (positive-leaf 1)
                                               (positive-leaf 922))))

(define neg_tree (interior-node (interior-node (interior-node (negative-leaf 100)
                                                              (negative-leaf 100))
                                               (negative-leaf 54))
                                (interior-node (negative-leaf 922)
                                               (negative-leaf 0))))

(define balanced_tree (interior-node (interior-node (negative-leaf 246)
                                                    (positive-leaf 54))
                                     (interior-node (positive-leaf 289)
                                                    (negative-leaf 97))))

(define more_balanced_tree (interior-node (interior-node (negative-leaf 42)
                                                         (positive-leaf 42))
                                          (interior-node (positive-leaf 78)
                                                         (negative-leaf 78))))

(define more_balanced_tree2 (interior-node (positive-leaf 0)
                                           (interior-node (positive-leaf 1)
                                                          (negative-leaf 1))))

(define zero_tree (interior-node (interior-node (interior-node (negative-leaf 0)
                                                               (positive-leaf 0))
                                                (positive-leaf 0))
                                 (interior-node (positive-leaf 0)
                                                (negative-leaf 0))))

; test cases
; contains? tests
(test (contains? (interior-node (interior-node (positive-leaf 5)
                                               (negative-leaf 4))
                                (positive-leaf 3))
                 -4)
      true)

(test (contains? (positive-leaf 7) 7) true)
(test (contains? (negative-leaf 7) -7) true)
(test (contains? (negative-leaf 7) 7) false)
(test (contains? (positive-leaf 7) -7) false)
(test (contains? (positive-leaf 7) 2) false)

(test (contains? wonk_tree 0) false)
(test (contains? wonk_tree -2000000) true)
(test (contains? wonk_tree 1) true)
(test (contains? wonk_tree 600032) true)
(test (contains? wonk_tree -600032) false)
(test (contains? wonk_tree -5) true)
(test (contains? wonk_tree 1000) true)
(test (contains? wonk_tree -6) false)

(test (contains? zero_tree 0) true)
(test (contains? zero_tree 100) false)
(test (contains? zero_tree -100) false)
(test (contains? zero_tree 0.5) false)
(test (contains? zero_tree -0) true)


; smallest tests
(test (smallest (positive-leaf 7)) 7)
(test (smallest (negative-leaf 0)) 0)
(test (smallest (positive-leaf 0)) 0)
(test (smallest zero_tree) 0)
(test (smallest (negative-leaf 7)) -7)
(test (smallest wonk_tree) -2000000)
(test (smallest pos_tree) 1)
(test (smallest neg_tree) -922)

; balance tests
(test (balanced? (positive-leaf 0)) true)
(test (balanced? (positive-leaf 1)) false)
(test (balanced? (negative-leaf 1)) false)
(test (balanced? zero_tree) true)
(test (balanced? wonk_tree) false)
(test (balanced? pos_tree) false)
(test (balanced? neg_tree) false)
(test (balanced? balanced_tree) true)
(test (balanced? more_balanced_tree) true)
(test (balanced? more_balanced_tree2) true)

; deep-balanced? tests
(test (deep-balanced? (positive-leaf 0)) true)
(test (deep-balanced? (positive-leaf 1)) true)
(test (deep-balanced? (negative-leaf 1)) true)
(test (deep-balanced? zero_tree) true)
(test (deep-balanced? wonk_tree) false)
(test (deep-balanced? pos_tree) false)
(test (deep-balanced? neg_tree) false)
(test (deep-balanced? balanced_tree) false)
(test (deep-balanced? more_balanced_tree) true)
(test (deep-balanced? more_balanced_tree2) true)
(test (deep-balanced? (interior-node (negative-leaf 1) (positive-leaf 1))) true)

; negate tests
(test (negate (positive-leaf 0)) (negative-leaf 0))
(test (negate (positive-leaf 1)) (negative-leaf 1))
(test (negate (negative-leaf 1)) (positive-leaf 1))
(test (negate wonk_tree) (interior-node (interior-node (interior-node (positive-leaf 5)
                                                                      (negative-leaf 1000))
                                                       (negative-leaf 600032))
                                        (interior-node (negative-leaf 1)
                                                       (positive-leaf 2000000))))

(test (negate pos_tree) (interior-node (interior-node (interior-node (negative-leaf 100)
                                                                     (negative-leaf 10))
                                                      (negative-leaf 54))
                                       (interior-node (negative-leaf 1)
                                                      (negative-leaf 922))))
(test (negate neg_tree) (interior-node (interior-node (interior-node (positive-leaf 100)
                                                                     (positive-leaf 100))
                                                      (positive-leaf 54))
                                       (interior-node (positive-leaf 922)
                                                      (positive-leaf 0))))
(test (negate balanced_tree) (interior-node (interior-node (positive-leaf 246)
                                                           (negative-leaf 54))
                                            (interior-node (negative-leaf 289)
                                                           (positive-leaf 97))))
(test (negate more_balanced_tree) (interior-node (interior-node (positive-leaf 42)
                                                                (negative-leaf 42))
                                                 (interior-node (negative-leaf 78)
                                                                (positive-leaf 78))))
(test (negate more_balanced_tree2) (interior-node (negative-leaf 0)
                                                  (interior-node (negative-leaf 1)
                                                                 (positive-leaf 1))))

; add tests
(test (add (positive-leaf 0) 0) (positive-leaf 0))
(test (add (positive-leaf 0) 1) (positive-leaf 1))
(test (add (positive-leaf 0) -1) (negative-leaf 1))
(test (add (positive-leaf 1) -1) (positive-leaf 0))
(test (add (negative-leaf 1) 1) (positive-leaf 0))
(test (add balanced_tree 200) (interior-node (interior-node (negative-leaf 46)
                                                           (positive-leaf 254))
                                            (interior-node (positive-leaf 489)
                                                           (positive-leaf 103))))
(test (add balanced_tree -200) (interior-node (interior-node (negative-leaf 446)
                                                           (negative-leaf 146))
                                            (interior-node (positive-leaf 89)
                                                           (negative-leaf 297))))
(test (add more_balanced_tree2 5) (interior-node (positive-leaf 5)
                                                 (interior-node (positive-leaf 6)
                                                                (positive-leaf 4))))
(test (add more_balanced_tree2 0) (interior-node (positive-leaf 0)
                                                 (interior-node (positive-leaf 1)
                                                                (negative-leaf 1))))
(test (add more_balanced_tree2 -1) (interior-node (negative-leaf 1)
                                                  (interior-node (positive-leaf 0)
                                                                 (negative-leaf 2))))

; positive-thinking tests
(test (positive-thinking (positive-leaf 0)) (positive-leaf 0))
(test (positive-thinking (positive-leaf 1)) (positive-leaf 1))
(test (positive-thinking (negative-leaf 1)) false)
(test (positive-thinking (negative-leaf 0)) false)
(test (positive-thinking zero_tree) (interior-node (interior-node (positive-leaf 0)
                                                                  (positive-leaf 0))
                                                   (positive-leaf 0)))
(test (positive-thinking wonk_tree) (interior-node (interior-node (positive-leaf 1000)
                                                                  (positive-leaf 600032))
                                                   (positive-leaf 1)))
(test (positive-thinking pos_tree) pos_tree)
(test (positive-thinking neg_tree) false)
(test (positive-thinking balanced_tree)  (interior-node (positive-leaf 54)
                                                        (positive-leaf 289)))
(test (positive-thinking more_balanced_tree) (interior-node (positive-leaf 42)
                                                        (positive-leaf 78)))
(test (positive-thinking more_balanced_tree2) (interior-node (positive-leaf 0)
                                                             (positive-leaf 1)))