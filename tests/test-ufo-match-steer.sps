#!/usr/bin/env scheme-script
;; -*- mode: scheme; coding: utf-8 -*- !#
;; Copyright (c) 2026 ufo
;; SPDX-License-Identifier: MIT
#!r6rs

(import (rnrs (6))
        (srfi :64 testing)
        (ufo-match-steer))

(test-begin "ufo-match-steer")

;; Define a simple tree-node record that stores an S-expression and a
;; list of child tree-nodes.  The S-expression structure is isomorphic
;; to the children structure.
(define-record-type tree-node
  (fields
    (immutable expression)
    (immutable children)))

(define (tree-node-first-child node)
  (car (tree-node-children node)))

(define (tree-node-rest-children node)
  (cdr (tree-node-children node)))

(define tree-node-protocol
  (make-match-protocol
    tree-node?
    tree-node-expression
    tree-node-children
    tree-node-first-child
    tree-node-rest-children
    #f
    #f))

;; Helper to build a tree-node from an expression and a list of children.
(define (tn expr . children)
  (make-tree-node expr children))

;; Helper to build a leaf tree-node.
(define (leaf expr)
  (make-tree-node expr '()))

;; Helper to compare tree-node expressions in assertions.
(define (node-exprs nodes)
  (map tree-node-expression nodes))

;; Recursive helper for nested lists of tree-nodes.
(define (tree-expr x)
  (if (tree-node? x)
      (tree-node-expression x)
      (map tree-expr x)))

;; Basic list pattern matching on tree nodes.
;; Variables are bound to child tree-nodes, so we compare expressions.
(test-equal "match tree-node list pattern"
  '((x) x)
  (node-exprs
   (match-steer tree-node-protocol
     (tn '(lambda (x) x)
         (leaf 'lambda)
         (tn '(x) (leaf 'x))
         (leaf 'x))
     [('lambda params body) (list params body)]
     [else 'no-match])))

;; Nested tree-node matching.
(test-equal "match nested tree-node"
  'x
  (tree-node-expression
   (match-steer tree-node-protocol
     (tn '(lambda (x) x)
         (leaf 'lambda)
         (tn '(x) (leaf 'x))
         (leaf 'x))
     [('lambda (params ...) body) body]
     [else 'no-match])))

;; Ellipsis matching on tree nodes.
(test-equal "match tree-node ellipsis"
  '(((x)) x)
  (tree-expr
   (match-steer tree-node-protocol
     (tn '(lambda (x) x)
         (leaf 'lambda)
         (tn '(x) (leaf 'x))
         (leaf 'x))
     [('lambda args ... body) (list args body)]
     [else 'no-match])))

;; Literal matching uses the expression field.
(test-equal "match tree-node literal"
  'x
  (tree-node-expression
   (match-steer tree-node-protocol
     (tn '(lambda (x) x)
         (leaf 'lambda)
         (tn '(x) (leaf 'x))
         (leaf 'x))
     [('lambda (x) body) body]
     [else 'no-match])))

;; Fallback to ordinary pairs/lists when value is not a tree-node.
(test-equal "fallback to ordinary list"
  '(2 3)
  (match-steer tree-node-protocol
    '(1 2 3)
    [(a b c) (list b c)]
    [else 'no-match]))

;; Fallback to ordinary pairs with ellipsis.
(test-equal "fallback with ellipsis"
  '(2 3)
  (match-steer tree-node-protocol
    '(1 2 3)
    [(a b ...) b]
    [else 'no-match]))

;; A leaf tree-node is matched by the catch-all variable pattern.
;; The variable is bound to the tree-node itself.
(test-equal "tree-node with leaf expression match"
  'x
  (tree-node-expression
   (match-steer tree-node-protocol
     (leaf 'x)
     [x x]
     [else 'no-match])))

;; Record patterns ($ struct & object) are reserved for a future design
;; and disabled in the library.  Kept here as a placeholder.
;;
;; (test-equal "record pattern on tree-node"
;;   '(expr ())
;;   (match-steer tree-node-protocol
;;     (leaf 'expr)
;;     [($ tree-node expr children) (list expr children)]
;;     [else 'no-match]))

;; Quasiquote pattern on tree-node.
(test-equal "quasiquote on tree-node"
  'x
  (tree-node-expression
   (match-steer tree-node-protocol
     (tn '(lambda (x) x)
         (leaf 'lambda)
         (tn '(x) (leaf 'x))
         (leaf 'x))
     [`(lambda (x) ,body) body]
     [else 'no-match])))

;; P0 tests for the core derived macros and multi-protocol support.

(test-equal "match-lambda-steer"
  '(x y)
  (tree-node-expression
   ((match-lambda-steer tree-node-protocol
      [('lambda params body) params]
      [else 'no-match])
    (tn '(lambda (x y) z)
        (leaf 'lambda)
        (tn '(x y) (leaf 'x) (leaf 'y))
        (leaf 'z)))))

(test-equal "match-lambda*-steer"
  '(a b c)
  (node-exprs
   ((match-lambda*-steer tree-node-protocol
      [(a b c) (list a b c)]
      [else 'no-match])
    (leaf 'a) (leaf 'b) (leaf 'c))))

(test-equal "match-let-steer parallel bindings"
  '(x y z)
  (node-exprs
   (match-let-steer tree-node-protocol
     ([(a b) (list (leaf 'x) (leaf 'y))]
      [c (leaf 'z)])
     (list a b c))))

(test-equal "match-let*-steer sequential bindings"
  'x
  (match-let*-steer tree-node-protocol
    ([(a) (list (leaf 'x))]
     [b (tree-node-expression a)])
    b))

(test-equal "match-let-steer named let recursive sum"
  6
  (match-let-steer tree-node-protocol sum ([n 3] [acc 0])
    (if (= n 0)
        acc
        (sum (- n 1) (+ acc n)))))

(test-equal "match-letrec-steer mutually recursive functions"
  #t
  (match-letrec-steer tree-node-protocol
    ([(even? odd?)
      (list
       (lambda (n) (if (= n 0) #t (odd? (- n 1))))
       (lambda (n) (if (= n 0) #f (even? (- n 1)))))])
    (even? 10)))

;; A second record type to test multi-protocol matching.
(define-record-type box-node
  (fields
    (immutable expression)
    (immutable child)))

(define (box-node-first-child node)
  (box-node-child node))

(define (box-node-rest-children node)
  '())

(define box-node-protocol
  (make-match-protocol
    box-node?
    box-node-expression
    (lambda (node) (list (box-node-child node)))
    box-node-first-child
    box-node-rest-children
    #f
    #f))

(test-equal "match-steer with multiple protocols"
  '(inner)
  (node-exprs
   (match-steer (list tree-node-protocol box-node-protocol)
     (make-box-node 'tree-box (leaf 'inner))
     [('lambda params body) params]
     [(x) (list x)]
     [else 'no-match])))

;; P1/P2/P3 tests for pattern features, advanced patterns, mutable
;; protocols, and empty-list matching.

(test-equal "? predicate pattern with subpattern"
  '((x) x)
  (let ([node (tn '(lambda (x) x)
                  (leaf 'lambda)
                  (tn '(x) (leaf 'x))
                  (leaf 'x))])
    (node-exprs
     (match-steer tree-node-protocol node
       [(? tree-node? ('lambda params body)) (list params body)]
       [else 'no-match]))))

(test-equal "= pattern transforms value before matching"
  '((x) x)
  (match-steer tree-node-protocol
    (tn '(lambda (x) x)
        (leaf 'lambda)
        (tn '(x) (leaf 'x))
        (leaf 'x))
    [(= tree-node-expression ('lambda params body)) (list params body)]
    [else 'no-match]))

(test-equal "and pattern"
  'x
  (tree-node-expression
   (match-steer tree-node-protocol
     (leaf 'x)
     [(and n (? tree-node?)) n]
     [else 'no-match])))

(test-equal "or pattern"
  'ok
  (match-steer tree-node-protocol
    (leaf 'a)
    [(or 'a 'b) 'ok]
    [else 'no-match]))

(test-equal "not pattern"
  'not-symbol
  (match-steer tree-node-protocol
    (leaf 42)
    [(= tree-node-expression (not (? symbol?))) 'not-symbol]
    [else 'no-match]))

(test-equal "vector pattern"
  '(2 3)
  (match-steer tree-node-protocol
    '#(1 2 3)
    [#(a b c) (list b c)]
    [else 'no-match]))

(test-equal "vector ellipsis pattern"
  '(2 3)
  (match-steer tree-node-protocol
    '#(1 2 3)
    [#(a b ...) b]
    [else 'no-match]))

(test-equal "*** tree search"
  'found
  (match-steer tree-node-protocol
    (tn '(a (b (c target)))
        (leaf 'a)
        (tn '(b (c target))
            (leaf 'b)
            (tn '(c target)
                (leaf 'c)
                (leaf 'target))))
    [(x *** 'target) 'found]
    [else 'not-found]))

(test-equal "**1 non-empty repetition matches whole value"
  '(a x y)
  (tree-node-expression
   (match-steer tree-node-protocol
     (tn '(a x y) (leaf 'a) (leaf 'x) (leaf 'y))
     [(a **1) a]
     [else 'no-match])))

(test-equal "**1 does not match empty ordinary list"
  'empty
  (match-steer tree-node-protocol
    '()
    [(a **1) 'non-empty]
    [else 'empty]))

(test-equal "=.. exact repetition"
  '(a a a)
  (node-exprs
   (match-steer tree-node-protocol
     (list (leaf 'a) (leaf 'a) (leaf 'a))
     [(a =.. 3) a]
     [else 'no-match])))

(test-equal "*.. range repetition"
  '(a a)
  (node-exprs
   (match-steer tree-node-protocol
     (list (leaf 'a) (leaf 'a))
     [(a *.. 1 3) a]
     [else 'no-match])))

(test-equal "quasiquote unquote-splicing"
  '((x y))
  (node-exprs
   (match-steer tree-node-protocol
     (tn '(lambda (x y) body)
         (leaf 'lambda)
         (tn '(x y) (leaf 'x) (leaf 'y))
         (leaf 'body))
     [`(lambda ,@ps body) ps]
     [else 'no-match])))

(test-equal "nested quasiquote"
  'x
  (tree-node-expression
   (match-steer tree-node-protocol
     (tn '(quote x) (leaf 'quote) (leaf 'x))
     [`(quote ,x) x]
     [else 'no-match])))

;; Mutable record and protocol for set!/get! testing.
(define-record-type mutable-node
  (fields
    (mutable expression)
    (mutable children)))

(define (mutable-node-first-child node)
  (car (mutable-node-children node)))

(define (mutable-node-rest-children node)
  (cdr (mutable-node-children node)))

(define (set-mutable-node-first-child! node new)
  (set-mutable-node-children! node (cons new (cdr (mutable-node-children node)))))

(define (set-mutable-node-rest-children! node new)
  (set-mutable-node-children! node (cons (car (mutable-node-children node)) new)))

(define mutable-node-protocol
  (make-match-protocol
    mutable-node?
    mutable-node-expression
    mutable-node-children
    mutable-node-first-child
    mutable-node-rest-children
    set-mutable-node-first-child!
    set-mutable-node-rest-children!))

(define (mn expr . children)
  (make-mutable-node expr children))

(define (mleaf expr)
  (make-mutable-node expr '()))

(test-equal "mutable protocol get! pattern"
  '(x)
  (let ([m (mn '(lambda (x) x)
               (mleaf 'lambda)
               (mn '(x) (mleaf 'x))
               (mleaf 'x))])
    (mutable-node-expression
     (match-steer mutable-node-protocol m
       [('lambda (get! g) body) (g)]
       [else 'no-match]))))

(test-equal "mutable protocol set! pattern"
  '(lambda (y z) x)
  (let ([m (mn '(lambda (x) x)
               (mleaf 'lambda)
               (mn '(x) (mleaf 'x))
               (mleaf 'x))])
    (match-steer mutable-node-protocol m
      [('lambda (set! s) body)
       (s (mn '(y z) (mleaf 'y) (mleaf 'z)))
       (map mutable-node-expression (mutable-node-children m))]
      [else 'no-match])))

(test-equal "empty list pattern on ordinary null"
  'empty
  (match-steer tree-node-protocol
    '()
    [() 'empty]
    [else 'non-empty]))

(test-equal "named failure continuation => uses current branch"
  'matched
  (match-steer tree-node-protocol
    (tn '(x y z) (leaf 'x) (leaf 'y) (leaf 'z))
    [(a b c) (=> fail)
     (if (eq? 'x (tree-node-expression a)) 'matched (fail))]
    [else 'fallback]))

(test-equal "named failure continuation => falls through"
  'fallback
  (match-steer tree-node-protocol
    (tn '(a b c) (leaf 'a) (leaf 'b) (leaf 'c))
    [(a b c) (=> fail)
     (if (eq? 'x (tree-node-expression a)) 'matched (fail))]
    [else 'fallback]))

(test-equal "empty list pattern on null tree-node"
  'empty
  (match-steer tree-node-protocol
    (leaf 'x)
    [() 'empty]
    [else 'non-empty]))

(test-end)

(exit (if (zero? (test-runner-fail-count (test-runner-get))) 0 1))
