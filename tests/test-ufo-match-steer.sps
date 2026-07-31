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

;; Ordinary Scheme pairs/lists are never matched by a protocol matcher.
(test-error "ordinary list rejected by tree-node protocol"
  (match-steer tree-node-protocol
    '(1 2 3)
    [(a b c) (list b c)]
    [else 'no-match]))

(test-error "ordinary list with ellipsis rejected"
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

;; P1/P2/P3 tests for pattern features, advanced patterns, mutable
;; protocol, and empty-list matching.

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

(test-equal "**1 does not match empty non-tree value"
  'empty
  (match-steer tree-node-protocol
    '()
    [(a **1) 'non-empty]
    [else 'empty]))

(test-equal "=.. exact repetition"
  '(a a a)
  (node-exprs
   (match-steer tree-node-protocol
     (tn 'expr (leaf 'a) (leaf 'a) (leaf 'a))
     [(a =.. 3) a]
     [else 'no-match])))

(test-equal "*.. range repetition"
  '(a a)
  (node-exprs
   (match-steer tree-node-protocol
     (tn 'expr (leaf 'a) (leaf 'a))
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

(test-equal "empty list pattern on ordinary null does not match"
  'non-empty
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

;; Additional boundary and edge-case tests.

(define (catch-error thunk)
  (guard (e (else 'error-raised))
    (thunk)
    'no-error))

(test-equal "no matching pattern raises error"
  'error-raised
  (catch-error
   (lambda ()
     (match-steer tree-node-protocol (leaf 'x)
       ['no-such 'ok]))))

(test-equal "=.. too few elements falls through"
  'too-few
  (match-steer tree-node-protocol
    (list (leaf 'a) (leaf 'a))
    [(a =.. 3) a]
    [else 'too-few]))

(test-equal "=.. too many elements falls through"
  'too-many
  (match-steer tree-node-protocol
    (list (leaf 'a) (leaf 'a) (leaf 'a) (leaf 'a))
    [(a =.. 3) a]
    [else 'too-many]))

(test-equal "*.. below minimum falls through"
  'below-min
  (match-steer tree-node-protocol
    (list (leaf 'a))
    [(a *.. 2 4) a]
    [else 'below-min]))

(test-equal "*.. above maximum falls through"
  'above-max
  (match-steer tree-node-protocol
    (list (leaf 'a) (leaf 'a) (leaf 'a) (leaf 'a) (leaf 'a))
    [(a *.. 2 4) a]
    [else 'above-max]))

(test-equal "*** captures path variables"
  '(a b c)
  (node-exprs
   (match-steer tree-node-protocol
     (tn '(a (b (c target)))
         (leaf 'a)
         (tn '(b (c target))
             (leaf 'b)
             (tn '(c target)
                 (leaf 'c)
                 (leaf 'target))))
     [(path *** 'target) path]
     [else 'no-match])))

(test-equal "get! pattern on tree-node"
  '(lambda x y)
  (match-steer tree-node-protocol
    (tn '(lambda (x) y) (leaf 'lambda) (leaf 'x) (leaf 'y))
    [((get! g) b c)
     (list (tree-node-expression (g))
           (tree-node-expression b)
           (tree-node-expression c))]
    [else 'no-match]))

(test-assert "match-protocol? recognizes protocol"
  (match-protocol? tree-node-protocol))

(test-equal "match-protocol-predicate works"
  #t
  ((match-protocol-predicate tree-node-protocol) (leaf 'x)))

(test-equal "match-protocol-expression-getter works"
  'x
  ((match-protocol-expression-getter tree-node-protocol) (leaf 'x)))

(test-equal "match-protocol-children-getter works"
  '()
  ((match-protocol-children-getter tree-node-protocol) (leaf 'x)))

(test-equal "match-protocol-first-child-getter works"
  'a
  ((match-protocol-expression-getter tree-node-protocol)
   ((match-protocol-first-child-getter tree-node-protocol)
    (tn '(a b) (leaf 'a) (leaf 'b)))))

(test-equal "match-protocol-rest-children-getter works"
  '(b)
  (map tree-node-expression
       ((match-protocol-rest-children-getter tree-node-protocol)
        (tn '(a b) (leaf 'a) (leaf 'b)))))

(test-equal "match-protocol setters are #f for immutable tree-node"
  '(#f #f)
  (list
   (match-protocol-first-child-setter tree-node-protocol)
   (match-protocol-rest-children-setter tree-node-protocol)))

(test-equal "? predicate without subpattern"
  'node
  (match-steer tree-node-protocol
    (leaf 'x)
    [(? tree-node?) 'node]
    [else 'no-match]))

(test-equal "or variable unification"
  'x
  (match-steer tree-node-protocol
    'x
    [(or (and n (? symbol?)) n) n]
    [else 'no-match]))

(test-equal "and with not"
  42
  (match-steer tree-node-protocol
    42
    [(and n (not (? symbol?))) n]
    [else 'no-match]))

(test-equal "top-level set! pattern"
  'new
  (let ([v 'original])
    (match-steer tree-node-protocol v
      [(set! s) (s 'new) v]
      [else 'no-match])))

(test-equal "literal mismatch falls through"
  'no
  (match-steer tree-node-protocol
    (leaf 'x)
    ['y 'ok]
    [else 'no]))

(test-equal "vector length mismatch falls through"
  'no-match
  (match-steer tree-node-protocol
    '#(1 2 3)
    [#(a b) 'short]
    [else 'no-match]))

(test-equal "ellipsis on empty non-tree value does not match"
  'no-match
  (match-steer tree-node-protocol
    '()
    [(a ...) a]
    [else 'no-match]))

(test-equal "ellipsis on empty tree-node children binds whole node"
  'x
  (tree-node-expression
   (match-steer tree-node-protocol
     (leaf 'x)
     [(a ...) a]
     [else 'no-match])))

(test-equal "large ellipsis matching does not overflow"
  100
  (length
   (match-steer tree-node-protocol
     (apply tn 'expr (map leaf (iota 100)))
     [(a =.. 100) a]
     [else 'no-match])))

(define (raising-setter)
  (error 'setter "setter should not be called during non-mutating match"))

(define no-setter-protocol
  (make-match-protocol
    tree-node?
    tree-node-expression
    tree-node-children
    tree-node-first-child
    tree-node-rest-children
    raising-setter
    raising-setter))

(test-equal "normal patterns do not call setters"
  'x
  (tree-node-expression
   (match-steer no-setter-protocol
     (tn '(lambda (x) x)
         (leaf 'lambda)
         (tn '(x) (leaf 'x))
         (leaf 'x))
     [('lambda params body) body]
     [else 'no-match])))

(test-end)

(exit (if (zero? (test-runner-fail-count (test-runner-get))) 0 1))
