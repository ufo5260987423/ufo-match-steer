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

;; Record pattern still works on tree-node fields.
(test-equal "record pattern on tree-node"
  '(expr ())
  (match-steer tree-node-protocol
    (leaf 'expr)
    [($ tree-node expr children) (list expr children)]
    [else 'no-match]))

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

(test-equal "match-named-let-steer recursive sum"
  6
  ;; match-named-let-steer is exported as the auxiliary behind
  ;; match-let-steer's named-let form; its direct syntax includes an
  ;; empty accumulator before the binding clauses.
  (match-named-let-steer tree-node-protocol sum () ([n 3] [acc 0])
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

(test-end)

(exit (if (zero? (test-runner-fail-count (test-runner-get))) 0 1))
