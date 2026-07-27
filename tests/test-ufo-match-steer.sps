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

(test-end)

(exit (if (zero? (test-runner-fail-count (test-runner-get))) 0 1))
