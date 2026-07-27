#!/usr/bin/env scheme-script
;; -*- mode: scheme; coding: utf-8 -*- !#
;; Copyright (c) 2026 ufo
;; SPDX-License-Identifier: MIT
#!r6rs

(import (rnrs (6)) (ufo-match-steer))

;; A small demonstration of match-steer with a custom tree-node record.
(define-record-type tree-node
  (fields (immutable expression) (immutable children)))

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

(define (leaf expr)
  (make-tree-node expr '()))

(define sample
  (make-tree-node '(lambda (x) x)
    (list (leaf 'lambda)
          (make-tree-node '(x) (list (leaf 'x)))
          (leaf 'x))))

(display
 (match-steer tree-node-protocol sample
   [('lambda (params ...) body) (list 'lambda params body)]
   [else 'no-match]))
(newline)
