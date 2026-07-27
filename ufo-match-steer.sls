;; -*- mode: scheme; coding: utf-8 -*-
;; Copyright (c) 2026 ufo
;; SPDX-License-Identifier: MIT
#!r6rs

(library (ufo-match-steer)
  (export
    match-steer
    match-lambda-steer
    match-lambda*-steer
    match-let-steer
    match-let*-steer
    match-letrec-steer
    define-match-protocol
    make-match-protocol
    match-protocol?
    match-protocol-predicate
    match-protocol-expression-getter
    match-protocol-children-getter
    match-protocol-first-child-getter
    match-protocol-rest-children-getter
    match-protocol-first-child-setter
    match-protocol-rest-children-setter
    :_ ___ **1 =.. *.. *** ? $ struct & object get!)
  (import
    (rnrs base)
    (rnrs lists)
    (rnrs mutable-pairs)
    (rnrs hashtables)
    (rnrs records syntactic)
    (rnrs records procedural)
    (rnrs records inspection)
    (rnrs syntax-case)
    (only (chezscheme) iota syntax-error))

  ;; We declare and export the symbols used as auxiliary identifiers
  ;; in 'syntax-rules' to make them work in Chez Scheme's interactive
  ;; environment. (FBE)

  ;; Also we replaced '_' with ':_' as the special identifier matching
  ;; anything and not binding.  This is because R6RS forbids its use
  ;; as an auxiliary literal in a syntax-rules form.
  (define-syntax define-auxiliary-keyword
    (syntax-rules ()
      [(_ name)
       (define-syntax name
         (lambda (x)
           (syntax-violation #f "misplaced use of auxiliary keyword" x)))]))

  (define-syntax define-auxiliary-keywords
    (syntax-rules ()
      [(_ name* ...)
       (begin (define-auxiliary-keyword name*) ...)]))

  (define-auxiliary-keywords :_ ___ **1 =.. *.. *** ? $ struct & object get!)

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; Tree access protocol

  (define-record-type match-protocol
    (fields
      (immutable predicate)
      (immutable expression-getter)
      (immutable children-getter)
      (immutable first-child-getter)
      (immutable rest-children-getter)
      (immutable first-child-setter)
      (immutable rest-children-setter)))

  (define-syntax define-match-protocol
    (syntax-rules (predicate: expression: children: first-child: rest-children:
                   first-child-setter: rest-children-setter:)
      ((_ name
          predicate: predicate
          expression: expression
          children: children
          first-child: first-child
          rest-children: rest-children)
       (define name
         (make-match-protocol predicate expression children first-child
                                rest-children #f #f)))
      ((_ name
          predicate: predicate
          expression: expression
          children: children
          first-child: first-child
          rest-children: rest-children
          first-child-setter: first-child-setter
          rest-children-setter: rest-children-setter)
       (define name
         (make-match-protocol predicate expression children first-child
                                rest-children first-child-setter
                                rest-children-setter)))))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; Runtime protocol selection helpers

  (define (match-steer-find-protocol protocols v)
    (let loop ([ps protocols])
      (cond
        [(null? ps) #f]
        [((match-protocol-predicate (car ps)) v) (car ps)]
        [else (loop (cdr ps))])))

  (define (match-steer-tree? protocols v)
    (or (pair? v)
        (and (match-steer-find-protocol protocols v) #t)))

  (define (match-steer-null-tree? protocols v)
    (or (null? v)
        (let ([p (match-steer-find-protocol protocols v)])
          (and p (null? ((match-protocol-children-getter p) v))))))

  (define (match-steer-expression protocols v)
    (if (pair? v)
        v
        (let ([p (match-steer-find-protocol protocols v)])
          (if p
              ((match-protocol-expression-getter p) v)
              v))))

  (define (match-steer-car protocols v)
    (if (pair? v)
        (car v)
        (let ([p (match-steer-find-protocol protocols v)])
          ((match-protocol-first-child-getter p) v))))

  (define (match-steer-cdr protocols v)
    (if (pair? v)
        (cdr v)
        (let ([p (match-steer-find-protocol protocols v)])
          ((match-protocol-rest-children-getter p) v))))

  (define (match-steer-list? protocols v)
    (if (pair? v)
        (list? v)
        (let ([p (match-steer-find-protocol protocols v)])
          (and p (list? ((match-protocol-children-getter p) v))))))

  (define (match-steer-length protocols v)
    (if (pair? v)
        (length v)
        (let ([p (match-steer-find-protocol protocols v)])
          (if p
              (length ((match-protocol-children-getter p) v))
              0))))

  (define (match-steer-set-car! protocols v new)
    (if (pair? v)
        (set-car! v new)
        (let ([p (match-steer-find-protocol protocols v)])
          ((match-protocol-first-child-setter p) v new))))

  (define (match-steer-set-cdr! protocols v new)
    (if (pair? v)
        (set-cdr! v new)
        (let ([p (match-steer-find-protocol protocols v)])
          ((match-protocol-rest-children-setter p) v new))))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; force compile-time syntax errors with useful messages

  (define-syntax match-syntax-error
    (syntax-rules ()
      ((_) (syntax-error "invalid match-syntax-error usage"))
      ((_ msg . _) (syntax-error msg))))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;> \section{Syntax}

  ;;> \macro{(match-steer protocol expr (pattern . body) ...)\br{}
  ;;> (match-steer protocol expr (pattern (=> failure) . body) ...)}

  ;;> Like match, but the list/pair patterns are interpreted according to
  ;;> the tree access PROTOCOL.  PROTOCOL can be a single protocol or a
  ;;> list of protocols.

  (define-syntax match-steer
    (syntax-rules ()
      ((match-steer protocol)
       (match-syntax-error "missing match expression"))
      ((match-steer protocol atom)
       (match-syntax-error "no match clauses"))
      ((match-steer protocol-expr atom (pat . body) ...)
       (let ([protocols (let ([p protocol-expr])
                          (if (list? p) p (list p)))]
             [v atom])
         (match-steer-next protocols v (atom (set! atom)) (pat . body) ...)))))

  ;; MATCH-NEXT passes each clause to MATCH-ONE in turn with its failure
  ;; thunk, which is expanded by recursing MATCH-NEXT on the remaining
  ;; clauses.  `g+s' is a list of two elements, the get! and set!
  ;; expressions respectively.

  (define-syntax match-steer-next
    (syntax-rules (=>)
      ;; no more clauses, the match failed
      ((match-steer-next protocols v g+s)
       (error 'match-steer "no matching pattern"))
      ;; named failure continuation
      ((match-steer-next protocols v g+s (pat (=> failure) . body) . rest)
       (let ((failure (lambda () (match-steer-next protocols v g+s . rest))))
         ;; match-one analyzes the pattern for us
         (match-steer-one protocols v pat g+s (match-drop-ids (begin . body)) (failure) ())))
      ;; anonymous failure continuation, give it a dummy name
      ((match-steer-next protocols v g+s (pat . body) . rest)
       (match-steer-next protocols v g+s (pat (=> failure) . body) . rest))))

  ;; MATCH-ONE first checks for ellipsis patterns, otherwise passes on to
  ;; MATCH-TWO.

  (define-syntax match-steer-one
    (syntax-rules ()
      ;; If it's a list of two or more values, check to see if the
      ;; second one is an ellipsis and handle accordingly, otherwise go
      ;; to MATCH-TWO.
      ((match-steer-one protocols v (p q . r) g+s sk fk i)
       (match-check-ellipsis
        q
        (match-extract-vars p (match-steer-gen-ellipsis protocols v p r g+s sk fk i) i ())
        (match-steer-two protocols v (p q . r) g+s sk fk i)))
      ;; Go directly to MATCH-TWO.
      ((match-steer-one protocols . x)
       (match-steer-two protocols . x))))

  ;; This is the guts of the pattern matcher.  We are passed a lot of
  ;; information in the form:
  ;;
  ;;   (match-steer-two protocols var pattern getter setter success-k fail-k (ids ...))
  ;;
  ;; usually abbreviated
  ;;
  ;;   (match-steer-two protocols v p g+s sk fk i)
  ;;
  ;; where VAR is the symbol name of the current variable we are
  ;; matching, PATTERN is the current pattern, getter and setter are the
  ;; corresponding accessors (e.g. CAR and SET-CAR! of the pair holding
  ;; VAR), SUCCESS-K is the success continuation, FAIL-K is the failure
  ;; continuation (which is just a thunk call and is thus safe to expand
  ;; multiple times) and IDS are the list of identifiers bound in the
  ;; pattern so far.

  (define-syntax match-steer-two
    (syntax-rules (:_ ___ **1 =.. *.. *** quote quasiquote ? $ struct & object = and or not set! get!)
      ((match-steer-two protocols v () g+s (sk ...) fk i)
       (if (match-steer-null-tree? protocols v) (sk ... i) fk))
      ((match-steer-two protocols v (quote p) g+s (sk ...) fk i)
       (if (equal? (match-steer-expression protocols v) 'p) (sk ... i) fk))
      ((match-steer-two protocols v (quasiquote p) . x)
       (match-steer-quasiquote protocols v p . x))
      ((match-steer-two protocols v (and) g+s (sk ...) fk i) (sk ... i))
      ((match-steer-two protocols v (and p q ...) g+s sk fk i)
       (match-steer-one protocols v p g+s (match-steer-one protocols v (and q ...) g+s sk fk) fk i))
      ((match-steer-two protocols v (or) g+s sk fk i) fk)
      ((match-steer-two protocols v (or p) . x)
       (match-steer-one protocols v p . x))
      ((match-steer-two protocols v (or p ...) g+s sk fk i)
       (match-extract-vars (or p ...) (match-gen-or protocols v (p ...) g+s sk fk i) i ()))
      ((match-steer-two protocols v (not p) g+s (sk ...) fk i)
       (let ((fk2 (lambda () (sk ... i))))
         (match-steer-one protocols v p g+s (match-drop-ids fk) (fk2) i)))
      ((match-steer-two protocols v (get! getter) (g s) (sk ...) fk i)
       (let ((getter (lambda () g))) (sk ... i)))
      ((match-steer-two protocols v (set! setter) (g (s ...)) (sk ...) fk i)
       (let ((setter (lambda (x) (s ... x)))) (sk ... i)))
      ((match-steer-two protocols v (? pred . p) g+s sk fk i)
       (if (pred v) (match-steer-one protocols v (and . p) g+s sk fk i) fk))
      ((match-steer-two protocols v (= proc p) . x)
       (let ((w (proc v))) (match-steer-one protocols w p . x)))
      ((match-steer-two protocols v (p ___ . r) g+s sk fk i)
       (match-extract-vars p (match-steer-gen-ellipsis protocols v p r g+s sk fk i) i ()))
      ((match-steer-two protocols v (p) g+s sk fk i)
       (let ([p-found (match-steer-find-protocol protocols v)])
         (if p-found
             (if (match-steer-null-tree? protocols
                   ((match-protocol-rest-children-getter p-found) v))
                 (let ((w ((match-protocol-first-child-getter p-found) v)))
                   (match-steer-one protocols w p
                     (((match-protocol-first-child-getter p-found) v)
                      (lambda (new)
                        ((match-protocol-first-child-setter p-found) v new)))
                     sk fk i))
                 fk)
             (if (and (pair? v) (null? (cdr v)))
                 (let ((w (car v)))
                   (match-steer-one protocols w p ((car v) (set-car! v)) sk fk i))
                 fk))))
      ((match-steer-two protocols v (p *** q) g+s sk fk i)
       (match-extract-vars p (match-steer-gen-search protocols v p q g+s sk fk i) i ()))
      ((match-steer-two protocols v (p *** . q) g+s sk fk i)
       (match-syntax-error "invalid use of ***" (p *** . q)))
      ((match-steer-two protocols v (p **1) g+s sk fk i)
       (if (match-steer-tree? protocols v)
           (match-steer-one protocols v (p ___) g+s sk fk i)
           fk))
      ((match-steer-two protocols v (p =.. n . r) g+s sk fk i)
       (match-extract-vars
        p
        (match-steer-gen-ellipsis/range n n protocols v p r g+s sk fk i) i ()))
      ((match-steer-two protocols v (p *.. n m . r) g+s sk fk i)
       (match-extract-vars
        p
        (match-steer-gen-ellipsis/range n m protocols v p r g+s sk fk i) i ()))
      ((match-steer-two protocols v ($ rec p ...) g+s sk fk i)
       (if (is-a? v rec)
           (match-record-refs protocols v rec 0 (p ...) g+s sk fk i)
           fk))
      ((match-steer-two protocols v (struct rec p ...) g+s sk fk i)
       (if (is-a? v rec)
           (match-record-refs v rec 0 (p ...) g+s sk fk i)
           fk))
      ((match-steer-two protocols v (& rec p ...) g+s sk fk i)
       (if (is-a? v rec)
           (match-record-named-refs protocols v rec (p ...) g+s sk fk i)
           fk))
      ((match-steer-two protocols v (object rec p ...) g+s sk fk i)
       (if (is-a? v rec)
           (match-record-named-refs protocols v rec (p ...) g+s sk fk i)
           fk))
      ((match-steer-two protocols v (p . q) g+s sk fk i)
       (let ([p-found (match-steer-find-protocol protocols v)])
         (if p-found
             (let ((w ((match-protocol-first-child-getter p-found) v))
                   (x ((match-protocol-rest-children-getter p-found) v)))
               (match-steer-one protocols w p
                 (((match-protocol-first-child-getter p-found) v)
                  (lambda (new)
                    ((match-protocol-first-child-setter p-found) v new)))
                 (match-steer-one protocols x q
                   (((match-protocol-rest-children-getter p-found) v)
                    (lambda (new)
                      ((match-protocol-rest-children-setter p-found) v new)))
                   sk fk)
                 fk
                 i))
             (if (pair? v)
                 (let ((w (car v)) (x (cdr v)))
                   (match-steer-one protocols w p ((car v) (set-car! v))
                     (match-steer-one protocols x q ((cdr v) (set-cdr! v)) sk fk)
                     fk
                     i))
                 fk))))
      ((match-steer-two protocols v #(p ...) g+s . x)
       (match-vector protocols v 0 () (p ...) . x))
      ;; Next line: replace '_' with ':_'. (FBE)
      ((match-steer-two protocols v :_ g+s (sk ...) fk i) (sk ... i))
      ;; Not a pair or vector or special literal, test to see if it's a
      ;; new symbol, in which case we just bind it, or if it's an
      ;; already bound symbol or some other literal, in which case we
      ;; compare it with EQUAL?.
      ((match-steer-two protocols v x g+s (sk ...) fk (id ...))
       (match-check-identifier
        x
        (let-syntax
            ((new-sym?
              (syntax-rules (id ...)
                ((new-sym? x sk2 fk2) sk2)
                ((new-sym? y sk2 fk2) fk2))))
          (new-sym? random-sym-to-match
                    (let ((x v)) (sk ... (id ... x)))
                    (if (equal? (match-steer-expression protocols v) x) (sk ... (id ...)) fk)))
        (if (equal? (match-steer-expression protocols v) x) (sk ... (id ...)) fk)))
      ))

  ;; QUASIQUOTE patterns

  (define-syntax match-steer-quasiquote
    (syntax-rules (unquote unquote-splicing quasiquote or)
      ((_ protocols v (unquote p) g+s sk fk i)
       (match-steer-one protocols v p g+s sk fk i))
      ((_ protocols v ((unquote-splicing p) . rest) g+s sk fk i)
       (match-extract-vars
        p
        (match-steer-gen-ellipsis/qq protocols v p rest g+s sk fk i) i ()))
      ((_ protocols v (quasiquote p) g+s sk fk i . depth)
       (match-steer-quasiquote protocols v p g+s sk fk i #f . depth))
      ((_ protocols v (unquote p) g+s sk fk i x . depth)
       (match-steer-quasiquote protocols v p g+s sk fk i . depth))
      ((_ protocols v (unquote-splicing p) g+s sk fk i x . depth)
       (match-steer-quasiquote protocols v p g+s sk fk i . depth))
      ((_ protocols v (p . q) g+s sk fk i . depth)
       (let ([p-found (match-steer-find-protocol protocols v)])
         (if p-found
             (let ((w ((match-protocol-first-child-getter p-found) v))
                   (x ((match-protocol-rest-children-getter p-found) v)))
               (match-steer-quasiquote protocols w p g+s
                 (match-steer-quasiquote-step protocols x q g+s sk fk depth)
                 fk i . depth))
             (if (pair? v)
                 (let ((w (car v)) (x (cdr v)))
                   (match-steer-quasiquote protocols w p g+s
                     (match-steer-quasiquote-step protocols x q g+s sk fk depth)
                     fk i . depth))
                 fk))))
      ((_ protocols v #(elt ...) g+s sk fk i . depth)
       (if (vector? v)
           (let ((ls (vector->list v)))
             (match-steer-quasiquote protocols ls (elt ...) g+s sk fk i . depth))
           fk))
      ((_ protocols v x g+s sk fk i . depth)
       (match-steer-one protocols v 'x g+s sk fk i))))

  (define-syntax match-steer-quasiquote-step
    (syntax-rules ()
      ((match-steer-quasiquote-step protocols x q g+s sk fk depth i)
       (match-steer-quasiquote protocols x q g+s sk fk i . depth))))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; Utilities

  (define-syntax match-drop-ids
    (syntax-rules ()
      ((_ expr ids ...) expr)))

  (define-syntax match-tuck-ids
    (syntax-rules ()
      ((_ (letish args (expr ...)) ids ...)
       (letish args (expr ... ids ...)))))

  (define-syntax match-drop-first-arg
    (syntax-rules ()
      ((_ arg expr) expr)))

  ;; To expand an OR group we try each clause in succession, passing the
  ;; first that succeeds to the success continuation.  On failure for
  ;; any clause, we just try the next clause, finally resorting to the
  ;; failure continuation fk if all clauses fail.  The only trick is
  ;; that we want to unify the identifiers, so that the success
  ;; continuation can refer to a variable from any of the OR clauses.

  (define-syntax match-gen-or
    (syntax-rules ()
      ((_ protocols v p g+s (sk ...) fk (i ...) ((id id-ls) ...))
       (let ((sk2 (lambda (id ...) (sk ... (i ... id ...))))
             (id (if #f #f)) ...)
         (match-gen-or-step protocols v p g+s (match-drop-ids (sk2 id ...)) fk (i ...))))))

  (define-syntax match-gen-or-step
    (syntax-rules ()
      ((_ protocols v () g+s sk fk . x)
       ;; no OR clauses, call the failure continuation
       fk)
      ((_ protocols v (p) . x)
       ;; last (or only) OR clause, just expand normally
       (match-steer-one protocols v p . x))
      ((_ protocols v (p . q) g+s sk fk i)
       ;; match one and try the remaining on failure
       (let ((fk2 (lambda () (match-gen-or-step protocols v q g+s sk fk i))))
         (match-steer-one protocols v p g+s sk (fk2) i)))
      ))

  ;; We match a pattern (p ...) by matching the pattern p in a loop on
  ;; each element of the variable, accumulating the bound ids into lists.

  (define-syntax match-steer-gen-ellipsis
  (syntax-rules ()
    ;; TODO: restore fast path when p is not already bound
    ((_ protocols v p () g+s (sk ...) fk i ((id id-ls) ...))
     (match-check-identifier p
       ;; simplest case equivalent to (p ...), just match the list
       (let ((w v))
         (if (match-steer-list? protocols w)
             (match-steer-one protocols w p g+s (sk ...) fk i)
             fk))
       ;; simple case, match all elements of the list
       (let loop ((ls v) (id-ls '()) ...)
         (cond
           ((match-steer-null-tree? protocols ls)
            (let ((id (reverse id-ls)) ...) (sk ... i)))
           ((match-steer-tree? protocols ls)
            (let ((w (match-steer-car protocols ls)))
              (match-steer-one protocols w p
                  ((match-steer-car protocols ls) (match-steer-set-car! protocols ls))
                  (match-drop-ids (loop (match-steer-cdr protocols ls) (cons id id-ls) ...))
                  fk i)))
           (else
            fk)))))
    ((_ protocols v p r g+s sk fk (i ...) ((id id-ls) ...))
     (match-verify-no-ellipsis
      r
      (match-bound-identifier-memv
       p
       (i ...)
       ;; p is bound, match the list up to the known length, then
       ;; match the trailing patterns
       (let loop ((ls v) (expect p))
         (cond
          ((null? expect)
           (match-steer-one protocols ls r (#f #f) sk fk (i ...)))
          ((match-steer-tree? protocols ls)
           (let ((w (match-steer-car protocols ls))
                 (e (car expect)))
             (if (equal? (match-steer-expression protocols w)
                         (match-steer-expression protocols e))
                 (match-drop-ids (loop (match-steer-cdr protocols ls) (cdr expect)))
                 fk)))
          (else
           fk)))
       ;; general case, trailing patterns to match, keep track of
       ;; the remaining list length so we don't need any backtracking
       (let* ((tail-len (length 'r))
              (ls v)
              (len (and (match-steer-list? protocols ls) (match-steer-length protocols ls))))
         (if (or (not len) (< len tail-len))
             fk
             (let loop ((ls ls) (n len) (id-ls '()) ...)
               (cond
                ((= n tail-len)
                 (let ((id (reverse id-ls)) ...)
                   (match-steer-one protocols ls r (#f #f) sk fk (i ... id ...))))
                ((match-steer-tree? protocols ls)
                 (let ((w (match-steer-car protocols ls)))
                   (match-steer-one protocols w p
                       ((match-steer-car protocols ls) (match-steer-set-car! protocols ls))
                       (match-drop-ids
                        (loop (match-steer-cdr protocols ls) (- n 1) (cons id id-ls) ...))
                       fk
                       (i ...))))
                (else
                 fk)))
           )))))))

;; Variant of the above where the rest pattern is in a quasiquote.

(define-syntax match-steer-gen-ellipsis/qq
  (syntax-rules ()
    ((_ protocols v p r g+s (sk ...) fk (i ...) ((id id-ls) ...))
     (match-verify-no-ellipsis
      r
      (let* ((tail-len (length 'r))
             (ls v)
             (len (and (match-steer-list? protocols ls) (match-steer-length protocols ls))))
        (if (or (not len) (< len tail-len))
            fk
            (let loop ((ls ls) (n len) (id-ls '()) ...)
              (cond
               ((= n tail-len)
                (let ((id (reverse id-ls)) ...)
                  (match-steer-quasiquote ls r g+s (sk ...) fk (i ... id ...))))
               ((match-steer-tree? protocols ls)
                (let ((w (match-steer-car protocols ls)))
                  (match-steer-one protocols w p
                      ((match-steer-car protocols ls) (match-steer-set-car! protocols ls))
                      (match-drop-ids
                       (loop (match-steer-cdr protocols ls) (- n 1) (cons id id-ls) ...))
                      fk
                      (i ...))))
               (else
                fk)))))))))

;; Variant of above which takes an n/m range for the number of
;; repetitions.  At least n elements much match, and up to m elements
;; are greedily consumed.

(define-syntax match-steer-gen-ellipsis/range
  (syntax-rules ()
    ((_ %lo %hi v p r g+s (sk ...) fk (i ...) ((id id-ls) ...))
     ;; general case, trailing patterns to match, keep track of the
     ;; remaining list length so we don't need any backtracking
     (match-verify-no-ellipsis
      r
      (let* ((lo %lo)
             (hi %hi)
             (tail-len (length 'r))
             (ls v)
             (len (and (match-steer-list? protocols ls) (- (match-steer-length protocols ls) tail-len))))
        (if (and len (<= lo len hi))
            (let loop ((ls ls) (j 0) (id-ls '()) ...)
              (cond
                ((= j len)
                 (let ((id (reverse id-ls)) ...)
                   (match-steer-one protocols ls r (#f #f) (sk ...) fk (i ... id ...))))
                ((match-steer-tree? protocols ls)
                 (let ((w (match-steer-car protocols ls)))
                   (match-steer-one protocols w p
                       ((match-steer-car protocols ls) (match-steer-set-car! protocols ls))
                       (match-drop-ids
                        (loop (match-steer-cdr protocols ls) (+ j 1) (cons id id-ls) ...))
                       fk
                       (i ...))))
                (else
                 fk)))
            fk))))))

;; This is just a safety check.  Although unlike syntax-rules we allow
;; trailing patterns after an ellipsis, we explicitly disable multiple
;; ellipsis at the same level.  This is because in the general case
;; such patterns are exponential in the number of ellipsis, and we
;; don't want to make it easy to construct very expensive operations
;; with simple looking patterns.  For example, it would be O(n^2) for
;; patterns like (a ... b ...) because we must consider every trailing
;; element for every possible break for the leading "a ...".

(define-syntax match-verify-no-ellipsis
  (syntax-rules ()
    ((_ (x . y) sk)
     (match-check-ellipsis
      x
      (match-syntax-error
       "multiple ellipsis patterns not allowed at same level")
      (match-verify-no-ellipsis y sk)))
    ((_ () sk)
     sk)
    ((_ x sk)
     (match-syntax-error "dotted tail not allowed after ellipsis" x))))

;; To implement the tree search, we use two recursive procedures.  TRY
;; attempts to match Y once, and on success it calls the normal SK on
;; the accumulated list ids as in MATCH-GEN-ELLIPSIS.  On failure, we
;; call NEXT which first checks if the current value is a list
;; beginning with X, then calls TRY on each remaining element of the
;; list.  Since TRY will recursively call NEXT again on failure, this
;; effects a full depth-first search.
;;
;; The failure continuation throughout is a jump to the next step in
;; the tree search, initialized with the original failure continuation
;; FK.

(define-syntax match-steer-gen-search
  (syntax-rules ()
    ((match-steer-gen-search protocols v p q g+s sk fk i ((id id-ls) ...))
     (letrec ((try (lambda (w fail id-ls ...)
                     (match-steer-one protocols w q g+s
                                (match-tuck-ids
                                 (let ((id (reverse id-ls)) ...)
                                   sk))
                                (next w fail id-ls ...) i)))
              (next (lambda (w fail id-ls ...)
                      (if (not (match-steer-tree? protocols w))
                          (fail)
                          (let ((u (match-steer-car protocols w)))
                            (match-steer-one
                             u p ((match-steer-car protocols w) (match-steer-set-car! protocols w))
                             (match-drop-ids
                              ;; accumulate the head variables from
                              ;; the p pattern, and loop over the tail
                              (let ((id-ls (cons id id-ls)) ...)
                                (let lp ((ls (match-steer-cdr protocols w)))
                                  (if (match-steer-tree? protocols ls)
                                      (try (match-steer-car protocols ls)
                                           (lambda () (lp (match-steer-cdr protocols ls)))
                                           id-ls ...)
                                      (fail)))))
                             (fail) i))))))
       ;; the initial id-ls binding here is a dummy to get the right
       ;; number of '()s
       (let ((id-ls '()) ...)
         (try v (lambda () fk) id-ls ...))))))

;; Vector patterns are just more of the same, with the slight
;; exception that we pass around the current vector index being
;; matched.

(define-syntax match-vector
    (syntax-rules (___)
      ((_ protocols v n pats (p q) . x)
       (match-check-ellipsis q
        (match-gen-vector-ellipsis protocols v n pats p . x)
        (match-vector-two protocols v n pats (p q) . x)))
      ((_ protocols v n pats (p ___) sk fk i)
       (match-gen-vector-ellipsis protocols v n pats p sk fk i))
      ((_ protocols . x)
       (match-vector-two protocols . x))))

  ;; Check the exact vector length, then check each element in turn.

  (define-syntax match-vector-two
    (syntax-rules ()
      ((_ protocols v n ((pat index) ...) () sk fk i)
       (if (vector? v)
           (let ((len (vector-length v)))
             (if (= len n)
                 (match-vector-step protocols v ((pat index) ...) sk fk i)
                 fk))
           fk))
      ((_ protocols v n (pats ...) (p . q) . x)
       (match-vector protocols v (+ n 1) (pats ... (p n)) q . x))))

  (define-syntax match-vector-step
    (syntax-rules ()
      ((_ protocols v () (sk ...) fk i) (sk ... i))
      ((_ protocols v ((pat index) . rest) sk fk i)
       (let ((w (vector-ref v index)))
         (match-steer-one protocols w pat ((vector-ref v index) (vector-set! v index))
                   (match-vector-step protocols v rest sk fk)
                   fk i)))))

  ;; With a vector ellipsis pattern we first check to see if the vector
  ;; length is at least the required length.

  (define-syntax match-gen-vector-ellipsis
    (syntax-rules ()
      ((_ protocols v n ((pat index) ...) p sk fk i)
       (if (vector? v)
           (let ((len (vector-length v)))
             (if (>= len n)
                 (match-vector-step protocols v ((pat index) ...)
                                    (match-vector-tail protocols v p n len sk fk)
                                    fk i)
                 fk))
           fk))))

  (define-syntax match-vector-tail
    (syntax-rules ()
      ((_ protocols v p n len sk fk i)
       (match-extract-vars p (match-vector-tail-two protocols v p n len sk fk i) i ()))))

  (define-syntax match-vector-tail-two
    (syntax-rules ()
      ((_ protocols v p n len (sk ...) fk i ((id id-ls) ...))
       (let loop ((j n) (id-ls '()) ...)
         (if (>= j len)
           (let ((id (reverse id-ls)) ...) (sk ... i))
           (let ((w (vector-ref v j)))
             (match-steer-one protocols w p ((vector-ref v j) (vector-set! v j))
                       (match-drop-ids (loop (+ j 1) (cons id id-ls) ...))
                       fk i)))))))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; Cached record accessors/mutators
  ;;
  ;; Creating record accessors/mutators involves mapping field names to
  ;; indices and calling record-accessor/record-mutator.  These are
  ;; cached per RTD and field to avoid recomputing them on every match.

  (define *match-accessor-cache* (make-eq-hashtable))
  (define *match-mutator-cache* (make-eq-hashtable))

  (define (match-vector-index vec pred)
    (let loop ([i 0])
      (cond
        [(= i (vector-length vec)) #f]
        [(pred (vector-ref vec i)) i]
        [else (loop (+ i 1))])))

  (define (match-cached-accessor rtd field)
    (let ([field-table (or (hashtable-ref *match-accessor-cache* rtd #f)
                           (let ([t (make-eq-hashtable)])
                             (hashtable-set! *match-accessor-cache* rtd t)
                             t))])
      (or (hashtable-ref field-table field #f)
          (let* ([fields (record-type-field-names rtd)]
                 [idx (if (number? field)
                          field
                          (match-vector-index fields (lambda (f) (eq? f field))))]
                 [acc (record-accessor rtd idx)])
            (hashtable-set! field-table field acc)
            acc))))

  (define (match-cached-mutator rtd field)
    (let ([field-table (or (hashtable-ref *match-mutator-cache* rtd #f)
                           (let ([t (make-eq-hashtable)])
                             (hashtable-set! *match-mutator-cache* rtd t)
                             t))])
      (or (hashtable-ref field-table field #f)
          (let* ([fields (record-type-field-names rtd)]
                 [idx (if (number? field)
                          field
                          (match-vector-index fields (lambda (f) (eq? f field))))]
                 [mut (record-mutator rtd idx)])
            (hashtable-set! field-table field mut)
            mut))))

  (define-syntax is-a?
    (syntax-rules ()
      ((_ rec rtn)
       (let ((rec: rec))
        (and (record? rec:)
             (eq? (record-type-name (record-rtd rec:)) (quote rtn)))))))

  (define-syntax slot-ref
    (syntax-rules ()
      ((_ rtn rec n)
       (let ((n: n) (rec: rec))
         (if (number? n:)
             ((record-accessor (record-rtd rec:) n:) rec:)
             ;; If it's not a number, then it should be a symbol with
             ;; the name of a field.
             (let* ((rtd (record-rtd rec:))
                    (fields (record-type-field-names rtd))
                    (fields-idxs (map (lambda (f i) (cons f i))
                                      (vector->list fields)
                                      (iota (vector-length fields))))
                    (idx (cdr (assv n: fields-idxs))))
               ((record-accessor rtd idx) rec:)))))))

  (define-syntax slot-set!
    (syntax-rules ()
      ((_ rtn rec n val)
       (let ((n: n) (rec: rec))
         (if (number? n:)
             ((record-mutator (record-rtd rec:) n) rec: val)
             ;; If it's not a number, then it should be a symbol with
             ;; the name of a field.
             (let* ((rtd (record-rtd rec:))
                    (fields (record-type-field-names rtd))
                    (fields-idxs (map (lambda (f i) (cons f i))
                                      (vector->list fields)
                                      (iota (vector-length fields))))
                    (idx (cdr (assv n: fields-idxs))))
               ((record-mutator rtd idx) rec: val)))))))

  (define-syntax match-record-refs
    (syntax-rules ()
      ((_ protocols v rec n (p . q) g+s sk fk i)
       (let ((rtd (record-rtd v)))
         (let ((w ((match-cached-accessor rtd n) v)))
           (match-steer-one protocols w p (((match-cached-accessor rtd n) v) ((match-cached-mutator rtd n) v))
                      (match-record-refs protocols v rec (+ n 1) q g+s sk fk) fk i))))
      ((_ protocols v rec n () g+s (sk ...) fk i)
       (sk ... i))))

  (define-syntax match-record-named-refs
    (syntax-rules ()
      ((_ protocols v rec ((f p) . q) g+s sk fk i)
       (let ((rtd (record-rtd v)))
         (let ((w ((match-cached-accessor rtd 'f) v)))
           (match-steer-one protocols w p (((match-cached-accessor rtd 'f) v) ((match-cached-mutator rtd 'f) v))
                      (match-record-named-refs protocols v rec q g+s sk fk) fk i))))
      ((_ protocols v rec () g+s (sk ...) fk i)
       (sk ... i))))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; Extract all identifiers in a pattern.  A little more complicated
  ;; than just looking for symbols, we need to ignore special keywords
  ;; and non-pattern forms (such as the predicate expression in ?
  ;; patterns), and also ignore previously bound identifiers.
  ;;
  ;; Calls the continuation with all new vars as a list of the form
  ;; ((orig-var tmp-name) ...), where tmp-name can be used to uniquely
  ;; pair with the original variable (e.g. it's used in the ellipsis
  ;; generation for list variables).
  ;;
  ;; (match-extract-vars pattern continuation (ids ...) (new-vars ...))

  (define-syntax match-extract-vars
    (syntax-rules (:_ ___ **1 =.. *.. *** ? $ struct & object = quote quasiquote and or not get! set!)
      ((match-extract-vars (? pred . p) . x)
       (match-extract-vars p . x))
      ((match-extract-vars ($ rec . p) . x)
       (match-extract-vars p . x))
      ((match-extract-vars (struct rec . p) . x)
       (match-extract-vars p . x))
      ((match-extract-vars (& rec (f p) ...) . x)
       (match-extract-vars (p ...) . x))
      ((match-extract-vars (object rec (f p) ...) . x)
       (match-extract-vars (p ...) . x))
      ((match-extract-vars (= proc p) . x)
       (match-extract-vars p . x))
      ((match-extract-vars (quote x) (k ...) i v)
       (k ... v))
      ((match-extract-vars (quasiquote x) k i v)
       (match-extract-quasiquote-vars x k i v (#t)))
      ((match-extract-vars (and . p) . x)
       (match-extract-vars p . x))
      ((match-extract-vars (or . p) . x)
       (match-extract-vars p . x))
      ((match-extract-vars (not . p) . x)
       (match-extract-vars p . x))
      ;; A non-keyword pair, expand the CAR with a continuation to
      ;; expand the CDR.
      ((match-extract-vars (p q . r) k i v)
       (match-check-ellipsis
        q
        (match-extract-vars (p . r) k i v)
        (match-extract-vars p (match-extract-vars-step (q . r) k i v) i ())))
      ((match-extract-vars (p . q) k i v)
       (match-extract-vars p (match-extract-vars-step q k i v) i ()))
      ((match-extract-vars #(p ...) . x)
       (match-extract-vars (p ...) . x))
      ((match-extract-vars :_ (k ...) i v)    (k ... v))
      ((match-extract-vars ___ (k ...) i v)  (k ... v))
      ((match-extract-vars *** (k ...) i v)  (k ... v))
      ((match-extract-vars **1 (k ...) i v)  (k ... v))
      ((match-extract-vars =.. (k ...) i v)  (k ... v))
      ((match-extract-vars *.. (k ...) i v)  (k ... v))
      ;; This is the main part, the only place where we might add a new
      ;; var if it's an unbound symbol.
      ((match-extract-vars p (k ...) (i ...) v)
       (let-syntax
           ((new-sym?
             (syntax-rules (i ...)
               ((new-sym? p sk fk) sk)
               ((new-sym? any sk fk) fk))))
         (new-sym? random-sym-to-match
                   (k ... ((p p-ls) . v))
                   (k ... v))))
      ))

  ;; Stepper used in the above so it can expand the CAR and CDR
  ;; separately.

  (define-syntax match-extract-vars-step
    (syntax-rules ()
      ((_ p k i v ((v2 v2-ls) ...))
       (match-extract-vars p k (v2 ... . i) ((v2 v2-ls) ... . v)))
      ))

  (define-syntax match-extract-quasiquote-vars
    (syntax-rules (quasiquote unquote unquote-splicing)
      ((match-extract-quasiquote-vars (quasiquote x) k i v d)
       (match-extract-quasiquote-vars x k i v (#t . d)))
      ((match-extract-quasiquote-vars (unquote-splicing x) k i v d)
       (match-extract-quasiquote-vars (unquote x) k i v d))
      ((match-extract-quasiquote-vars (unquote x) k i v (#t))
       (match-extract-vars x k i v))
      ((match-extract-quasiquote-vars (unquote x) k i v (#t . d))
       (match-extract-quasiquote-vars x k i v d))
      ((match-extract-quasiquote-vars (x . y) k i v d)
       (match-extract-quasiquote-vars
        x
        (match-extract-quasiquote-vars-step y k i v d) i () d))
      ((match-extract-quasiquote-vars #(x ...) k i v d)
       (match-extract-quasiquote-vars (x ...) k i v d))
      ((match-extract-quasiquote-vars x (k ...) i v d)
       (k ... v))
      ))

  (define-syntax match-extract-quasiquote-vars-step
    (syntax-rules ()
      ((_ x k i v d ((v2 v2-ls) ...))
       (match-extract-quasiquote-vars x k (v2 ... . i) ((v2 v2-ls) ... . v) d))
      ))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; Gimme some sugar baby.

  ;;> Shortcut for \scheme{lambda} + \scheme{match-steer}.  Creates a
  ;;> procedure of one argument, and matches that argument against each
  ;;> clause.

  (define-syntax match-lambda-steer
    (syntax-rules ()
      ((_ protocol (pattern . body) ...)
       (lambda (expr) (match-steer protocol expr (pattern . body) ...)))))

  ;;> Similar to \scheme{match-lambda-steer}.  Creates a procedure of any
  ;;> number of arguments, and matches the argument list against each
  ;;> clause.

  (define-syntax match-lambda*-steer
    (syntax-rules ()
      ((_ protocol (pattern . body) ...)
       (lambda expr (match-steer protocol expr (pattern . body) ...)))))

  ;;> Matches each var to the corresponding expression, and evaluates
  ;;> the body with all match variables in scope.  Raises an error if
  ;;> any of the expressions fail to match.  Syntax analogous to named
  ;;> let can also be used for recursive functions which match on their
  ;;> arguments as in \scheme{match-lambda*-steer}.

  (define-syntax match-let-steer
    (syntax-rules ()
      ((_ protocol ((var value) ...) . body)
       (match-let-steer/aux protocol () () ((var value) ...) . body))
      ((_ protocol loop ((var init) ...) . body)
       (match-named-let-steer protocol loop () ((var init) ...) . body))))

  (define-syntax match-let-steer/aux
    (syntax-rules ()
      ((_ protocol ((var expr) ...) () () . body)
       (let ((var expr) ...) . body))
      ((_ protocol ((var expr) ...) ((pat tmp) ...) () . body)
       (let ((var expr) ...)
         (match-let*-steer protocol ((pat tmp) ...)
           . body)))
      ((_ protocol (v ...) (p ...) (((a . b) expr) . rest) . body)
       (match-let-steer/aux protocol (v ... (tmp expr)) (p ... ((a . b) tmp)) rest . body))
      ((_ protocol (v ...) (p ...) ((#(a ...) expr) . rest) . body)
       (match-let-steer/aux protocol (v ... (tmp expr)) (p ... (#(a ...) tmp)) rest . body))
      ((_ protocol (v ...) (p ...) ((a expr) . rest) . body)
       (match-let-steer/aux protocol (v ... (a expr)) (p ...) rest . body))))

  (define-syntax match-named-let-steer
    (syntax-rules ()
      ((_ protocol loop ((pat expr var) ...) () . body)
       (let loop ((var expr) ...)
         (match-let-steer protocol ((pat var) ...)
           . body)))
      ((_ protocol loop (v ...) ((pat expr) . rest) . body)
       (match-named-let-steer protocol loop (v ... (pat expr tmp)) rest . body))))

  ;;> \macro{(match-let*-steer protocol ((var value) ...) body ...)}

  ;;> Similar to \scheme{match-let-steer}, but analogously to \scheme{let*}
  ;;> matches and binds the variables in sequence, with preceding match
  ;;> variables in scope.

  (define-syntax match-let*-steer
    (syntax-rules ()
      ((_ protocol () . body)
       (let () . body))
      ((_ protocol ((pat expr) . rest) . body)
       (match-steer protocol expr (pat (match-let*-steer protocol rest . body))))))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; Challenge stage - unhygienic insertion.
  ;;
  ;; It's possible to implement match-letrec without unhygienic
  ;; insertion by building the let+set! logic directly into the match
  ;; code above (passing a parameter to distinguish let vs let).
  ;; However, it makes the code much more complicated, so we religate
  ;; the complexity here.

  ;;> Similar to \scheme{match-let-steer}, but analogously to \scheme{letrec}
  ;;> matches and binds the variables with all match variables in scope.

  (define-syntax match-letrec-steer
    (syntax-rules ()
      ((_ protocol ((pat val) ...) . body)
       (match-letrec-steer-one protocol (pat ...) (((pat val) ...) . body) ()))))

  ;; 1: extract all ids in all patterns
  (define-syntax match-letrec-steer-one
    (syntax-rules ()
      ((_ protocol (pat . rest) expr ((id tmp) ...))
       (match-extract-vars
        pat (match-letrec-steer-one protocol rest expr) (id ...) ((id tmp) ...)))
      ((_ protocol () expr ((id tmp) ...))
       (match-letrec-steer-two protocol expr () ((id tmp) ...)))))

  ;; 2: rewrite ids
  (define-syntax match-letrec-steer-two
    (syntax-rules ()
      ((_ protocol (() . body) ((var2 val2) ...) ((id tmp) ...))
       ;; We know the ids, their tmp names, and the renamed patterns
       ;; with the tmp names - expand to the classic letrec pattern of
       ;; let+set!.  That is, we bind the original identifiers written
       ;; in the source with let, run match on their renamed versions,
       ;; then set! the originals to the matched values.
       (let ((id (if #f #f)) ...)
         (match-let-steer protocol ((var2 val2) ...)
            (set! id tmp) ...
            . body)))
      ((_ protocol (((var val) . rest) . body) ((var2 val2) ...) ids)
       (match-rewrite
        var
        ids
        (match-letrec-steer-two-step protocol (rest . body) ((var2 val2) ...) ids val)))))

  (define-syntax match-letrec-steer-two-step
    (syntax-rules ()
      ((_ protocol next (rewrites ...) ids val var)
       (match-letrec-steer-two protocol next (rewrites ... (var val)) ids))))

  ;; This is where the work is done.  To rewrite all occurrences of any
  ;; id with its tmp, we need to walk the expression, using CPS to
  ;; restore the original structure.  We also need to be careful to pass
  ;; the tmp directly to the macro doing the insertion so that it
  ;; doesn't get renamed.  This trick was originally found by Al*
  ;; Petrofsky in a message titled "How to write seemingly unhygienic
  ;; macros using syntax-rules" sent to comp.lang.scheme in Nov 2001.

  (define-syntax match-rewrite
    (syntax-rules (quote)
      ((match-rewrite (quote x) ids (k ...))
       (k ... (quote x)))
      ((match-rewrite (p . q) ids k)
       (match-rewrite p ids (match-rewrite2 q ids (match-cons k))))
      ((match-rewrite () ids (k ...))
       (k ... ()))
      ((match-rewrite p () (k ...))
       (k ... p))
      ((match-rewrite p ((id tmp) . rest) (k ...))
       (match-bound-identifier=? p id (k ... tmp) (match-rewrite p rest (k ...))))
      ))

  (define-syntax match-rewrite2
    (syntax-rules ()
      ((match-rewrite2 q ids (k ...) p)
       (match-rewrite q ids (k ... p)))))

  (define-syntax match-cons
    (syntax-rules ()
      ((match-cons (k ...) p q)
       (k ... (p . q)))))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;; This is a little more complicated, and introduces a new let-syntax,
  ;; but should work portably in any R[56]RS Scheme.  Taylor Campbell
  ;; originally came up with the idea.
  (define-syntax match-check-ellipsis
    (syntax-rules ()
      ;; these two aren't necessary but provide fast-case failures
      ((match-check-ellipsis (a . b) success-k failure-k) failure-k)
      ((match-check-ellipsis #(a ...) success-k failure-k) failure-k)
      ;; matching an atom
      ((match-check-ellipsis id success-k failure-k)
       (let-syntax ((ellipsis? (syntax-rules ()
                                 ;; iff `id' is `...' here then this will
                                 ;; match a list of any length
                                 ((ellipsis? (foo id) sk fk) sk)
                                 ((ellipsis? other sk fk) fk))))
         ;; this list of three elements will only match the (foo id) list
         ;; above if `id' is `...'
         (ellipsis? (a b c) success-k failure-k)))))

  ;; This is portable but can be more efficient with non-portable
  ;; extensions.  This trick was originally discovered by Oleg Kiselyov.
  (define-syntax match-check-identifier
    (syntax-rules ()
      ;; fast-case failures, lists and vectors are not identifiers
      ((_ (x . y) success-k failure-k) failure-k)
      ((_ #(x ...) success-k failure-k) failure-k)
      ;; x is an atom
      ((_ x success-k failure-k)
       (let-syntax
           ((sym?
             (syntax-rules ()
               ;; if the symbol `abracadabra' matches x, then x is a
               ;; symbol
               ((sym? x sk fk) sk)
               ;; otherwise x is a non-symbol datum
               ((sym? y sk fk) fk))))
         (sym? abracadabra success-k failure-k)))))

  ;; This check is inlined in some cases above, but included here for
  ;; the convenience of match-rewrite.
  (define-syntax match-bound-identifier=?
    (syntax-rules ()
      ((match-bound-identifier=? a b sk fk)
       (let-syntax ((b (syntax-rules ())))
         (let-syntax ((eq (syntax-rules (b)
                            ((eq b) sk)
                            ((eq _) fk))))
           (eq a))))))

  ;; Variant of above for a list of ids.
  (define-syntax match-bound-identifier-memv
    (syntax-rules ()
      ((match-bound-identifier-memv a (id ...) sk fk)
       (match-check-identifier
        a
        (let-syntax
            ((memv?
              (syntax-rules (id ...)
                ((memv? a sk2 fk2) fk2)
                ((memv? anything-else sk2 fk2) sk2))))
          (memv? random-sym-to-match sk fk))
        fk))))
)
