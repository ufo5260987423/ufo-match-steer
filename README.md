# ufo-match-steer

[![License: MIT](https://img.shields.io/badge/License-MIT-blue.svg)](LICENSE)
[![Version: 1.1.4](https://img.shields.io/badge/Version-1.1.4-green.svg)]()

A generic pattern-matching library for Chez Scheme (R6RS).  It extends the
Alex-Shinn-style `match` macro so that list/pair patterns can be applied to
*any* tree-like data structure via a configurable tree-access protocol.

This is especially useful for matching record-based ASTs — for example, the
`index-node` structures used by `scheme-langserver` — without forcing them to
be ordinary Scheme pairs.

## Features

- Pattern matching over arbitrary tree structures through a `match-protocol`.
- Familiar Alex-Shinn-style patterns:
  variables, `:_`, literals, `quote`, `quasiquote`, vectors
- Ellipsis variants: `...`, `___`, `**1`, `=..`, `*..`, `***`
- Logic/combinators: `and`, `or`, `not`
- Predicates and transformers: `?`, `:=`
- Mutability support: `set!`, `get!`
- Record-matching keywords (`$`, `struct`, `&`, `object`) are reserved for a
  future design and currently disabled.

## Installation

The package is managed with [Akku](https://akkuscm.org/).  After cloning,
install dependencies and activate the environment:

```bash
akku install
source .akku/bin/activate
```

## How it works

Alex Shinn's `match` macro decomposes list/pair patterns with fixed
operations such as `car`, `cdr`, `pair?` and `null?`.  `ufo-match-steer`
takes the same pattern language but replaces those fixed operations with a
configurable **tree-access protocol**.

A `match-protocol` bundles the seven operations the matcher needs:

| Operation | Role |
|-----------|------|
| `predicate` | test whether a value belongs to the tree type |
| `expression-getter` | fetch the "datum" stored at a node |
| `children-getter` | fetch the list of children |
| `first-child-getter` | fetch the first child |
| `rest-children-getter` | fetch the remaining children |
| `first-child-setter` | mutate the first child (for `set!`) |
| `rest-children-setter` | mutate the remaining children (for `set!`) |

The matcher never calls Scheme's `car`/`cdr` directly on the input value.
Instead it calls the protocol accessors.  As a result, ordinary Scheme pairs
are *not* accepted by a protocol by default — the input must be a node
recognized by the protocol's predicate, or a wrapped tail produced by the
protocol itself.  This makes it safe to match record-based ASTs whose
internal shape is isomorphic to an S-expression but which are not themselves
Scheme pairs.

## Quick start

Define a record and a matching protocol, then use `match-steer`:

```scheme
(import (rnrs (6))
        (ufo-match-steer))

(define-record-type tree-node
  (fields expression children))

(define (tree-node-first-child n)
  (car (tree-node-children n)))

(define (tree-node-rest-children n)
  (cdr (tree-node-children n)))

(define tree-node-protocol
  (make-match-protocol
    tree-node?              ; predicate
    tree-node-expression    ; expression-getter
    tree-node-children      ; children-getter
    tree-node-first-child   ; first-child-getter
    tree-node-rest-children ; rest-children-getter
    #f                      ; first-child-setter (optional)
    #f))                    ; rest-children-setter (optional)

(define (leaf expr)
  (make-tree-node expr '()))

(define (tn expr . children)
  (make-tree-node expr children))

;; Match a lambda-like tree node.
(match-steer tree-node-protocol
  (tn '(lambda (x) x)
      (leaf 'lambda)
      (tn '(x) (leaf 'x))
      (leaf 'x))
  [('lambda params body) (list params body)]
  [else 'no-match])
;; => ((#<tree-node>) #<tree-node>)
```

## Supported patterns

| Pattern | Meaning |
|---------|---------|
| `x` | bind variable |
| `:_` | wildcard, no binding |
| `'datum` | literal equality |
| `` `form `` | quasiquote pattern |
| `#(p ...)` | vector pattern |
| `(p ...)` | list/tree decomposition |
| `(p ... rest)` | ellipsis |
| `(p ___ rest)` | same as `...` |
| `(p **1)` | one or more repetitions |
| `(p =.. n)` | exactly `n` repetitions |
| `(p *.. n m)` | between `n` and `m` repetitions |
| `(p *** q)` | deep tree search |
| `(? pred . p)` | predicate guard |
| `(:= proc p)` | transform value before matching |
| `(and p ...)` | all patterns must match |
| `(or p ...)` | any pattern matches |
| `(not p)` | negation |
| `(set! s)` | bind setter |
| `(get! g)` | bind getter |

## Running tests

```bash
bash test.sh
```

All 62 tests should pass.

## Known issues

- **`(p *** q)` may miss targets that are the first/only child of a node.**

  The tree-search pattern only finds `q` when it lies on a path of *last*
  children.  For example, with ordinary lists this corresponds to:

  ```scheme
  (match '(a (b (c target)))
    [(p *** 'target) 'found]
    [else 'else])
  ;; => found

  (match '(target)
    [(p *** 'target) 'found]
    [else 'else])
  ;; => else        (expected: found)

  (match '(target other)
    [(p *** 'target) 'found]
    [else 'else])
  ;; => else        (expected: found)
  ```

  This is inherited from the upstream Alex Shinn `match` implementation on
  which `ufo-match-steer` is based.  It is a limitation of the current
  `match-gen-search` / `match-steer-gen-search` algorithm, not specific to
  protocol trees.

## Changelog

### 1.1.4

- Fixed macro expansion error when `syntax` is used as a quoted literal
  pattern (e.g. `'syntax`) or as a pattern variable.  This was caused by
  nested `syntax-rules` tricks that placed the user's identifier into the
  rule header of an inner macro; Chez Scheme treats `syntax` as a core
  keyword in that position.  The affected helpers
  (`match-check-ellipsis`, `match-check-identifier`,
  `match-bound-identifier-memv`, and the variable-binding code in
  `match-steer-two` / `match-extract-vars`) now use `syntax-case` or a
  shared `match-identifier-memv` helper that keeps the identifier in the
  literal list instead.
- Fixed bound-variable comparison so that repeated occurrences of the
  same variable in a pattern (e.g. `(a a)` or `(syntax syntax)`) are
  compared via the protocol's expression getter rather than comparing an
  expression to the bound node object.
- Fixed ellipsis patterns `(p ...)` and `(p **1)` on protocol nodes so
  that the variable `p` binds to the list of children rather than to the
  whole node object.  This makes the behavior consistent with ordinary
  `match` ellipsis semantics and with positional decomposition patterns
  such as `(p1 p2 p3)`.
- Fixed `**1` (one-or-more repetition) so that it no longer matches
  empty protocol trees.  It now correctly requires at least one child
  element.
- Added regression tests for `syntax` literal/variable patterns and for
  `**1` wildcard matching on empty and non-empty tree nodes.

## License

MIT © 2026 ufo.  See [LICENSE](LICENSE) for details.
