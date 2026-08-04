# ufo-match-steer

[![License: MIT](https://img.shields.io/badge/License-MIT-blue.svg)](LICENSE)

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

All 52 tests should pass.

## License

MIT © 2026 ufo.  See [LICENSE](LICENSE) for details.
