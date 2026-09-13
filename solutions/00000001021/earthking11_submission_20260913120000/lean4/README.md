# Lean 4 formalisation (`tlmc1021`)

Core Lean 4 only: `import Std`, no Mathlib, no `sorry`, no `axiom`, no
`native_decide`. Toolchain pinned to `leanprover/lean4:v4.33.1`.

Build and audit:

```sh
export PATH="/opt/homebrew/bin:$PATH"
lake build
lake env lean Check.lean
```

## What is formalised

`Main.lean` (namespace `Tlmc1021`) formalises the **counting core** of the
disproof of conjecture 00000001021.

* Forced layer arithmetic. `outDeg`, `layer`, `treeSize` encode the BFS
  branching `3, 5, 2, 5, 2, ...` from a degree-3 variable root:
  * `layer_sizes` : the six layers are `1, 3, 15, 30, 150, 300`;
  * `layer_sum`   : `1 + 3 + 15 + 30 + 150 + 300 = 499`;
  * `treeSize_five` : `treeSize 5 = 499`;
  * `too_small`   : `132 < treeSize 5`;
  * `treeSize_mono` : `treeSize 5 <= treeSize 10`.
* Concrete alternating tree. `Tree` is an inductive type whose constructors
  encode the node shapes forced by the alternation — `rootV` (degree-3
  variable root, arity 3), `check` (non-root degree-6 check node, arity 5),
  `varN` (non-root degree-3 variable node, arity 2), and `leaf` (truncation).
  `Tree.size` is the vertex count, `full`/`fullCheck`/`fullVar` build the
  complete truncated tree, and `treeSizeFull_five` proves the radius-5 tree
  has exactly 499 vertices as a cardinality of a genuine inductive type (not
  merely arithmetic).
* `conjecture_00000001021_false` collects the layer facts, `treeSize 5 = 499`,
  `treeSizeFull 5 = 499`, `132 < 499`, and the statement that no `n = 132` can
  satisfy `499 <= n` — an arithmetic obstruction to the claimed minimum.

`Check.lean` runs `#print axioms` for every theorem.

## What is NOT formalised

* **Graphs.** Core Lean/Std (no Mathlib) has no `SimpleGraph`, and we avoid
  `Finset`; the formalisation never defines a Tanner graph, its girth, or BFS
  on a graph.
* **The collision lemma.** The key graph-theoretic step — "if girth >= 12 then
  no two vertices at distance <= 5 from a fixed vertex can coincide, so the
  radius-5 ball is a tree" — is **proved in `main.tex` and checked
  computationally in `reproduce.py`, not in Lean.** Lean therefore proves the
  arithmetic of the forced layers and the cardinality of the alternating tree;
  the reduction from a girth-12 Tanner graph to that tree is the documented
  mathematical input.

## Axiom audit

`lake env lean Check.lean` prints, for each theorem, that it
`does not depend on any axioms`. In particular there is no `sorryAx` and no
`Lean.ofReduceBool` (which `native_decide` would introduce).
