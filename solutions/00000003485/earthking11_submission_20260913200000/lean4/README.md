# Lean 4 formalisation — disproof of conjecture `00000003485`

Core Lean only (`import Std`), no Mathlib, no `sorry`. The project pins
`lean-toolchain` to `leanprover/lean4:v4.33.1` and defines the library `Main` in
`lakefile.toml`.

## Build and audit

```sh
lake build
lake env lean Check.lean
```

`Check.lean` prints `#print axioms` for every theorem so a reviewer can confirm
the absence of `sorryAx` and of Mathlib dependencies. `Eval.lean` is an optional
demo that `#eval`s the computed facts.

## What is formalised

The conjecture asserts that every digraph with bounded out-degree and (directed)
girth at least five has a kernel. A kernel is a set `S` that is *independent* (no
arc in either direction between two members of `S`) and *out-stable* (every
vertex outside `S` has an arc into `S`).

The witness is the directed `5`-cycle `C₅` on `Fin 5` with arcs
`i → i + 1 (mod 5)`. Its arcs are the decidable predicate

```lean
def arc5 (i j : Fin 5) : Bool := decide (j = i + 1)
```

and a subset of `Fin 5` is represented as its indicator function
`S : Fin 5 → Bool`. The kernel conditions are the `Bool`-valued predicates

```lean
def independent5 (S : Fin 5 → Bool) : Bool :=
  !(S 0 && S 1) && !(S 1 && S 2) && !(S 2 && S 3) && !(S 3 && S 4) && !(S 4 && S 0)

def outStable5 (S : Fin 5 → Bool) : Bool :=
  (S 0 || S 1) && (S 1 || S 2) && (S 2 || S 3) && (S 3 || S 4) && (S 4 || S 0)

def kernel5 (S : Fin 5 → Bool) : Bool := independent5 S && outStable5 S
```

(the independence clauses are exactly the five unordered pairs joined by an arc;
the out-stability clauses use that each vertex has the single out-neighbour
`i + 1`).

| Theorem | Statement | Role |
|:--------|:----------|:-----|
| `outdeg5_le_one` | `(V5.map outDeg5).all (· ≤ 1) = true` | bounded out-degree (in fact every out-degree is `1`) |
| `outdeg5_eq_one` | `(V5.map outDeg5).all (· = 1) = true` | the out-degree bound holds sharply |
| `girth5_ge_five` | no directed closed walk of length `1,2,3,4` | directed girth `≥ 5` |
| `girth5_le_five` | `walk5 5 0 0 = true` | the `5`-cycle, so directed girth `= 5` |
| `no_kernel5` | `∀ S : Fin 5 → Bool, kernel5 S = false` | **`C₅` has no kernel** (all `2^5 = 32` subsets) |
| `no_kernel5_exists` | `¬ HasKernel5` | negation form |
| `kernelMasks5_nil` | `kernelMasks5 = []` | explicit brute force over the `32` bitmasks |
| `kernelMasks5_count` | `kernelMasks5.length = 0` | count form |
| `no_kernel3` | `∀ S : Fin 3 → Bool, kernel3 S = false` | `C₃` has no kernel (`8` subsets) |
| `no_kernel7` | `∀ S : Fin 7 → Bool, kernel7 S = false` | `C₇` has no kernel (`128` subsets) |
| `C5_in_class` | hypotheses of the conjecture hold for `C₅` | bounded out-degree and girth `≥ 5` |
| `conjecture_00000003485_false` | hypotheses hold but `¬ HasKernel5` | the refutation |
| `conjecture_00000003485_refuted` | conjunction of all of the above | collected disproof |

## Proof strategy

- `arc5 i j` is `decide (j = i + 1)`; `Fin 5` addition is modular, so this is the
  cyclic successor.
- `walk5 k i j` is defined by recursion on `k`: a walk of length `0` is `i = j`,
  and a walk of length `k+1` is a walk of length `k` to some `m` followed by the
  arc `m → j`. `decide` evaluates `girth5_ge_five` and `girth5_le_five`.
- The key theorem `no_kernel5` is proved by `cases` on the five values
  `S 0, …, S 4`: this is an exhaustive split of the `2^5 = 32` subsets. Lean
  substitutes the values into the goal, and each of the `32` resulting closed
  `Bool` expressions is discharged by `decide`. No `Fintype`, `Finset`, or
  function extensionality is needed — the argument never compares two functions.
- `kernelMasks5` repeats the same brute force as an explicit `List.range 32`
  filter, so the "`32` subsets" count is also a literal computation.
- `no_kernel5_exists` derives the negation from `no_kernel5` with `Bool.noConfusion`.
- `no_kernel3` and `no_kernel7` repeat the split for `8` and `128` subsets.

The general theorem — *a directed cycle has a kernel iff its length is even* — is
proved by the alternating-set argument in `main.tex` and is documented here as
the family containing the concrete witnesses; it is not formalised beyond
`C₃`, `C₅`, `C₇`.

## Scope note

"Bounded out-degree" is witnessed by the sharpest possible bound: every vertex of
`C₅` has out-degree exactly `1`, so `outdeg5_eq_one` implies `outdeg5_le_one`.
"Girth at least five" is witnessed for the directed girth (`girth5_ge_five` plus
`girth5_le_five`); the underlying undirected graph of `C₅` is a `5`-cycle, so the
claim also fails under the undirected reading of "girth". Since the conjecture is
a universal implication, one counterexample refutes it.

## Environment

Lean 4.33.1, Lake, no Mathlib. `lake build` needs no cache download.
