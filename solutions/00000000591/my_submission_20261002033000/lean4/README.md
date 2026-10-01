# Lean 4 verification — disproof of conjecture 00000000591

Core Lean 4 only (no Mathlib). `lakefile.toml` builds target `Main` by default.

## Build and audit

```sh
lake build
lake env lean Check.lean
```

Every `#print axioms` line in `Check.lean` must print

```
'...' does not depend on any axioms
```

There are zero `sorry` and zero axioms; all proofs are `rfl`/`decide` on concrete
`Nat`/`Bool` computations (kernel-evaluated).

## Content of `Main.lean`

`rep a b c n` (Bool) decides whether `n = x*a + y*b + z*c` has a solution in
nonnegative integers, by exhaustive bounded search over `y in [0, n/b]`,
`z in [0, n/c]` with divisibility of the remainder by `a` — sound and complete.
`countNongaps a b c upto` counts nongaps of `<a,b,c>` in `[0, upto-1]`;
`surplus n g = 3*n - g - 3` is the Wilf surplus at embedding dimension 3.

Theorem groups, one per semigroup (each big enumeration is its own theorem):

| semigroup | Frobenius g | nongaps n | surplus | ratio | theorems |
|---|---|---|---|---|---|
| `<17,23,29>` | 215 | 104 | 94 | 0.4372 | `gap_/cover_/count_/surplus_/ratio_17_23_29` |
| `<9,13,101>` | 95 | 48 | 46 | 0.4842 | `*_9_13_101` |
| `<15,33,55>` | 227 | 114 | 112 | 0.4934 | `*_15_33_55` |
| `<35,55,77>` | 603 | 302 | 300 | 0.4975 | `*_35_55_77` |

`gap_*` shows g is a gap; `cover_*` shows `multiplicity` consecutive integers
above g are nongaps (closure under addition then lifts this to all `n > g`, so g
is exactly the Frobenius number); `count_*` fixes n; `ratio_*` shows
`surplus/g > 2/5`. `main` conjoins all 20 facts.

The ratio does not tend to 0: the complete-intersection family
`<pq, pr, qr>` (p,q,r distinct primes) is symmetric, so `n = (g+1)/2` and
`surplus = (g-3)/2` exactly, giving `surplus/g = (g-3)/(2g) -> 1/2` as
`g = 2pqr - pq - pr - qr -> infinity` (verified numerically up to g = 2194011 in
`../reproduce.py`).
