# Lean 4 formalisation — disproof of conjecture `00000001142`

Core Lean only (`import Std`), no Mathlib, no `sorry`. The project pins
`lean-toolchain` to `leanprover/lean4:v4.33.1` and defines the library `Main`
in `lakefile.toml`.

## Build and audit

```sh
timeout 300 lake build
timeout 120 lake env lean Check.lean
```

Measured on the author's machine (Apple silicon, Lean 4.33.1):

| Command | Wall time | Peak RSS |
|:--------|:----------|:---------|
| `lake build` | **≈ 50 s** (47.5 s on the final clean build; 59.8 s and 63.9 s on two earlier clean builds) | ≈ 4.4 GB |
| `lake env lean Check.lean` | < 1 s (reuses the built `.olean`) | — |

The build stays comfortably under the 120 s budget. It is a pure **kernel**
`decide` reduction; `native_decide` is **not** used (see the disclosure below).

## What is formalised

The conjecture asserts `|Aut(W(1;1))| = p(p-1)` for the mod-`p` Witt algebra
`W(1;1) = Der(F_p[x]/(x^p))`, whose `p` basis elements `b_k = x^k d/dx`
(`k = 0, ..., p-1`) satisfy

```
[b_k, b_l] = (l - k) * b_{k+l-1}   if 1 <= k+l <= p,   else 0.
```

The Lean component refutes the claim at **p = 3** by exhaustive search.

| Theorem | Statement |
|:--------|:----------|
| `num_mats` | `allMats.length = 3 ^ 9` — the search really covers 19683 matrices |
| `aut_count_3` | `auts3.length = 24` — exactly 24 invertible bracket-preserving matrices |
| `claim_false_3` | `auts3.length ≠ 3 * (3 - 1)` — the conjectured value 6 does not occur |

## How the enumeration works (faithful, not hardcoded)

* A `3 × 3` matrix over `F_3` is coded by a single `Nat` `m < 3^9 = 19683`
  whose base-3 digits are the nine entries in row-major order.
* Only the **definition** of the algebra is written down: the three
  coordinates of `[X,Y]` are the bilinear forms read off the nine structure
  constants of `W(1;1)` at `p = 3`,
  `[X,Y]_0 = x0*y1 + 2*x1*y0`, `[X,Y]_1 = 2*x0*y2 + x2*y0`,
  `[X,Y]_2 = x1*y2 + 2*x2*y1`.
* `isAut m` tests invertibility (`detG m ≠ 0`, cofactor rule mod 3) and bracket
  preservation on the nine basis pairs (`presG`).
* `auts3 = (List.range (3^9)).filter isAut` is computed by the kernel; the
  count **24** is genuinely computed, not asserted.

In numbers: of the `3^9 = 19683` matrices over `F_3`, exactly
`|GL(3,3)| = 11232` are invertible, and exactly **24** of those preserve the
bracket. The conjecture predicts `p(p-1) = 6`, so it is false at `p = 3`.

## Why the kernel route is fast enough

The naive prototype (lists of nine `Nat`s, `List.getD`, `List.foldl`) took
`14 min 12 s` of kernel time. The shipped version reduces this to ≈ 50 s by

* coding the matrix as one base-3 `Nat` and reading the nine digits with
  constant literal divisors (`% 3`, `/ 3 % 3`, ...);
* inlining the structure constants so that the hot path contains no
  `List.getD`, no `List.foldl`, no closures, and no `Finset`/`Matrix`/`ZMod`
  (none of which are in `import Std` anyway);
* short-circuiting on the determinant first (`&&`), so bracket preservation is
  tested only on the 11232 invertible matrices;
* `set_option maxRecDepth 1000000` and `set_option maxHeartbeats 0`.

## Axiom audit

`lake env lean Check.lean` reports:

```
'Tlmc1142.Witt3.num_mats' does not depend on any axioms
'Tlmc1142.Witt3.aut_count_3' does not depend on any axioms
'Tlmc1142.Witt3.claim_false_3' does not depend on any axioms
```

No `sorryAx`, and no `Lean.ofReduceBool`: the enumeration is kernel `decide`,
not `native_decide`.

## Scope note

* **p = 3 is fully covered here.** The claim is also false for **every** `p ≥ 3`;
  the case `p = 5` (`|Aut| = 500 ≠ 20`) is proved by an exact exhaustive
  computation in `../reproduce.py` and stated in `../main.tex`, because the
  analogous Lean enumeration would require `5^25` matrices and is infeasible.
* The claim happens to be **true at p = 2** (`|Aut| = 2 = p(p-1)`); this is
  verified in `../reproduce.py`.
* The modelling is faithful: only the algebra's structure-constant table is
  supplied by hand; the number 24 is the output of the search.

## Environment

Lean 4.33.1, Lake, no Mathlib and no cache download. `lake build` needs no
network access.
