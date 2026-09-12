# lean4 — Disproof of TLMC conjecture 00000001854

Lean 4 formalization of the numeric core of the `n = 1, q = 2` counterexample.

## Build and audit

```sh
lake build
lake env lean Check.lean
```

`lake build` compiles `Main.lean`; `Check.lean` prints the axiom profile of
every theorem. Expected output: each theorem `does not depend on any axioms`
(no `sorryAx`, no `propext`, no `Classical.choice`, no `Quot.sound`).

## What is proved (zero axioms, zero `sorry`)

| theorem            | statement                                                                        |
|--------------------|----------------------------------------------------------------------------------|
| `count_q2`         | enumerating `Mat_1(F_2)` and filtering by squarefree charpoly leaves `2` matrices |
| `formula_num_q2`   | conjectured formula numerator at `n = 1, q = 2` is `2`                            |
| `formula_den_q2`   | conjectured formula denominator at `n = 1, q = 2` is `2`                          |
| `formula_value_q2` | the formula fraction equals `1` exactly (`2 / 2 = 1`)                             |
| `refute`           | `2 ≠ 1` — the true count differs from the formula value                           |
| `count_ne_formula` | exact cross-multiplied inequality `2 * den ≠ num` between count and formula       |

All are `rfl`/`decide` proofs over kernel-computable `Nat` arithmetic.

## Honest scope

Lean 4 core has no `Polynomial` library (it lives in Mathlib, which this
project intentionally does not depend on), and core `Rat` operations do not
reduce inside the kernel. The squarefreeness of the degree-one characteristic
polynomials `X − a` is therefore *encoded* (`sqfree1b`, true for every `a`)
rather than derived inside Lean, and the formula value is encoded as an exact
fraction `formulaNum / formulaDen` over `Nat`. The mathematical justification
— a degree-one polynomial has derivative `1`, hence `gcd(f, f') = 1` — is
given in `Main.lean`'s module docstring, in the package `README.md`/`main.tex`,
and is verified computationally (via an actual gcd computation) by
`reproduce.py` for `q = 2, 3, 4, 5`. Everything that *is* formalized is
computable and axiom-free.
