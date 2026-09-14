# Lean 4 formalisation — disproof of conjecture `00000001752`

Core Lean only (`import Std`), no Mathlib, no `Finset`, no `sorry`, and no
`native_decide`. The project pins `lean-toolchain` to
`leanprover/lean4:v4.33.1` and defines the library `tlmc1752` in
`lakefile.toml`.

## Build and audit

```sh
lake build
lake env lean Check.lean
```

`lake build` exits `0`. `Check.lean` prints `#print axioms` for every theorem
so a reviewer can confirm the absence of `sorryAx` and of Mathlib dependencies.

## What is formalised

Conjecture `00000001752` asserts, in the parenthetical reading, that for `S_n`
acting on `k`-subsets the Burnside average equals `k!·S(n,k)/|G|` with
`|G| = n!`. Both sides have denominator `|G|`, so for `S_3`, `k = 1` the
assertion is the integer identity

```
sum_{g in S_3} Fix_1(g)  =  1! * S(3,1),
```

and the left side is `6` while the right side is `1`.

| Theorem | Statement | Role |
|:--------|:----------|:-----|
| `perms_length` | `perms.length = 6` | `S_3` has 6 elements, out of 27 functions |
| `burnsideSum_eq` | `burnsideSum = 6` | the fixed-point counts `[3,1,1,1,0,0]` sum to 6 |
| `formula_val` | `fact 1 * stirling2 3 1 = 1` | the conjectured numerator `1!·S(3,1) = 1` |
| `burnside_average_is_one` | `burnsideSum = perms.length` | Burnside's average (= orbit count) is 1 |
| `mismatch` | `burnsideSum ≠ fact 1 * stirling2 3 1` | **main result**: `6 ≠ 1`, i.e. `1 ≠ 1/6` |
| `one_ne_one_sixth_cross` | `(1 : Nat) * 6 ≠ (1 : Nat) * 1` | the unit-fraction cross-product form |

## Proof strategy

- **`isPerm`** is the Boolean test `((List.finRange 3).map f).eraseDups.length
  == 3`: a function `Fin 3 → Fin 3` is a permutation iff its three values are
  distinct. `allFuns` enumerates all `3^3 = 27` functions by their value table
  with nested `List.flatMap`/`List.map`; `perms := allFuns.filter isPerm` keeps
  the six bijections.
- **`fixCount f`** is `List.countP (fun s => f s == s) (List.finRange 3)`; for
  `k = 1` a permutation fixes the singleton `{s}` iff `f s = s`, so this is
  `Fix_1(f)`.
- **`burnsideSum`** is `(perms.map fixCount).sum`, the numerator of the
  Burnside average. Its denominator is `perms.length = |S_3| = 6`.
- **`fact`** and **`stirling2`** are hand-rolled (neither `Nat.factorial` nor
  `Finset` is available under `import Std`); `stirling2` uses the standard
  recurrence `S(n+1,k+1) = (k+1)·S(n,k+1) + S(n,k)`.
- The concrete values are kernel computations, proved by `rfl`
  (`perms_length`, `burnsideSum_eq`, `formula_val`). The **main theorem**
  `mismatch` rewrites with these and closes the resulting `Nat` goal `6 ≠ 1`
  by `decide`. Since both sides of the conjecture share the denominator `6`,
  no `Rat` (and no `decide` on rationals, which does not reduce) is needed.

## Axiom audit

`lake env lean Check.lean` reports:

```
'Tlmc1752.perms_length' depends on axioms: [propext]
'Tlmc1752.burnsideSum_eq' depends on axioms: [propext]
'Tlmc1752.formula_val' does not depend on any axioms
'Tlmc1752.burnside_average_is_one' depends on axioms: [propext]
'Tlmc1752.mismatch' depends on axioms: [propext]
'Tlmc1752.one_ne_one_sixth_cross' does not depend on any axioms
```

No `sorryAx` appears for any theorem, and no Mathlib axiom is used. The
`propext` dependency arises from the `List`/`BEq` machinery used to evaluate
the filter and the counting predicate; the two theorems that state pure
arithmetic (`formula_val`, `one_ne_one_sixth_cross`) are axiom-free.

## Scope note

- The formalised witness is **in scope**: the action of `S_3` on 1-subsets is
  the natural, sharply 2-transitive action on three points, so it lies inside
  the strict 2-transitive case of the conjecture.
- The general statement "the Burnside average is always the number of orbits,
  hence 1" is proved in prose in `../main.tex` and checked exhaustively in
  `../reproduce.py`; here the formalisation pins the decisive numerical
  mismatch to the natural number inequality `6 ≠ 1`.
- **Honest caveat (mirrors the write-up).** The conjecture is auto-generated
  and misdefines "Mark": a Mark is an integer permutation-character value,
  whereas this file equates it with a Burnside average. The formalised theorem
  refutes the definite Burnside-average equation the conjecture file writes in
  parentheses. Under the strictest reading ("`M_k` is an ATLAS Mark") the
  statement is ill-typed rather than false, and this file does not claim
  otherwise.
- The `k = 2` case for `S_3` agrees (the isolated coincidence `(3,2)`:
  `2!·S(3,2)/6 = 1`); it is not formalised, as it does not affect the verdict.

## Environment

Lean 4.33.1, Lake, no Mathlib. `lake build` needs no cache download.
