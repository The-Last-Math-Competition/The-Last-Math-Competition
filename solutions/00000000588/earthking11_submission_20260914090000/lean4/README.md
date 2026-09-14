# Lean 4 formalisation — disproof of conjecture `00000000588`

Core Lean only: **`Main.lean` has no imports at all** (not even `Std`), uses no
Mathlib and no `sorry`. The project pins `lean-toolchain` to
`leanprover/lean4:v4.33.1` and defines the library `Main` in `lakefile.toml`.

## Build and audit

```sh
lake build
lake env lean Check.lean
```

`Check.lean` prints `#print axioms` for every theorem so a reviewer can confirm
the absence of `sorryAx` and of any dependency (Mathlib or otherwise). Because
`Main.lean` is import-free, the formalisation is self-contained: nothing beyond
the Lean prelude is used.

## What is formalised

The conjecture defines the type `t(S)` as the number of maximal Apéry elements.
For the counterexample `n = 4`, `S = ⟨4,5,6,7⟩`:

| Object | Definition |
|:-------|:-----------|
| `inS x` | `∃ a b c d, x = 4a + 5b + 6c + 7d` |
| `inAp x` | `x = 0 ∨ x = 5 ∨ x = 6 ∨ x = 7`, i.e. `Ap(S,4) = {0,5,6,7}` |
| `ltS x y` | `x < y ∧ inS (y - x)` — the strict Apéry order |
| `isMax x` | `inAp x ∧ ∀ y, inAp y → ¬ ltS x y` |
| `maximals` | the list `[5,6,7]` |
| `t` | `maximals.length` |

| Theorem | Statement | Role |
|:--------|:----------|:-----|
| `not_inS_1`, `not_inS_2`, `not_inS_3` | `¬ inS 1`, `¬ inS 2`, `¬ inS 3` | `1,2,3` are gaps (by `omega`) |
| `inS_0`, `inS_5`, `inS_6`, `inS_7` | `inS 0`, … | the elements of the Apéry set lie in `S` |
| `not_isMax_0` | `¬ isMax 0` | `0 <_S 5`, so `0` is not maximal |
| `isMax_5`, `isMax_6`, `isMax_7` | `isMax x` for `x = 5,6,7` | the three nonzero Apéry elements are pairwise incomparable |
| `maximals_correct` | `(∀ x, x ∈ maximals → isMax x) ∧ (∀ x, isMax x → x ∈ maximals)` | the maximal set is exactly `{5,6,7}` |
| `t_eq_3` | `t = 3` | by `rfl` (the list length) |
| `t_ne_two` | `t ≠ 2` | by `decide` |
| `counterexample_n4` | `t = 3 ∧ t ≠ 2` | **main refutation**: `t = 3` but `⌈4/2⌉ = 2` |
| `maximals3_correct`, `conjecture_holds_n3` | `t3 = 2` | `n = 3` happens to satisfy the claim (`2 = ⌈3/2⌉`) |
| `maximals5_correct`, `counterexample_n5` | `t5 = 4 ∧ t5 ≠ 3` | `n = 5` fails again (`4 ≠ ⌈5/2⌉ = 3`) |

## Proof strategy

- **Gaps.** `not_inS_k` (`k = 1,2,3`) destructures the existential representing
  `k` as `4a+5b+6c+7d` and closes with `omega`.
- **Incomparability.** For `isMax_5`, expand `isMax` and `inAp`; the Apéry
  element `y` is one of `0,5,6,7`. The cases `y = 0` and `y = 5` contradict
  `5 < y` (`simp only [ltS] at hlt` then `omega`); the cases `y = 6` and `y = 7`
  give `y - 5 = 1` resp. `2`, excluded by `not_inS_1` / `not_inS_2`. The proofs
  for `6` and `7` are analogous. `not_isMax_0` witnesses `0 <_S 5`.
- **The list is complete.** `maximals_correct` splits into the two inclusions:
  elements of the list are maximal (the three lemmas), and a maximal element has
  `inAp x`, i.e. `x ∈ {0,5,6,7}`; `x = 0` is excluded by `not_isMax_0` and the
  other three are literally in the list (`decide`).
- **The type.** `t = maximals.length = 3` holds by `rfl`; `t ≠ 2` is a closed
  `decide`, so `counterexample_n4 : t = 3 ∧ t ≠ 2` is axiom-free.

The instances `n = 3` and `n = 5` repeat the same scheme with generators
`3,4,5` (`Ap = {0,4,5}`, `t = 2`) and `5,6,7,8,9` (`Ap = {0,6,7,8,9}`,
`t = 4`), confirming that the conjecture holds at `n = 3` but already fails at
`n = 4`, and fails again at `n = 5`.

## Axiom audit

`lake build` exits `0`. `lake env lean Check.lean` reports:

- `t_eq_3`, `t_ne_two`, `counterexample_n4`, `conjecture_holds_n3`,
  `counterexample_n5`: **does not depend on any axioms**;
- `not_inS_1/2/3`, `not_isMax_0`, `isMax_5/6/7`, `maximals_correct`,
  `maximals3_correct`, `maximals5_correct`: only the core axioms `propext` and
  `Quot.sound`;
- **no `sorryAx`** for any theorem, and no Mathlib axiom of any kind.

## Scope note

- The refutation is a **single explicit counterexample** with a fully formal,
  axiom-free value computation: the Apéry set, the order, the maximal set, and
  the resulting `t = 3 ≠ 2` are all proved, not merely `#eval`-ed.
- The general closed form `t(⟨n,…,2n−1⟩) = n − 1` is proved in the write-up and
  verified computationally for `n = 2..12` by `reproduce.py`; it is not
  formalised for symbolic `n` in Lean. That is not needed: one counterexample
  suffices to disprove the universally quantified closed form.
- `Ap` is taken with respect to the multiplicity (the smallest positive element,
  here `4`). This is the standard convention; `README.md` and `main.tex` record
  the robustness check showing the type is unchanged for other moduli.

## Environment

Lean 4.33.1, Lake, no dependencies, no Mathlib, no imports in `Main.lean`.
`lake build` needs no cache download.
