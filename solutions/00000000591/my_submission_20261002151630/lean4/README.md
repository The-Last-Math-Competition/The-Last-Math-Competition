# Lean 4 formalization — disproof of TLMC conjecture 00000000591 (v2)

Core Lean 4.33.1, **no Mathlib**, **zero axioms**, **zero `sorry`**, no
`native_decide`.

## Build and audit

    export ELAN_HOME=/Users/mychanging/.workbuddy-ai/binaries/lean/elan
    export PATH="$ELAN_HOME/bin:$PATH"
    lake build
    lake env lean Check.lean

`Check.lean` prints `... does not depend on any axioms` for all 32 audited
theorems, including the main theorem `main`.

## Contents of `Main.lean`

* Closed-form definitions for the infinite family
  `S_k = ⟨6, 2*(6k+5), 3*(6k+5)⟩` (complete intersection, symmetric,
  embedding dimension 3): `frob k = 42k+29` (Frobenius number),
  `nongapCount k = 21k+15` (nongaps on `[0, g_k]`),
  `surplus k = 21k+13` (Wilf surplus `3n − g − 3`).
* `main` — the discretized negation of the conjecture's "surplus/g → 0":
  a positive rational ε = 1/3 exists such that arbitrarily far out in the
  family a member satisfies `ε.den * surplus_k ≥ ε.num * g_k`, the exact
  cross-multiplied form of `ε ≤ surplus_k/g_k` (both denominators positive).
* `zero_lt_third`, `third_le_ratio_zero`, `third_le_ratio_one` — `0 < 1/3` and,
  on ground members, the ℚ-order statement `1/3 ≤ ratio_k` itself, by
  definitional reduction of the rational order.
* `wilf_relation` — `3*n_k = g_k + surplus_k + 3`; `exact_identity` —
  `2*surplus_k*g_k = (g_k−3)*g_k` (i.e. `surplus/g = (g−3)/(2g)`); `frob_ge_nine`.
* Exhaustive-search anchoring certificates (`rep`, `countNongaps`, `gap_*`,
  `cover_*`, `count_*`) that the closed formulas agree with the actual
  semigroups at `k = 0` (`g = 29`, `n = 15`) and `k = 1` (`g = 71`, `n = 36`).

## Why the symbolic inequality is cross-multiplied

Core Lean's ℚ-order reduces to boolean cross-multiplication of the `num`/`den`
fields, and core `Rat` literals carry `propext`/`Quot.sound` through their
`by decide` coprimality fields (`omega` and `simp` are avoided for the same
reason). All arithmetic on the family is therefore done with a small
self-contained axiom-free toolkit (`myLeftDistrib`, `myMulAdd`, `myMulAssoc`,
`myAddPair`, `myShuffle`) plus `Nat.le.intro`/`Nat.succ_pos`/`Nat.add_assoc`/
`Nat.add_left_comm`/`Nat.mul_comm` — verified axiom-free — and the ℚ-order is
formalized in full on the ground members `13/29` and `34/71`.
