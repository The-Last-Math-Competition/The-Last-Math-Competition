# Lean 4 verification — conjecture 00000001367 (FALSE)

This directory contains a core-Lean (`import Std`, **no Mathlib**) formalisation of
the refutation of conjecture 00000001367.

## Build and check

```sh
cd lean4
lake build
lake env lean Check.lean
```

`lean-toolchain` pins `leanprover/lean4:v4.33.1`.  The build uses no `sorry`, no
`axiom`, and no `native_decide`.

## What is formalised

`Main.lean` (namespace `Tlmc1367`):

| Name | Statement |
|------|-----------|
| `Adj` | Grid adjacency on `Z × Z`: `q = (p.1+1, p.2) ∨ q = (p.1-1, p.2) ∨ q = (p.1, p.2+1) ∨ q = (p.1, p.2-1)`. |
| `col` | The parity coloring `p ↦ Int.toNat ((p.1 + p.2) % 2) : Nat`. |
| `parity_proper` | `∀ p q, Adj p q → col p ≠ col q`. Proved by cases on the edge and integer parity arithmetic (`omega`). |
| `col2` / `col2_proper` | The same coloring as a map into `Fin 2`, and its properness. |
| `two_coloring_exists` | `∃ c : Int × Int → Fin 2, ∀ p q, Adj p q → c p ≠ c q`. Two colors suffice. |
| `chromatic_not_four` | `¬ (∀ c : Int × Int → Fin 3, ∃ p q, Adj p q ∧ c p = c q)`, i.e. there is a proper 3-coloring, so the chromatic number does not exceed 2 and is not 4. |
| `conjecture_00000001367_false` | Collects: (a) a proper `Fin 2`-coloring exists; (b) the documented Borel ingredient `BorelCountableNote`; (c) `2 < 4 ∧ 2 < 5`. |

## Axiom audit

`Check.lean` runs `#print axioms` on every theorem.  The output contains only
`propext`, `Quot.sound` (and `Classical.choice` for the final collected theorem);
there is no `sorryAx` and no `ofReduceBool`.

## Not formalised: the Borel argument

The formal development covers the combinatorial half only.  The following
mathematical step is **documented here, not formalised in Lean**:

* `Z × Z` is countable.  Equipped with its discrete σ-algebra it is a standard
  Borel space, and in fact *every* subset of `Z × Z` is Borel (a countable space
  is standard Borel and its σ-algebra is the full power set).  Consequently every
  function out of `Z × Z`, in particular the parity coloring `col2`, is Borel
  measurable.  Hence

  χ_Borel(grid) ≤ 2.

  Since the grid has at least one edge, any proper coloring needs at least two
  colors, so χ_Borel(grid) = 2.

Core Lean has no Borel/measurability library, so this is recorded as the
placeholder `BorelCountableNote := True` in `Main.lean` and stated mathematically
in `main.tex`.  This is the only ingredient of the refutation not mechanically
verified.

## Conclusion

Both values asserted by the conjecture are wrong: the classical chromatic number
is **2** (not 4) and the Borel chromatic number is also **2** (not 5).  The
Borel constraint does **not** force an extra color here.
