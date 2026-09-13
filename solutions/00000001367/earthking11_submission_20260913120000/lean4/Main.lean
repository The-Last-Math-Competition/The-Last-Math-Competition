/-
  Refutation of conjecture 00000001367.

  CLAIM (as stated): the Borel chromatic number of the Cayley graph of Z^2 with
  generators {±e1, ±e2} is exactly 5, and the classical chromatic number is 4.

  The conjecture is FALSE, and wrong in both asserted values:

  * The Cayley graph of Z^2 with generators {±e1, ±e2} is the square grid: two
    lattice points are adjacent iff they differ by ±e1 or ±e2.  This graph is
    BIPARTITE, via the parity map (i, j) ↦ (i + j) mod 2, which uses 2 colors
    and flips on every edge.  Hence the classical chromatic number is 2, not 4.

  * Z^2 is countable, so its discrete σ-algebra is all of P(Z^2): every subset
    is Borel.  Thus the parity coloring is Borel measurable and the Borel
    chromatic number is also 2, not 5.  The claim that "the Borel constraint
    forces one extra color" is false here: χ(Borel) = χ = 2.

  The Lean development below is core Lean only (`import Std`, no Mathlib, no
  `sorry`, no `axiom`, no `native_decide`).  It formalises the graph, the
  parity coloring, its properness, the existence of a proper `Fin 2`-coloring,
  and the arithmetic obstructions 2 < 4 and 2 < 5.  The Borel-measurability
  ingredient (countable space ⇒ all sets Borel) is a documented mathematical
  statement, not formalised here; see `lean4/README.md`.
-/

import Std

set_option maxRecDepth 100000

namespace Tlmc1367

/-- Grid adjacency on `Z × Z`: two lattice points are adjacent iff one is a unit
step from the other in one of the four axis directions. -/
def Adj (p q : Int × Int) : Prop :=
  q = (p.1 + 1, p.2) ∨ q = (p.1 - 1, p.2) ∨ q = (p.1, p.2 + 1) ∨ q = (p.1, p.2 - 1)

/-- The parity coloring of the grid: `(i, j) ↦ (i + j) mod 2`, returned as a
natural number (always `0` or `1`). -/
def col (p : Int × Int) : Nat := Int.toNat ((p.1 + p.2) % 2)

/-- The same parity coloring packaged as a map into `Fin 2`. -/
def col2 (p : Int × Int) : Fin 2 :=
  ⟨col p, by
    unfold col
    have h1 : 0 ≤ (p.1 + p.2) % 2 := Int.emod_nonneg _ (by decide)
    have h2 : (p.1 + p.2) % 2 < (2 : Int) := Int.emod_lt_of_pos _ (by decide)
    omega⟩

/-- The parity coloring is proper: adjacent vertices receive different colors.
Each case is a pure integer-parity computation. -/
theorem parity_proper : ∀ p q, Adj p q → col p ≠ col q := by
  intro p q h
  rcases h with h | h | h | h
  · rw [h]; unfold col; omega
  · rw [h]; unfold col; omega
  · rw [h]; unfold col; omega
  · rw [h]; unfold col; omega

/-- The `Fin 2` parity coloring is proper. -/
theorem col2_proper : ∀ p q, Adj p q → col2 p ≠ col2 q := by
  intro p q hpq hEq
  exact parity_proper p q hpq (by simpa [col2] using congrArg Fin.val hEq)

/-- Two colors suffice: there is a proper coloring of the grid by `Fin 2`. -/
theorem two_coloring_exists : ∃ c : Int × Int → Fin 2, ∀ p q, Adj p q → c p ≠ c q :=
  ⟨col2, col2_proper⟩

/-- There is a proper 3-coloring of the grid (obtained by lifting the proper
2-coloring).  Equivalently, it is *not* the case that every `Fin 3`-coloring has
a monochromatic edge; so the chromatic number does not exceed 2, and in
particular is not 4. -/
theorem chromatic_not_four :
    ¬ (∀ c : Int × Int → Fin 3, ∃ p q, Adj p q ∧ c p = c q) := by
  intro h
  let c3 : Int × Int → Fin 3 :=
    fun p => ⟨(col2 p).val, by have hlt := (col2 p).isLt; omega⟩
  obtain ⟨p, q, hpq, hEq⟩ := h c3
  have hval : (col2 p).val = (col2 q).val := by
    have := congrArg Fin.val hEq
    simpa [c3] using this
  exact col2_proper p q hpq (Fin.ext hval)

/-- Documented (non-formalised) mathematical ingredient: `Z × Z` is countable,
so its discrete σ-algebra is the full power set; hence the parity coloring is
Borel measurable.  This `Prop` is a placeholder recording the statement; it is
not a formalisation of Borel measurability. -/
def BorelCountableNote : Prop := True

/-- The conjecture 00000001367 is false, collected:
(a) a proper `Fin 2`-coloring of the grid exists;
(b) the parity coloring is Borel because `Z × Z` is countable (documented, see
    `lean4/README.md`; represented here by `BorelCountableNote`);
(c) `2 < 4` and `2 < 5`, so neither asserted value 4 nor 5 can be the chromatic
    number. -/
theorem conjecture_00000001367_false :
    (∃ c : Int × Int → Fin 2, ∀ p q, Adj p q → c p ≠ c q) ∧
      (2 < 4 ∧ 2 < 5) ∧ BorelCountableNote :=
  ⟨two_coloring_exists, ⟨by omega, trivial⟩⟩

end Tlmc1367
