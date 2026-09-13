/-
  Refutation of conjecture `00000001109`: formal core.

  Conjecture (as filed):

    Definition: the exponents of a Coxeter system (equivalently, the roots of
                its characteristic polynomial).
    Conjecture: the exponent set of a NON-crystallographic Coxeter group
                contains, besides (h, 1), some exponent of multiplicity ≥ 2
                ("universality of multiplicity structure").

  Reading and verdict.

  * For a finite Coxeter group the exponents are the degrees minus one, and the
    Coxeter number `h` is the largest DEGREE, so `h` is not itself an exponent;
    the phrase "(h, 1)" is therefore vacuous under the standard convention

        exponents = degrees − 1,      h = max degree.

  * The complete list of IRREDUCIBLE finite non-crystallographic Coxeter types
    is H₃, H₄, and I₂(m) for m ≥ 5  (I₂(3) = A₂, I₂(4) = B₂, I₂(6) = G₂ and
    I₂(2) = A₁² are crystallographic, or reducible).  Their exponents are

        H₃     : 1, 5, 9                 (degrees 2, 6, 10;    h = 10)
        H₄     : 1, 11, 19, 29           (degrees 2, 12, 20, 30; h = 30)
        I₂(m)  : 1, m − 1                (degrees 2, m;       h = m)

    In every case the exponents are PAIRWISE DISTINCT, so every exponent has
    multiplicity exactly 1 and no exponent has multiplicity ≥ 2.

  * Hence, read UNIVERSALLY over all irreducible finite non-crystallographic
    Coxeter groups — which is what the conjecture's own phrase "universality of
    multiplicity structure" (中文: 重数结构普遍性) indicates — the conclusion is
    FALSE and the conjecture is disproved.

  HONEST SCOPE BOUNDARY (formalised below as `reducible_has_repeated`).

  * Under an EXISTENTIAL reading that also admits REDUCIBLE non-crystallographic
    groups, the conjecture is TRUE, and this file proves the counterexample:
    A₁ × H₃ is non-crystallographic and has exponent multiset 1, 1, 5, 9, so
    the exponent 1 has multiplicity 2.  The refutation therefore depends on the
    universal reading, which the conjecture's wording supports.

  * Adjoining `h` to the exponent list does not change the conclusion: the
    lists 1, 5, 9, 10 and 1, 11, 19, 29, 30 are still all-distinct.

  The classification of finite Coxeter groups and their exponent tables is CITED
  (Humphreys, Bourbaki), NOT reproved here.  This file formalises only the
  finite multiplicity arithmetic on the exponent lists.

  CORE LEAN ONLY (`import Std`); no Mathlib, no `Finset`, no `ZMod`, no `sorry`,
  no `native_decide`.
-/

import Std

set_option maxRecDepth 1000000

namespace Tlmc1109

/-! ## Exponent lists of the irreducible finite non-crystallographic types -/

/-- Exponents of `H₃`: degrees `2, 6, 10` minus one. -/
def expsH3 : List Nat := [1, 5, 9]

/-- Exponents of `H₄`: degrees `2, 12, 20, 30` minus one. -/
def expsH4 : List Nat := [1, 11, 19, 29]

/-- Exponents of `I₂(m)`, `m ≥ 5`: degrees `2, m` minus one. -/
def expsI2 (m : Nat) : List Nat := [1, m - 1]

/-- Exponents of the rank-one crystallographic group `A₁` (degree `2`).  Used
only to build the reducible scope counterexample `A₁ × H₃`. -/
def expsA1 : List Nat := [1]

/-- Coxeter number of `H₃` (the largest degree, `10`). -/
def hH3 : Nat := 10

/-- Coxeter number of `H₄` (the largest degree, `30`). -/
def hH4 : Nat := 30

/-- Coxeter number of `I₂(m)` (the largest degree, `m`). -/
def hI2 (m : Nat) : Nat := m

/-! ## The conjecture's conclusion predicate -/

/-- The conclusion of conjecture `00000001109`: the exponent multiset contains,
besides `(h, 1)`, some exponent of multiplicity `≥ 2`.  Read on the bare
exponent list, this is `HasRepeatedExponent l`. -/
def HasRepeatedExponent (l : List Nat) : Prop :=
  ∃ x, x ∈ l ∧ 2 ≤ l.count x

/-! ## General lemma: distinctness forces multiplicity one -/

/-- If a list has no duplicate entries then every member occurs exactly once.
This is the abstract form of "the exponents are pairwise distinct, hence every
exponent has multiplicity `1`".  Proof by induction on the list. -/
theorem count_eq_one_of_nodup : ∀ (l : List Nat), l.Nodup → ∀ x ∈ l, l.count x = 1 := by
  intro l
  induction l with
  | nil =>
      intro _ x hx
      simp at hx
  | cons a t ih =>
      intro h x hx
      rw [List.nodup_cons] at h
      obtain ⟨ha, ht⟩ := h
      rcases List.mem_cons.mp hx with rfl | hxt
      · simp [List.count_eq_zero_of_not_mem ha]
      · have hax : a ≠ x := by
          intro heq
          exact ha (heq ▸ hxt)
        simp [List.count_cons_of_ne hax, ih ht x hxt]

/-! ## Pairwise distinctness of the exponents -/

/-- The exponents of `H₃` are pairwise distinct. -/
theorem h3_nodup : (expsH3).Nodup := by decide

/-- The exponents of `H₄` are pairwise distinct. -/
theorem h4_nodup : (expsH4).Nodup := by decide

/-- The exponents `1, m − 1` of `I₂(m)` are pairwise distinct whenever
`m − 1 ≠ 1` (true for all `m ≥ 5`).  Plain `omega` cannot see through
truncated subtraction here; `simp` reduces the goal and `Ne.symm` flips the
given hypothesis. -/
theorem i2_nodup (m : Nat) (hm : m - 1 ≠ 1) : (expsI2 m).Nodup := by
  simp [expsI2]
  exact fun h => hm h.symm

/-! ## No repeated exponent: the conjecture's conclusion is false -/

/-- `H₃` has no exponent of multiplicity `≥ 2`. -/
theorem h3_no_repeat : ¬ HasRepeatedExponent expsH3 := by
  unfold HasRepeatedExponent
  decide

/-- `H₄` has no exponent of multiplicity `≥ 2`. -/
theorem h4_no_repeat : ¬ HasRepeatedExponent expsH4 := by
  unfold HasRepeatedExponent
  decide

/-- `I₂(m)` has no exponent of multiplicity `≥ 2` for every `m ≥ 5` (in fact
whenever `m − 1 ≠ 1`).  This is a direct consequence of distinctness, via
`count_eq_one_of_nodup`. -/
theorem i2_no_repeat (m : Nat) (hm : m - 1 ≠ 1) :
    ¬ HasRepeatedExponent (expsI2 m) := by
  rintro ⟨x, hx, h2⟩
  have h1 := count_eq_one_of_nodup (expsI2 m) (i2_nodup m hm) x hx
  omega

/-- Collected refutation of conjecture `00000001109` under the universal
reading over irreducible finite non-crystallographic Coxeter groups: none of
`H₃`, `H₄`, or `I₂(m)` (`m ≥ 5`) has an exponent of multiplicity `≥ 2`.  Hence
it is NOT the case that every non-crystallographic Coxeter group contains,
besides `(h, 1)`, an exponent of multiplicity `≥ 2`. -/
theorem conjecture_00000001109_false :
    ¬ HasRepeatedExponent expsH3 ∧ ¬ HasRepeatedExponent expsH4 ∧
    (∀ m, m - 1 ≠ 1 → ¬ HasRepeatedExponent (expsI2 m)) :=
  ⟨h3_no_repeat, h4_no_repeat, i2_no_repeat⟩

/-! ## The `(h, 1)` reading: `h` is not an exponent -/

/-- `h = 10` is not an exponent of `H₃` (it is the largest degree). -/
theorem h3_h_not_exponent : (expsH3.contains hH3) = false := by decide

/-- `h = 30` is not an exponent of `H₄` (it is the largest degree). -/
theorem h4_h_not_exponent : (expsH4.contains hH4) = false := by decide

/-- Exponents of `H₃` with `h` adjoined, `1, 5, 9, 10`. -/
def expsH3WithH : List Nat := expsH3 ++ [hH3]

/-- Exponents of `H₄` with `h` adjoined, `1, 11, 19, 29, 30`. -/
def expsH4WithH : List Nat := expsH4 ++ [hH4]

/-- Adjoining `h = 10` to the exponents of `H₃` keeps them all-distinct, so
even the generous reading of `(h, 1)` does not create a repeated exponent. -/
theorem h3_with_h_no_repeat : ¬ HasRepeatedExponent expsH3WithH := by
  unfold HasRepeatedExponent expsH3WithH expsH3 hH3
  decide

/-- Adjoining `h = 30` to the exponents of `H₄` keeps them all-distinct. -/
theorem h4_with_h_no_repeat : ¬ HasRepeatedExponent expsH4WithH := by
  unfold HasRepeatedExponent expsH4WithH expsH4 hH4
  decide

/-! ## Honest scope boundary: the reducible group `A₁ × H₃` -/

/-- Exponent multiset of the REDUCIBLE non-crystallographic group `A₁ × H₃`:
exponents add over direct products, giving `1, 1, 5, 9`. -/
def expsA1H3 : List Nat := expsA1 ++ expsH3

/-- HONEST LIMITATION.  Under an EXISTENTIAL reading that admits reducible
groups, conjecture `00000001109` is TRUE: `A₁ × H₃` is non-crystallographic and
its exponent `1` has multiplicity `2`.  This theorem records that boundary
explicitly; it does not contradict `conjecture_00000001109_false`, which is the
UNIVERSAL statement over irreducible types. -/
theorem reducible_has_repeated : HasRepeatedExponent expsA1H3 := by
  unfold HasRepeatedExponent expsA1H3 expsA1 expsH3
  decide

/-- The repeated exponent in `A₁ × H₃` is `1`, with multiplicity exactly `2`. -/
theorem reducible_count_one : expsA1H3.count 1 = 2 := by
  unfold expsA1H3 expsA1 expsH3
  decide

end Tlmc1109
