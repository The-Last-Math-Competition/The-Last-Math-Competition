/-
Copyright (c) 2026. All rights reserved.
Master formalization entry point for Conjecture 00000007603:
"The geometric product as the norm-type product structure. Conjecture: The conversion
constant is the norm law of the product, the norm always equaling the bound of the
quadratic-form product; the spectrum is explicit and is the isometry group; and the
tight example of equality is vector pairs."

Verdict: FALSE in general.
- Positive domain (non-vacuity): Grade-1 Euclidean vector pairs & versors in `Cl_{n,0}`
  for all `n ∈ ℕ`, and all multivectors in Hurwitz Clifford algebras `Cl_{0,n}` (`n ≤ 2`).
- Complete refutations:
  1. Fails on multivectors in `Cl_{n,0}` for ALL `n ≥ 1` (`1 ± e₁`), in `Cl_{0,n}` for ALL `n ≥ 3`
     (`1 ± e₁e₂e₃`), and simultaneously across `‖·‖₂²`, `N_rev`, `N_conj` on even multivectors in
     `Cl_{n,0}` for ALL `n ≥ 4` (`1 ± e₁e₂e₃e₄`), both by exceeding the `C = 1` bound (`8 > 4`)
     and by zero-divisor collapse (`0 < 4`).
  2. Fails even on grade-1 vector pairs in indefinite `Cl_{1,1}` (`u = e₁ + e₂, v = e₁ - e₂`).
  3. Unit-norm / Pin groups never equal `O(V, Q)` (universal `{±1}` double-cover kernel,
     cardinality/infinity mismatch already in `Cl_{0,1}`, and non-Pin algebraic units leaving `V`
     in `Cl_{3,0}`).
-/
import CliffordNormConjecture.Algebra
import CliffordNormConjecture.Positive
import CliffordNormConjecture.Counterexamples

namespace CliffordNormConjecture

open Cl

/-- Master Positive Non-Vacuity Theorem (valid over any `OrderedCommRing R`, including ℤ, ℚ, ℝ):
    1. Grade-1 Euclidean vector pairs satisfy `‖u v‖₂² = Q(u) Q(v) = ‖u‖₂² ‖v‖₂²` for all `n ∈ ℕ`.
    2. Euclidean versors satisfy `‖W Y‖₂² = ‖W‖₂² ‖Y‖₂²` for all `n ∈ ℕ`.
    3. Hurwitz low-dimensional Clifford algebras `Cl_{0,0}`, `Cl_{0,1}`, `Cl_{0,2}` satisfy
       `‖X Y‖₂² = ‖X‖₂² ‖Y‖₂²` for all multivectors `X, Y`.
    4. Sharp conversion-constant bound `‖X Y‖₂² ≤ 2 ‖X‖₂² ‖Y‖₂²` holds for all multivectors in
       `Cl_{1,0}`, `Cl_{1,1}`, `Cl_{0,3}`, and `Cl_{1,2}`. -/
theorem conjecture_00000007603_positive_domain (R : Type) [OrderedCommRing R] :
    (∀ (n : Nat) (u v : Vec R (eucSig R n)),
      l2NormSq (mul (ofVec u) (ofVec v)) = quadForm u * quadForm v ∧
      l2NormSq (mul (ofVec u) (ofVec v)) = l2NormSq (ofVec u) * l2NormSq (ofVec v)) ∧
    (∀ (n : Nat) (vs : List (Vec R (eucSig R n))) (y : Cl R (eucSig R n)),
      l2NormSq (mul (versor vs) y) = l2NormSq (versor vs) * l2NormSq y) ∧
    (∀ x y : Cl R (spinSig R 0), l2NormSq (mul x y) = l2NormSq x * l2NormSq y) ∧
    (∀ x y : Cl R (spinSig R 1), l2NormSq (mul x y) = l2NormSq x * l2NormSq y) ∧
    (∀ x y : Cl R (spinSig R 2), l2NormSq (mul x y) = l2NormSq x * l2NormSq y) ∧
    (∀ x y : Cl R (eucSig R 1), l2NormSq (mul x y) ≤ two R * (l2NormSq x * l2NormSq y)) ∧
    (∀ x y : Cl R (spinSig R 3), l2NormSq (mul x y) ≤ two R * (l2NormSq x * l2NormSq y)) :=
  ⟨euc_vec_pair_l2NormSq,
   euc_versor_l2NormSq_mul,
   hurwitz_cl00_l2NormSq_mul,
   hurwitz_cl01_l2NormSq_mul,
   hurwitz_cl02_l2NormSq_mul,
   sharp_upper_cl10,
   sharp_upper_cl03⟩

/-- Master Refutation Theorem for Conjecture 00000007603:
    Simultaneously refutes the universal norm-equality claim, the `C = 1` conversion-bound claim,
    the vector-pair tightness claim, and the unit-spectrum = isometry-group claim across all
    standard Clifford norm conventions (`‖·‖₂²`, `N_rev`, `N_conj`). -/
theorem conjecture_00000007603_refuted :
    -- (A) Euclidean `Cl_{n,0}` fails both `‖X Y‖₂² = ‖X‖₂² ‖Y‖₂²` and `‖X Y‖₂² ≤ ‖X‖₂² ‖Y‖₂²` for ALL `n ≥ 1`:
    (∀ (R : Type) [OrderedCommRing R] (m : Nat),
      ¬ (∀ x y : Cl R (eucSig R (m + 1)), l2NormSq (mul x y) ≤ l2NormSq x * l2NormSq y) ∧
      ∃ x y : Cl R (eucSig R (m + 1)),
        (0 : R) < l2NormSq x ∧ (0 : R) < l2NormSq y ∧ mul x y = zero) ∧
    -- (B) Spin-Euclidean `Cl_{0,n}` fails both equality and `C = 1` bound for ALL `n ≥ 3`:
    (∀ (R : Type) [OrderedCommRing R] (m : Nat),
      ¬ (∀ x y : Cl R (spinSig R (m + 3)), l2NormSq (mul x y) ≤ l2NormSq x * l2NormSq y) ∧
      ∃ x y : Cl R (spinSig R (m + 3)),
        (0 : R) < l2NormSq x ∧ (0 : R) < l2NormSq y ∧ mul x y = zero) ∧
    -- (C) Even subalgebra `Cl_{n,0}^+` fails ALL THREE scalar norms (`‖·‖₂²`, `N_rev`, `N_conj`) for ALL `n ≥ 4`:
    (∀ (R : Type) [OrderedCommRing R] (m : Nat),
      ∃ xPlus xMinus : Cl R (eucSig R (m + 4)),
        involute xPlus = xPlus ∧ involute xMinus = xMinus ∧
        l2NormSq xPlus = two R ∧ revNorm xPlus = two R ∧ conjNorm xPlus = two R ∧
        l2NormSq (mul xPlus xPlus) = eight R ∧
        revNorm (mul xPlus xPlus) = eight R ∧
        conjNorm (mul xPlus xPlus) = eight R ∧
        mul xPlus xMinus = zero) ∧
    -- (D) Indefinite `Cl_{1,1}` fails even on grade-1 vector pairs:
    (∀ (R : Type) [OrderedCommRing R],
      ∃ u v : Vec R [(1 : R), -(1 : R)],
        quadForm u = 0 ∧ quadForm v = 0 ∧ mul (ofVec u) (ofVec v) ≠ zero ∧
        l2NormSq (ofVec u) * l2NormSq (ofVec v) < l2NormSq (mul (ofVec u) (ofVec v))) ∧
    -- (E) Double-cover kernel `{±1}`, `Cl_{0,1}` unit-group vs `O(1)` mismatch, and `Cl_{3,0}` non-Pin unit:
    (∀ (R : Type) [OrderedCommRing R] (sig : List R),
      ∃ u1 u2 : Cl R sig, u1 ≠ u2 ∧ mul (rev u1) u1 = one ∧ mul (rev u2) u2 = one ∧
        ∀ x : Cl R sig, twistedAdjoint u1 x u1 = twistedAdjoint u2 x u2) ∧
    (∃ x : Cl Int (eucSig Int 3),
      mul (rev x) x = smul 25 one ∧ l2NormSq x = 25 ∧
      ¬ isGradeOne (mul (mul (involute x) (ofVec e1Vec30)) (rev x))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro R _ m
    rcases refutation_euc_all_pos_dim (R := R) m with
      ⟨xp, xm, hxp, _, hxm, _, _, _, hlt, hzd, _⟩
    refine ⟨?_, xp, xm, ?_, ?_, hzd⟩
    · intro hle
      have hc := hle xp xp
      exact ((OrderedCommRing.lt_iff_le_not_le _ _).1 hlt).2 hc
    · rw [hxp]; exact zero_lt_two
    · rw [hxm]; exact zero_lt_two
  · intro R _ m
    rcases refutation_spin_all_ge_three (R := R) m with
      ⟨xp, xm, hxp, _, hxm, _, _, _, hlt, hzd, _⟩
    refine ⟨?_, xp, xm, ?_, ?_, hzd⟩
    · intro hle
      have hc := hle xp xp
      exact ((OrderedCommRing.lt_iff_le_not_le _ _).1 hlt).2 hc
    · rw [hxp]; exact zero_lt_two
    · rw [hxm]; exact zero_lt_two
  · intro R _ m
    rcases refutation_euc_even_triple_norm_ge_four (R := R) m with
      ⟨xp, xm, hiP, hiM, hlP, hrP, hcP, _, _, _, hlSq, hrSq, hcSq, hzd⟩
    exact ⟨xp, xm, hiP, hiM, hlP, hrP, hcP, hlSq, hrSq, hcSq, hzd⟩
  · intro R _
    rcases refutation_indefinite_vector_pairs (R := R) with
      ⟨u, v, hqu, hqv, hne, hlu, hlv, hluv, _, _⟩
    refine ⟨u, v, hqu, hqv, hne, ?_⟩
    rw [hlu, hlv, hluv]
    exact four_lt_eight
  · intro R _ sig
    rcases refutation_double_cover_kernel (R := R) sig with
      ⟨hne, hr1, hr2, _, _, _, _, hadj⟩
    refine ⟨one, neg one, hne, hr1, hr2, fun x => ?_⟩
    rw [(hadj x).1, (hadj x).2]
  · rcases refutation_cl30_algebraic_unit_not_pin with ⟨hr, hl, _, _, _, hng⟩
    exact ⟨xUnit30, hr, hl, hng⟩

/-- Concrete non-vacuous specialization over `Int` (`OrderedCommRing Int`). -/
theorem conjecture_00000007603_int_nonvacuous :
    (∀ (n : Nat) (u v : Vec Int (eucSig Int n)),
      l2NormSq (mul (ofVec u) (ofVec v)) = quadForm u * quadForm v) ∧
    ¬ (∀ x y : Cl Int (eucSig Int 1), l2NormSq (mul x y) ≤ l2NormSq x * l2NormSq y) ∧
    ¬ (∀ x y : Cl Int (spinSig Int 3), l2NormSq (mul x y) ≤ l2NormSq x * l2NormSq y) := by
  refine ⟨fun n u v => (euc_vec_pair_l2NormSq n u v).1,
          (conjecture_00000007603_refuted.1 Int 0).1,
          (conjecture_00000007603_refuted.2.1 Int 0).1⟩

end CliffordNormConjecture
