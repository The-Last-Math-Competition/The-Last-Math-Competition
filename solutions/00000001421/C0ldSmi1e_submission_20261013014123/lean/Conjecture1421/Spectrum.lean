import Conjecture1421.Basic
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.Algebra.Polynomial.Roots

noncomputable section
open scoped BigOperators
open Polynomial
namespace Conjecture1421

abbrev FirstChar := AddChar (ZMod 2) ℂ
abbrev SecondChar (n : ℕ) := AddChar (Second n) ℂ
abbrev Characters (n : ℕ) := AddChar (State n) ℂ

def productChar (n : ℕ) (a : FirstChar) (b : SecondChar n) : Characters n where
  toFun x := a x.1 * b x.2
  map_zero_eq_one' := by simp
  map_add_eq_mul' x y := by simp only [Prod.fst_add, Prod.snd_add, AddChar.map_add_eq_mul]; ring

def firstRestriction (n : ℕ) (ψ : Characters n) : FirstChar where
  toFun a := ψ (a, 0)
  map_zero_eq_one' := ψ.map_zero_eq_one
  map_add_eq_mul' a b := by simpa using ψ.map_add_eq_mul (a, 0) (b, 0)

def secondRestriction (n : ℕ) (ψ : Characters n) : SecondChar n where
  toFun b := ψ (0, b)
  map_zero_eq_one' := ψ.map_zero_eq_one
  map_add_eq_mul' a b := by simpa using ψ.map_add_eq_mul (0, a) (0, b)

def characterEquiv (n : ℕ) : FirstChar × SecondChar n ≃ Characters n where
  toFun p := productChar n p.1 p.2
  invFun ψ := (firstRestriction n ψ, secondRestriction n ψ)
  left_inv p := by
    rcases p with ⟨a,b⟩
    apply Prod.ext <;> apply AddChar.ext <;> intro x <;>
      simp [firstRestriction, secondRestriction, productChar]
  right_inv ψ := by
    apply AddChar.ext
    rintro ⟨a,b⟩
    change ψ (a, 0) * ψ (0, b) = ψ (a, b)
    simpa using (ψ.map_add_eq_mul (a, 0) (0, b)).symm

@[simp] lemma productChar_apply (n : ℕ) (a : FirstChar) (b : SecondChar n) (x : State n) :
    productChar n a b x = a x.1 * b x.2 := rfl

lemma sum_zmod_two {R : Type*} [AddCommMonoid R] (f : ZMod 2 → R) :
    ∑ a, f a = f 0 + f 1 := by
  have h : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by
    ext a
    fin_cases a <;> decide
  rw [h]
  simp

lemma firstChar_one (a : FirstChar) : a 1 = if a = 0 then 1 else -1 := by
  classical
  have h := a.sum_eq_ite
  rw [sum_zmod_two] at h
  simp only [AddChar.map_zero_eq_one, ZMod.card, Nat.cast_ofNat] at h
  split_ifs with ha
  · simp [ha]
  · rw [if_neg ha] at h
    linear_combination h

def complexTransition (n : ℕ) : Matrix (State n) (State n) ℂ :=
  (transition n).map Complex.ofRealHom

def fourierEigenvalue (n : ℕ) (ψ : Characters n) : ℂ :=
  ∑ g, (jumpLaw n g : ℂ) * ψ g

lemma character_action (n : ℕ) (ψ : Characters n) :
    (complexTransition n).mulVec ψ = fourierEigenvalue n ψ • (ψ : State n → ℂ) := by
  classical
  funext x
  change (∑ y, (jumpLaw n (y - x) : ℂ) * ψ y) = fourierEigenvalue n ψ * ψ x
  rw [← Equiv.sum_comp (Equiv.addRight x)]
  change (∑ g, (jumpLaw n ((g + x) - x) : ℂ) * ψ (g + x)) = _
  simp only [add_sub_cancel_right, AddChar.map_add_eq_mul]
  simp [fourierEigenvalue, Finset.sum_mul, mul_assoc]

lemma complex_jumpLaw (n : ℕ) (g : State n) :
    (jumpLaw n g : ℂ) =
      (if g.1 = 0 ∧ g.2 = 0 then (s n : ℂ) else 0) +
      (if g.1 = 0 then 1 / (2 * (size n : ℂ)) else 0) +
      (if g.2 = 0 then 1 / (2 * (size n : ℂ)) else 0) := by
  have hn : (size n : ℂ) ≠ 0 := by exact_mod_cast size_ne_zero n
  unfold jumpLaw
  by_cases h1 : g.1 = 0 <;> by_cases h2 : g.2 = 0 <;>
    simp [h1, h2, s, Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_mul]
  field_simp
  ring

lemma fourierEigenvalue_product (n : ℕ) (a : FirstChar) (b : SecondChar n) :
    fourierEigenvalue n (productChar n a b) =
      if b = 0 then (if a = 0 then 1 else (q n : ℂ))
      else (if a = 0 then (r : ℂ) else (s n : ℂ)) := by
  classical
  have hn : (size n : ℂ) ≠ 0 := by exact_mod_cast size_ne_zero n
  unfold fourierEigenvalue
  simp_rw [complex_jumpLaw, productChar_apply, add_mul]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp_rw [Fintype.sum_prod_type, ite_mul, zero_mul, ite_and]
  simp_rw [Finset.sum_ite_irrel, Finset.sum_const_zero]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, AddChar.map_zero_eq_one,
    one_mul, mul_one]
  simp only [← Finset.mul_sum, ← Finset.sum_mul]
  simp only [AddChar.sum_eq_ite, ZMod.card]
  split_ifs <;> simp_all [q, r, s, size] <;> field_simp <;> ring

lemma character_toMatrix (n : ℕ) :
    LinearMap.toMatrix (AddChar.complexBasis (State n)) (AddChar.complexBasis (State n))
      (complexTransition n).mulVecLin = Matrix.diagonal (fourierEigenvalue n) := by
  classical
  ext i j
  rw [LinearMap.toMatrix_apply]
  simp only [AddChar.complexBasis_apply, Matrix.mulVecLin_apply, character_action]
  have hr : (AddChar.complexBasis (State n)).repr (j : State n → ℂ) =
      Finsupp.single j 1 := by
    simpa only [AddChar.complexBasis_apply] using (AddChar.complexBasis (State n)).repr_self j
  simp [hr, Matrix.diagonal, Finsupp.single_apply, eq_comm]
  split_ifs with h
  · subst j; rfl
  · simp

lemma charpoly_eq_product (n : ℕ) :
    (complexTransition n).charpoly = ∏ ψ : Characters n, (X - C (fourierEigenvalue n ψ)) := by
  classical
  have h := (complexTransition n).mulVecLin.charpoly_toMatrix (Pi.basisFun ℂ (State n))
  have h' := (complexTransition n).mulVecLin.charpoly_toMatrix (AddChar.complexBasis (State n))
  rw [character_toMatrix] at h'
  have hm : LinearMap.toMatrix (Pi.basisFun ℂ (State n)) (Pi.basisFun ℂ (State n))
      (complexTransition n).mulVecLin = complexTransition n := by
    ext i j
    simp [LinearMap.toMatrix_apply, Pi.basisFun_apply, Matrix.mulVecLin_apply]
  rw [hm] at h
  rw [h, ← h']
  simp [Matrix.charpoly, Matrix.charmatrix, Matrix.diagonal_sub, Matrix.det_diagonal]

lemma product_ite_zero {A M : Type*} [Fintype A] [DecidableEq A] [Zero A]
    [CommMonoid M] (x y : M) :
    (∏ a : A, if a = 0 then x else y) = x * y ^ (Fintype.card A - 1) := by
  rw [← Finset.mul_prod_erase (Finset.univ : Finset A) _ (Finset.mem_univ 0)]
  simp only [ite_true]
  congr 1
  calc
    _ = ∏ _a ∈ (Finset.univ : Finset A).erase 0, y := by
      apply Finset.prod_congr rfl
      intro a ha
      simp [Finset.ne_of_mem_erase ha]
    _ = _ := by simp [Finset.card_erase_of_mem]

lemma complexTransition_charpoly (n : ℕ) :
    (complexTransition n).charpoly =
      (X - C (1 : ℂ)) * (X - C (q n : ℂ)) *
        (X - C (r : ℂ)) ^ (n + 3) * (X - C (s n : ℂ)) ^ (n + 3) := by
  classical
  rw [charpoly_eq_product, ← Equiv.prod_comp (characterEquiv n), Fintype.prod_prod_type]
  change (∏ a : FirstChar, ∏ b : SecondChar n,
    (X - C (fourierEigenvalue n (productChar n a b)))) = _
  have hf (a : FirstChar) (b : SecondChar n) :
      X - C (fourierEigenvalue n (productChar n a b)) =
      if b = 0 then (if a = 0 then X - C (1 : ℂ) else X - C (q n : ℂ))
      else (if a = 0 then X - C (r : ℂ) else X - C (s n : ℂ)) := by
    rw [fourierEigenvalue_product]
    split_ifs <;> rfl
  simp_rw [hf, product_ite_zero]
  have hf' (a : FirstChar) :
      (if a = 0 then X - C (1 : ℂ) else X - C (q n : ℂ)) *
      (if a = 0 then X - C (r : ℂ) else X - C (s n : ℂ)) ^
        (Fintype.card (SecondChar n) - 1) =
      if a = 0 then (X - C (1 : ℂ)) * (X - C (r : ℂ)) ^ (n + 3)
      else (X - C (q n : ℂ)) * (X - C (s n : ℂ)) ^ (n + 3) := by
    simp only [AddChar.card_eq, ZMod.card]
    split_ifs <;> rfl
  simp_rw [hf', product_ite_zero]
  simp only [AddChar.card_eq, ZMod.card]
  norm_num
  ring

lemma eigenvalues_ordered (n : ℕ) : 0 < s n ∧ s n < r ∧ r < q n ∧ q n < 1 := by
  have hp : 0 < 1 / size n := one_div_pos.mpr (size_pos n)
  have hl : 1 / size n < (1 / 2 : ℝ) := by
    apply (div_lt_iff₀ (size_pos n)).2
    have := size_ge_four n
    linarith
  dsimp [s, r, q]
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

@[simp] lemma productChar_zero (n : ℕ) : productChar n 0 0 = 0 := by
  ext x
  simp

lemma productChar_eq_zero_iff (n : ℕ) (a : FirstChar) (b : SecondChar n) :
    productChar n a b = 0 ↔ a = 0 ∧ b = 0 := by
  change characterEquiv n (a,b) = 0 ↔ _
  rw [← productChar_zero n]
  change characterEquiv n (a,b) = characterEquiv n (0,0) ↔ _
  rw [Equiv.apply_eq_iff_eq]
  exact Prod.mk_inj

lemma fourierEigenvalue_nontrivial (n : ℕ) (ψ : Characters n) (hψ : ψ ≠ 0) :
    fourierEigenvalue n ψ = (q n : ℂ) ∨ fourierEigenvalue n ψ = (r : ℂ) ∨
      fourierEigenvalue n ψ = (s n : ℂ) := by
  classical
  obtain ⟨⟨a,b⟩, rfl⟩ := (characterEquiv n).surjective ψ
  change productChar n a b ≠ 0 at hψ
  change fourierEigenvalue n (productChar n a b) = (q n : ℂ) ∨
    fourierEigenvalue n (productChar n a b) = (r : ℂ) ∨
    fourierEigenvalue n (productChar n a b) = (s n : ℂ)
  rw [fourierEigenvalue_product]
  by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> simp_all [productChar_eq_zero_iff]

lemma exists_character_q (n : ℕ) : ∃ ψ : Characters n,
    ψ ≠ 0 ∧ fourierEigenvalue n ψ = (q n : ℂ) := by
  classical
  obtain ⟨a, ha⟩ := Fintype.exists_ne_of_one_lt_card
    (α := FirstChar) (by simp [AddChar.card_eq]) 0
  exact ⟨productChar n a 0, by simpa [productChar_eq_zero_iff],
    by simp [fourierEigenvalue_product, ha]⟩

lemma exists_character_s (n : ℕ) : ∃ ψ : Characters n,
    ψ ≠ 0 ∧ fourierEigenvalue n ψ = (s n : ℂ) := by
  classical
  obtain ⟨a, ha⟩ := Fintype.exists_ne_of_one_lt_card
    (α := FirstChar) (by simp [AddChar.card_eq]) 0
  obtain ⟨b, hb⟩ := Fintype.exists_ne_of_one_lt_card
    (α := SecondChar n) (by simp [AddChar.card_eq]) 0
  exact ⟨productChar n a b, by simp [productChar_eq_zero_iff, ha],
    by simp [fourierEigenvalue_product, ha, hb]⟩

def nontrivialCharacters (n : ℕ) : Finset (Characters n) := by
  classical
  exact Finset.univ.erase 0

lemma nontrivialCharacters_nonempty (n : ℕ) : (nontrivialCharacters n).Nonempty := by
  classical
  obtain ⟨ψ,hψ,_⟩ := exists_character_q n
  exact ⟨ψ, by simp [nontrivialCharacters, hψ]⟩

def maxNontrivialEigenvalue (n : ℕ) : ℝ :=
  (nontrivialCharacters n).sup' (nontrivialCharacters_nonempty n)
    (fun ψ => (fourierEigenvalue n ψ).re)

def minTransitionEigenvalue (n : ℕ) : ℝ :=
  (nontrivialCharacters n).inf' (nontrivialCharacters_nonempty n)
    (fun ψ => (fourierEigenvalue n ψ).re)

def spectralGap (n : ℕ) : ℝ := 1 - maxNontrivialEigenvalue n

lemma maxNontrivialEigenvalue_eq_q (n : ℕ) : maxNontrivialEigenvalue n = q n := by
  classical
  obtain ⟨hs, hsr, hrq, hq⟩ := eigenvalues_ordered n
  apply le_antisymm
  · apply Finset.sup'_le
    intro ψ hψ
    have hn : ψ ≠ 0 := by simpa [nontrivialCharacters] using hψ
    rcases fourierEigenvalue_nontrivial n ψ hn with h | h | h <;> rw [h] <;>
      simp only [Complex.ofReal_re] <;> linarith
  · obtain ⟨ψ,hψ,he⟩ := exists_character_q n
    have hm : ψ ∈ nontrivialCharacters n := by simp [nontrivialCharacters, hψ]
    have hh := Finset.le_sup' (s := nontrivialCharacters n)
      (f := fun ψ => (fourierEigenvalue n ψ).re) hm
    simpa [he, maxNontrivialEigenvalue] using hh

lemma minTransitionEigenvalue_eq_s (n : ℕ) : minTransitionEigenvalue n = s n := by
  classical
  obtain ⟨hs, hsr, hrq, hq⟩ := eigenvalues_ordered n
  apply le_antisymm
  · obtain ⟨ψ,hψ,he⟩ := exists_character_s n
    have hm : ψ ∈ nontrivialCharacters n := by simp [nontrivialCharacters, hψ]
    have hh := Finset.inf'_le (s := nontrivialCharacters n)
      (f := fun ψ => (fourierEigenvalue n ψ).re) hm
    simpa [he, minTransitionEigenvalue] using hh
  · apply Finset.le_inf'
    intro ψ hψ
    have hn : ψ ≠ 0 := by simpa [nontrivialCharacters] using hψ
    rcases fourierEigenvalue_nontrivial n ψ hn with h | h | h <;> rw [h] <;>
      simp only [Complex.ofReal_re] <;> linarith

lemma spectralGap_eq (n : ℕ) : spectralGap n = 1 / size n := by
  rw [spectralGap, maxNontrivialEigenvalue_eq_q, q]
  ring

lemma complex_eigenvalues_distinct (n : ℕ) :
    (s n : ℂ) ≠ 1 ∧ (s n : ℂ) ≠ (q n : ℂ) ∧ (s n : ℂ) ≠ (r : ℂ) ∧
      (q n : ℂ) ≠ 1 ∧ (q n : ℂ) ≠ (r : ℂ) := by
  obtain ⟨hs, hsr, hrq, hq⟩ := eigenvalues_ordered n
  have hs1 : s n ≠ 1 := ne_of_lt (lt_trans hsr (lt_trans hrq hq))
  have hsq : s n ≠ q n := ne_of_lt (lt_trans hsr hrq)
  have hsr' : s n ≠ r := ne_of_lt hsr
  have hq1 : q n ≠ 1 := ne_of_lt hq
  have hqr : q n ≠ r := ne_of_gt hrq
  exact ⟨by exact_mod_cast hs1, by exact_mod_cast hsq, by exact_mod_cast hsr',
    by exact_mod_cast hq1, by exact_mod_cast hqr⟩

lemma charpoly_rootMultiplicity_s (n : ℕ) :
    ((complexTransition n).charpoly).rootMultiplicity (s n : ℂ) = n + 3 := by
  classical
  rw [complexTransition_charpoly]
  have hn : (X - C (1 : ℂ)) * (X - C (q n : ℂ)) *
      (X - C (r : ℂ)) ^ (n + 3) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _))
      (pow_ne_zero _ (X_sub_C_ne_zero _))
  rw [rootMultiplicity_mul_X_sub_C_pow hn]
  have hd := complex_eigenvalues_distinct n
  have hr : ¬ IsRoot ((X - C (1 : ℂ)) * (X - C (q n : ℂ)) *
      (X - C (r : ℂ)) ^ (n + 3)) (s n : ℂ) := by
    simp [IsRoot, sub_eq_zero, hd.1, hd.2.1, hd.2.2.1]
  rw [rootMultiplicity_eq_zero hr, zero_add]

def minTransitionMultiplicity (n : ℕ) : ℕ :=
  ((complexTransition n).charpoly).rootMultiplicity (minTransitionEigenvalue n : ℂ)

lemma minTransitionMultiplicity_eq (n : ℕ) : minTransitionMultiplicity n = n + 3 := by
  rw [minTransitionMultiplicity, minTransitionEigenvalue_eq_s, charpoly_rootMultiplicity_s]

lemma charpoly_rootMultiplicity_q (n : ℕ) :
    ((complexTransition n).charpoly).rootMultiplicity (q n : ℂ) = 1 := by
  classical
  rw [complexTransition_charpoly]
  have he : (X - C (1 : ℂ)) * (X - C (q n : ℂ)) *
      (X - C (r : ℂ)) ^ (n + 3) * (X - C (s n : ℂ)) ^ (n + 3) =
      ((X - C (1 : ℂ)) * (X - C (r : ℂ)) ^ (n + 3) *
      (X - C (s n : ℂ)) ^ (n + 3)) * (X - C (q n : ℂ)) ^ 1 := by ring
  rw [he]
  have hn : (X - C (1 : ℂ)) * (X - C (r : ℂ)) ^ (n + 3) *
      (X - C (s n : ℂ)) ^ (n + 3) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (X_sub_C_ne_zero _) (pow_ne_zero _ (X_sub_C_ne_zero _)))
      (pow_ne_zero _ (X_sub_C_ne_zero _))
  rw [rootMultiplicity_mul_X_sub_C_pow hn]
  have hd := complex_eigenvalues_distinct n
  have hr : ¬ IsRoot ((X - C (1 : ℂ)) * (X - C (r : ℂ)) ^ (n + 3) *
      (X - C (s n : ℂ)) ^ (n + 3)) (q n : ℂ) := by
    simp [IsRoot, sub_eq_zero, hd.2.2.2.1, hd.2.2.2.2, Ne.symm hd.2.1]
  rw [rootMultiplicity_eq_zero hr, zero_add]

lemma minTransitionRatio_eq (n : ℕ) :
    (minTransitionMultiplicity n : ℝ) / spectralGap n = size n * (size n - 1) := by
  rw [minTransitionMultiplicity_eq, spectralGap_eq]
  rw [div_eq_mul_inv, one_div, inv_inv]
  simp only [size, Nat.cast_add, Nat.cast_ofNat]
  ring

lemma spectralGap_pos (n : ℕ) : 0 < spectralGap n := by
  rw [spectralGap_eq]
  exact one_div_pos.mpr (size_pos n)

lemma fourierEigenvalue_eq_one_iff (n : ℕ) (ψ : Characters n) :
    fourierEigenvalue n ψ = 1 ↔ ψ = 0 := by
  classical
  constructor
  · intro h
    by_contra hn
    obtain ⟨hs, hsr, hrq, hq⟩ := eigenvalues_ordered n
    have hr1 : r ≠ 1 := ne_of_lt (lt_trans hrq hq)
    have hd := complex_eigenvalues_distinct n
    rcases fourierEigenvalue_nontrivial n ψ hn with he | he | he
    · exact hd.2.2.2.1 (he.symm.trans h)
    · have : (r : ℂ) ≠ 1 := by exact_mod_cast hr1
      exact this (he.symm.trans h)
    · exact hd.1 (he.symm.trans h)
  · rintro rfl
    rw [← productChar_zero n, fourierEigenvalue_product]
    simp

def complexComplement (n : ℕ) : Matrix (State n) (State n) ℂ := 1 - complexTransition n

lemma complement_character_action (n : ℕ) (ψ : Characters n) :
    (complexComplement n).mulVec ψ = (1 - fourierEigenvalue n ψ) • (ψ : State n → ℂ) := by
  rw [complexComplement, Matrix.sub_mulVec, Matrix.one_mulVec, character_action, sub_smul, one_smul]

lemma complement_character_toMatrix (n : ℕ) :
    LinearMap.toMatrix (AddChar.complexBasis (State n)) (AddChar.complexBasis (State n))
      (complexComplement n).mulVecLin = Matrix.diagonal (fun ψ => 1 - fourierEigenvalue n ψ) := by
  classical
  ext i j
  rw [LinearMap.toMatrix_apply]
  simp only [AddChar.complexBasis_apply, Matrix.mulVecLin_apply, complement_character_action]
  have hr : (AddChar.complexBasis (State n)).repr (j : State n → ℂ) =
      Finsupp.single j 1 := by
    simpa only [AddChar.complexBasis_apply] using (AddChar.complexBasis (State n)).repr_self j
  simp [hr, Matrix.diagonal, Finsupp.single_apply, eq_comm]
  split_ifs with h
  · subst j; rfl
  · simp

lemma complement_charpoly_eq_product (n : ℕ) :
    (complexComplement n).charpoly =
      ∏ ψ : Characters n, (X - C (1 - fourierEigenvalue n ψ)) := by
  classical
  have h := (complexComplement n).mulVecLin.charpoly_toMatrix (Pi.basisFun ℂ (State n))
  have h' := (complexComplement n).mulVecLin.charpoly_toMatrix (AddChar.complexBasis (State n))
  rw [complement_character_toMatrix] at h'
  have hm : LinearMap.toMatrix (Pi.basisFun ℂ (State n)) (Pi.basisFun ℂ (State n))
      (complexComplement n).mulVecLin = complexComplement n := by
    ext i j
    simp [LinearMap.toMatrix_apply, Pi.basisFun_apply, Matrix.mulVecLin_apply]
  rw [hm] at h
  rw [h, ← h']
  simp [Matrix.charpoly, Matrix.charmatrix, Matrix.diagonal_sub, Matrix.det_diagonal]

lemma complexComplement_charpoly (n : ℕ) :
    (complexComplement n).charpoly =
      (X - C (0 : ℂ)) * (X - C (1 - (q n : ℂ))) *
        (X - C (1 - (r : ℂ))) ^ (n + 3) *
        (X - C (1 - (s n : ℂ))) ^ (n + 3) := by
  classical
  rw [complement_charpoly_eq_product, ← Equiv.prod_comp (characterEquiv n), Fintype.prod_prod_type]
  change (∏ a : FirstChar, ∏ b : SecondChar n,
    (X - C (1 - fourierEigenvalue n (productChar n a b)))) = _
  have hf (a : FirstChar) (b : SecondChar n) :
      X - C (1 - fourierEigenvalue n (productChar n a b)) =
      if b = 0 then (if a = 0 then X - C (0 : ℂ) else X - C (1 - (q n : ℂ)))
      else (if a = 0 then X - C (1 - (r : ℂ)) else X - C (1 - (s n : ℂ))) := by
    rw [fourierEigenvalue_product]
    split_ifs <;> simp
  simp_rw [hf, product_ite_zero]
  have hf' (a : FirstChar) :
      (if a = 0 then X - C (0 : ℂ) else X - C (1 - (q n : ℂ))) *
      (if a = 0 then X - C (1 - (r : ℂ)) else X - C (1 - (s n : ℂ))) ^
        (Fintype.card (SecondChar n) - 1) =
      if a = 0 then (X - C (0 : ℂ)) * (X - C (1 - (r : ℂ))) ^ (n + 3)
      else (X - C (1 - (q n : ℂ))) * (X - C (1 - (s n : ℂ))) ^ (n + 3) := by
    simp only [AddChar.card_eq, ZMod.card]
    split_ifs <;> rfl
  simp_rw [hf', product_ite_zero]
  simp only [AddChar.card_eq, ZMod.card]
  norm_num
  ring

/-- The genuine algebraic multiplicity at the smallest positive eigenvalue of `I-P`. -/
def gapModeMultiplicity (n : ℕ) : ℕ :=
  ((complexComplement n).charpoly).rootMultiplicity (spectralGap n : ℂ)

lemma gapModeMultiplicity_eq_one (n : ℕ) : gapModeMultiplicity n = 1 := by
  classical
  have hg : (spectralGap n : ℂ) = 1 - (q n : ℂ) := by
    rw [spectralGap, maxNontrivialEigenvalue_eq_q, Complex.ofReal_sub, Complex.ofReal_one]
  rw [gapModeMultiplicity, hg, complexComplement_charpoly]
  have he : (X - C (0 : ℂ)) * (X - C (1 - (q n : ℂ))) *
      (X - C (1 - (r : ℂ))) ^ (n + 3) * (X - C (1 - (s n : ℂ))) ^ (n + 3) =
      ((X - C (0 : ℂ)) * (X - C (1 - (r : ℂ))) ^ (n + 3) *
      (X - C (1 - (s n : ℂ))) ^ (n + 3)) * (X - C (1 - (q n : ℂ))) ^ 1 := by ring
  rw [he]
  have hn : (X - C (0 : ℂ)) * (X - C (1 - (r : ℂ))) ^ (n + 3) *
      (X - C (1 - (s n : ℂ))) ^ (n + 3) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (X_sub_C_ne_zero _) (pow_ne_zero _ (X_sub_C_ne_zero _)))
      (pow_ne_zero _ (X_sub_C_ne_zero _))
  rw [rootMultiplicity_mul_X_sub_C_pow hn]
  have hd := complex_eigenvalues_distinct n
  have hr : ¬ IsRoot ((X - C (0 : ℂ)) * (X - C (1 - (r : ℂ))) ^ (n + 3) *
      (X - C (1 - (s n : ℂ))) ^ (n + 3)) (1 - (q n : ℂ)) := by
    simp [IsRoot, sub_eq_zero, hd.2.2.2.1, Ne.symm hd.2.2.2.1,
      hd.2.2.2.2, Ne.symm hd.2.1]
    have ho := eigenvalues_ordered n
    constructor <;> intro h <;> linarith [ho.2.2.1, ho.2.1]
  rw [rootMultiplicity_eq_zero hr, zero_add]

lemma gapModeRatio_eq (n : ℕ) :
    (gapModeMultiplicity n : ℝ) / spectralGap n = size n := by
  rw [gapModeMultiplicity_eq_one, spectralGap_eq]
  simp

lemma fourierEigenvalue_classification (n : ℕ) (ψ : Characters n) :
    fourierEigenvalue n ψ = 1 ∨ fourierEigenvalue n ψ = (q n : ℂ) ∨
      fourierEigenvalue n ψ = (r : ℂ) ∨ fourierEigenvalue n ψ = (s n : ℂ) := by
  by_cases h : ψ = 0
  · exact Or.inl ((fourierEigenvalue_eq_one_iff n ψ).2 h)
  · exact Or.inr (fourierEigenvalue_nontrivial n ψ h)

lemma charpoly_isRoot_iff (n : ℕ) (z : ℂ) :
    IsRoot (complexTransition n).charpoly z ↔
      z = 1 ∨ z = (q n : ℂ) ∨ z = (r : ℂ) ∨ z = (s n : ℂ) := by
  simp [complexTransition_charpoly, IsRoot, sub_eq_zero, or_assoc]

lemma complement_charpoly_isRoot_iff (n : ℕ) (z : ℂ) :
    IsRoot (complexComplement n).charpoly z ↔
      z = 0 ∨ z = 1 - (q n : ℂ) ∨ z = 1 - (r : ℂ) ∨ z = 1 - (s n : ℂ) := by
  simp [complexComplement_charpoly, IsRoot, sub_eq_zero, or_assoc]

lemma complement_character_positive_iff (n : ℕ) (ψ : Characters n) :
    0 < (1 - fourierEigenvalue n ψ).re ↔ ψ ≠ 0 := by
  constructor
  · intro hp he
    rw [(fourierEigenvalue_eq_one_iff n ψ).2 he] at hp
    simp at hp
  · intro hψ
    have ho := eigenvalues_ordered n
    rcases fourierEigenvalue_nontrivial n ψ hψ with h | h | h <;> rw [h] <;>
      simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re] <;>
      linarith [ho.2.2.2, ho.2.2.1, ho.2.1]

/-- Minimum over the positive character eigenvalues of the actual operator `I-P`. -/
def minPositiveComplementEigenvalue (n : ℕ) : ℝ :=
  (nontrivialCharacters n).inf' (nontrivialCharacters_nonempty n)
    (fun ψ => (1 - fourierEigenvalue n ψ).re)

lemma minPositiveComplementEigenvalue_eq_gap (n : ℕ) :
    minPositiveComplementEigenvalue n = spectralGap n := by
  classical
  rw [spectralGap, maxNontrivialEigenvalue_eq_q]
  apply le_antisymm
  · obtain ⟨ψ,hψ,he⟩ := exists_character_q n
    have hm : ψ ∈ nontrivialCharacters n := by simp [nontrivialCharacters, hψ]
    have hh := Finset.inf'_le (s := nontrivialCharacters n)
      (f := fun ψ => (1 - fourierEigenvalue n ψ).re) hm
    simpa [he, minPositiveComplementEigenvalue] using hh
  · apply Finset.le_inf'
    intro ψ hψ
    have hn : ψ ≠ 0 := by simpa [nontrivialCharacters] using hψ
    have ho := eigenvalues_ordered n
    rcases fourierEigenvalue_nontrivial n ψ hn with h | h | h <;> rw [h] <;>
      simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re] <;>
      linarith [ho.2.2.1, ho.2.1]

lemma complement_roots_nonnegative (n : ℕ) (z : ℂ)
    (hz : IsRoot (complexComplement n).charpoly z) :
    z.im = 0 ∧ 0 ≤ z.re := by
  have ho := eigenvalues_ordered n
  rcases (complement_charpoly_isRoot_iff n z).1 hz with h | h | h | h <;> rw [h] <;>
    simp only [Complex.zero_im, Complex.zero_re, le_refl, and_self,
      Complex.sub_im, Complex.one_im, Complex.ofReal_im, sub_self,
      Complex.sub_re, Complex.one_re, Complex.ofReal_re, true_and]
  all_goals linarith [ho.2.2.2, ho.2.2.1, ho.2.1]

lemma spectralGap_le_positive_complement_root (n : ℕ) (z : ℂ)
    (hz : IsRoot (complexComplement n).charpoly z) (hpos : 0 < z.re) :
    spectralGap n ≤ z.re := by
  rw [spectralGap, maxNontrivialEigenvalue_eq_q]
  have ho := eigenvalues_ordered n
  rcases (complement_charpoly_isRoot_iff n z).1 hz with rfl | rfl | rfl | rfl <;>
    simp only [Complex.zero_re, Complex.sub_re, Complex.one_re, Complex.ofReal_re] at * <;>
    linarith [ho.2.2.1, ho.2.1]

lemma fourierEigenvalue_real (n : ℕ) (ψ : Characters n) :
    ((fourierEigenvalue n ψ).re : ℂ) = fourierEigenvalue n ψ := by
  rcases fourierEigenvalue_classification n ψ with h | h | h | h <;> rw [h] <;> simp

lemma fourierEigenvalue_im_eq_zero (n : ℕ) (ψ : Characters n) :
    (fourierEigenvalue n ψ).im = 0 := by
  rw [← fourierEigenvalue_real n ψ]
  exact Complex.ofReal_im _

lemma fourierEigenvalue_positive (n : ℕ) (ψ : Characters n) :
    0 < (fourierEigenvalue n ψ).re := by
  have ho := eigenvalues_ordered n
  rcases fourierEigenvalue_classification n ψ with h | h | h | h <;> rw [h] <;>
    simp only [Complex.one_re, Complex.ofReal_re] <;>
    linarith [ho.1, ho.2.1, ho.2.2.1]

end Conjecture1421
