import Mathlib

/-!
# Conjecture 00000007965: the smallest isospectral inequivalent pair is not at `(9,4)`

A binary linear code of length `n` is a subspace `C ≤ 𝔽₂ⁿ`. Its weight enumerator is
`A_C(z) = ∑_w A_w(C) zʷ`, where `A_w(C)` is the number of codewords of Hamming weight `w`.
Two codes are *isospectral* if they have the same weight enumerator, and *permutation
equivalent* if one is obtained from the other by permuting coordinates.

The second claim of Conjecture 00000007965 is that the minimal example of isospectral but
non-permutation-equivalent codes is the unique pair at `(n,k) = (9,4)`. Both parts fail.

* **Minimality.** The `[6,3]` codes with generator matrices
  `GA = (111001 / 000101 / 000011)` and `GB = (110000 / 001100 / 000011)` both have
  weight enumerator `1 + 3z² + 3z⁴ + z⁶`, but they are not permutation equivalent: the
  three weight-`2` words of `B` have pairwise disjoint supports, while any two distinct
  weight-`2` words of `A` share a coordinate. Since `6 < 9` and `3 < 4`, this pair is
  smaller than `(9,4)` in every sense.
* **Uniqueness.** Appending the coordinates of the repetition code `⟨111⟩`, respectively of
  the code `⟨100⟩`, gives two isospectral inequivalent pairs of `[9,4]` codes. The two
  pairs have different weight enumerators (`A₁ = 0` versus `A₁ = 1`), so they are not the
  same pair up to equivalence.
-/

namespace Submission00000007965

open Finset Matrix

/-- The binary field `𝔽₂`. -/
abbrev F2 := ZMod 2

/-- A binary linear code of length `n`: a linear subspace of `𝔽₂ⁿ`. -/
abbrev Code (n : ℕ) := Submodule F2 (Fin n → F2)

/-- `A_w(C)`: the number of codewords of `C` of Hamming weight `w` (Mathlib's
`hammingNorm`, the number of nonzero coordinates). -/
noncomputable def weightDist {n : ℕ} (C : Code n) (w : ℕ) : ℕ :=
  Nat.card {c : C // hammingNorm (c : Fin n → F2) = w}

/-- The weight enumerator `A_C(z) = ∑_{w=0}^{n} A_w(C) zʷ`. -/
noncomputable def weightEnumerator {n : ℕ} (C : Code n) : Polynomial ℕ :=
  ∑ w ∈ range (n + 1), Polynomial.monomial w (weightDist C w)

/-- Two codes are isospectral if they have the same weight enumerator. -/
def Isospectral {n : ℕ} (C D : Code n) : Prop :=
  weightEnumerator C = weightEnumerator D

/-- Permutation equivalence: for some permutation `σ` of the coordinates,
`D = {c ∘ σ | c ∈ C}`. -/
def PermEquiv {n : ℕ} (C D : Code n) : Prop :=
  ∃ σ : Equiv.Perm (Fin n), ∀ x : Fin n → F2, x ∈ C ↔ x ∘ σ ∈ D

/-- An isospectral pair of codes that are not permutation equivalent. -/
def IsospectralInequivalent {n : ℕ} (C D : Code n) : Prop :=
  Isospectral C D ∧ ¬ PermEquiv C D

/-- Second claim of the conjecture, minimality, in its weakest form: no isospectral
inequivalent pair has both `n < 9` and `k < 4`. Every reading of "the minimal example is at
`(n,k) = (9,4)`" implies this: minimal by length (`n ≥ 9`), by dimension (`k ≥ 4`), in the
componentwise order, lexicographically in either order, or by `n + k`. -/
def MinimalAtNineFour : Prop :=
  ∀ (n : ℕ) (C D : Code n), IsospectralInequivalent C D →
    9 ≤ n ∨ 4 ≤ Module.finrank F2 C

/-- Second claim of the conjecture, uniqueness: any two isospectral inequivalent pairs of
`[9,4]` codes are the same pair up to permutation equivalence and order. -/
def UniqueAtNineFour : Prop :=
  ∀ C D C' D' : Code 9,
    Module.finrank F2 C = 4 → Module.finrank F2 D = 4 →
    Module.finrank F2 C' = 4 → Module.finrank F2 D' = 4 →
    IsospectralInequivalent C D → IsospectralInequivalent C' D' →
    (PermEquiv C C' ∧ PermEquiv D D') ∨ (PermEquiv C D' ∧ PermEquiv D C')

/-- The second claim of Conjecture 00000007965: "the minimal example of isospectral but
non-permutation-equivalent codes is the unique pair at `(n,k) = (9,4)`". -/
def ConjectureClause2 : Prop :=
  MinimalAtNineFour ∧ UniqueAtNineFour

/-! ### General facts -/

/-- Isospectrality follows from equality of all `A_w`. -/
theorem isospectral_of_weightDist {n : ℕ} {C D : Code n}
    (h : ∀ w, weightDist C w = weightDist D w) : Isospectral C D := by
  unfold Isospectral weightEnumerator
  simp only [h]

/-- For an injective encoder `f : 𝔽₂ᵏ → 𝔽₂ⁿ`, `A_w(range f)` counts messages `x` with
`wt(f x) = w`. -/
theorem weightDist_range {k n : ℕ} (f : (Fin k → F2) →ₗ[F2] (Fin n → F2))
    (hf : Function.Injective f) (w : ℕ) :
    weightDist (LinearMap.range f) w = #{x | hammingNorm (f x) = w} := by
  classical
  unfold weightDist
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  exact (Nat.card_congr ((LinearEquiv.ofInjective f hf).toEquiv.subtypeEquiv
    (by intro x; simp))).symm

/-- The range of an injective encoder `𝔽₂ᵏ → 𝔽₂ⁿ` has dimension `k`. -/
theorem finrank_range {k n : ℕ} (f : (Fin k → F2) →ₗ[F2] (Fin n → F2))
    (hf : Function.Injective f) : Module.finrank F2 (LinearMap.range f) = k := by
  rw [LinearMap.finrank_range_of_inj hf, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]

/-- Permuting coordinates preserves the Hamming weight. -/
theorem hammingNorm_comp_perm {n : ℕ} (x : Fin n → F2) (σ : Equiv.Perm (Fin n)) :
    hammingNorm (x ∘ σ) = hammingNorm x := by
  unfold hammingNorm
  exact card_equiv σ (by simp)

/-- Permutation equivalent codes have the same weight distribution. -/
theorem weightDist_eq_of_permEquiv {n : ℕ} {C D : Code n} (h : PermEquiv C D) (w : ℕ) :
    weightDist C w = weightDist D w := by
  obtain ⟨σ, hσ⟩ := h
  unfold weightDist
  refine Nat.card_congr
    { toFun := fun c => ⟨⟨(c.1 : Fin n → F2) ∘ σ, (hσ _).1 c.1.2⟩,
        (hammingNorm_comp_perm _ σ).trans c.2⟩
      invFun := fun d => ⟨⟨(d.1 : Fin n → F2) ∘ σ.symm,
        (hσ _).2 (by simp [Function.comp_def])⟩,
        (hammingNorm_comp_perm _ σ.symm).trans d.2⟩
      left_inv := fun c => by
        apply Subtype.ext; apply Subtype.ext; funext i; simp
      right_inv := fun d => by
        apply Subtype.ext; apply Subtype.ext; funext i; simp }

/-- If any two distinct weight-`2` words of `C` share a coordinate, while `D` contains two
weight-`2` words with disjoint supports, then `C` and `D` are not permutation equivalent. -/
theorem not_permEquiv_of_disjoint {n : ℕ} {C D : Code n}
    (hC : ∀ x ∈ C, ∀ y ∈ C, hammingNorm x = 2 → hammingNorm y = 2 → x ≠ y →
      ∃ i, x i ≠ 0 ∧ y i ≠ 0)
    {b₁ b₂ : Fin n → F2} (h₁ : b₁ ∈ D) (h₂ : b₂ ∈ D)
    (hw₁ : hammingNorm b₁ = 2) (hw₂ : hammingNorm b₂ = 2) (hne : b₁ ≠ b₂)
    (hdisj : ∀ i, b₁ i = 0 ∨ b₂ i = 0) : ¬ PermEquiv C D := by
  rintro ⟨σ, hσ⟩
  have back : ∀ b : Fin n → F2, b ∈ D → b ∘ σ.symm ∈ C := fun b hb =>
    (hσ _).2 (by simpa [Function.comp_def] using hb)
  obtain ⟨i, hi₁, hi₂⟩ := hC _ (back b₁ h₁) _ (back b₂ h₂)
    (by rw [hammingNorm_comp_perm]; exact hw₁) (by rw [hammingNorm_comp_perm]; exact hw₂)
    (fun h => hne (funext fun j => by simpa using congrFun h (σ j)))
  rcases hdisj (σ.symm i) with h | h
  · exact hi₁ h
  · exact hi₂ h

/-- Codes with different `A_w` for some `w` are not permutation equivalent. -/
theorem not_permEquiv_of_weightDist_ne {n : ℕ} {C D : Code n} {w : ℕ}
    (h : weightDist C w ≠ weightDist D w) : ¬ PermEquiv C D :=
  fun he => h (weightDist_eq_of_permEquiv he w)

/-- `A_w(C) = 0` for `w > n`. -/
theorem filter_weight_eq_empty {k n : ℕ} (f : (Fin k → F2) → (Fin n → F2)) {w : ℕ}
    (hw : n < w) : #{x | hammingNorm (f x) = w} = 0 := by
  rw [card_eq_zero, filter_eq_empty_iff]
  intro x _ hx
  have := hammingNorm_le_card_fintype (x := f x)
  rw [Fintype.card_fin] at this
  omega

/-! ### The pair at length `6`, dimension `3` -/

/-- Generator matrix of `A`: codewords `(x₀, x₀, x₀, x₁, x₂, x₀+x₁+x₂)`. -/
def GA : Matrix (Fin 3) (Fin 6) F2 :=
  !![1, 1, 1, 0, 0, 1;
     0, 0, 0, 1, 0, 1;
     0, 0, 0, 0, 1, 1]

/-- Generator matrix of `B`: codewords `(x₀, x₀, x₁, x₁, x₂, x₂)`. -/
def GB : Matrix (Fin 3) (Fin 6) F2 :=
  !![1, 1, 0, 0, 0, 0;
     0, 0, 1, 1, 0, 0;
     0, 0, 0, 0, 1, 1]

/-- The `[6,3]` code generated by `GA`. -/
def codeA : Code 6 := LinearMap.range GA.vecMulLinear

/-- The `[6,3]` code generated by `GB`. -/
def codeB : Code 6 := LinearMap.range GB.vecMulLinear

theorem injective_GA : Function.Injective GA.vecMulLinear := by
  intro x y h
  have key : ∀ x y : Fin 3 → F2, x ᵥ* GA = y ᵥ* GA → x = y := by decide
  exact key x y h

theorem injective_GB : Function.Injective GB.vecMulLinear := by
  intro x y h
  have key : ∀ x y : Fin 3 → F2, x ᵥ* GB = y ᵥ* GB → x = y := by decide
  exact key x y h

theorem finrank_codeA : Module.finrank F2 codeA = 3 := finrank_range _ injective_GA

theorem finrank_codeB : Module.finrank F2 codeB = 3 := finrank_range _ injective_GB

/-- `A` and `B` have the same weight distribution, `(A₀,…,A₆) = (1,0,3,0,3,0,1)`. -/
theorem weightDist_codeA_eq_codeB (w : ℕ) : weightDist codeA w = weightDist codeB w := by
  unfold codeA codeB
  rw [weightDist_range _ injective_GA, weightDist_range _ injective_GB]
  rcases Nat.lt_or_ge 6 w with hw | hw
  · rw [filter_weight_eq_empty (⇑GA.vecMulLinear) hw,
      filter_weight_eq_empty (⇑GB.vecMulLinear) hw]
  · interval_cases w <;> decide

/-- The weight distribution of `A` (and hence of `B`), listed explicitly. -/
theorem weightDist_codeA :
    (weightDist codeA 0, weightDist codeA 1, weightDist codeA 2, weightDist codeA 3,
      weightDist codeA 4, weightDist codeA 5, weightDist codeA 6) = (1, 0, 3, 0, 3, 0, 1) := by
  unfold codeA
  simp only [weightDist_range _ injective_GA]
  decide

theorem isospectral_codeA_codeB : Isospectral codeA codeB :=
  isospectral_of_weightDist weightDist_codeA_eq_codeB

/-- Any two distinct weight-`2` words of `A` share a coordinate. -/
theorem codeA_weight_two_meet :
    ∀ x ∈ codeA, ∀ y ∈ codeA, hammingNorm x = 2 → hammingNorm y = 2 → x ≠ y →
      ∃ i, x i ≠ 0 ∧ y i ≠ 0 := by
  have key : ∀ m m' : Fin 3 → F2, hammingNorm (m ᵥ* GA) = 2 → hammingNorm (m' ᵥ* GA) = 2 →
      m ᵥ* GA ≠ m' ᵥ* GA → ∃ i, (m ᵥ* GA) i ≠ 0 ∧ (m' ᵥ* GA) i ≠ 0 := by decide
  rintro x ⟨m, rfl⟩ y ⟨m', rfl⟩
  exact key m m'

theorem not_permEquiv_codeA_codeB : ¬ PermEquiv codeA codeB :=
  not_permEquiv_of_disjoint codeA_weight_two_meet
    (b₁ := ![1, 1, 0, 0, 0, 0]) (b₂ := ![0, 0, 1, 1, 0, 0])
    (LinearMap.mem_range.2 ⟨![1, 0, 0], by decide⟩)
    (LinearMap.mem_range.2 ⟨![0, 1, 0], by decide⟩) (by decide) (by decide) (by decide)
    (by decide)

/-- `A` and `B` are isospectral but not permutation equivalent. -/
theorem isospectralInequivalent_codeA_codeB : IsospectralInequivalent codeA codeB :=
  ⟨isospectral_codeA_codeB, not_permEquiv_codeA_codeB⟩

/-- **Minimality fails**: the pair `(A, B)` has `(n,k) = (6,3)`. -/
theorem not_minimalAtNineFour : ¬ MinimalAtNineFour := by
  intro h
  have := h 6 codeA codeB isospectralInequivalent_codeA_codeB
  rw [finrank_codeA] at this
  omega

/-! ### Two different pairs at length `9`, dimension `4` -/

/-- `A ⊕ ⟨111⟩`: codewords `(x₀, x₀, x₀, x₁, x₂, x₀+x₁+x₂, x₃, x₃, x₃)`. -/
def GA1 : Matrix (Fin 4) (Fin 9) F2 :=
  !![1, 1, 1, 0, 0, 1, 0, 0, 0;
     0, 0, 0, 1, 0, 1, 0, 0, 0;
     0, 0, 0, 0, 1, 1, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 1, 1, 1]

/-- `B ⊕ ⟨111⟩`: codewords `(x₀, x₀, x₁, x₁, x₂, x₂, x₃, x₃, x₃)`. -/
def GB1 : Matrix (Fin 4) (Fin 9) F2 :=
  !![1, 1, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 1, 1, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 1, 1, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 1, 1, 1]

/-- `A ⊕ ⟨100⟩`: codewords `(x₀, x₀, x₀, x₁, x₂, x₀+x₁+x₂, x₃, 0, 0)`. -/
def GA2 : Matrix (Fin 4) (Fin 9) F2 :=
  !![1, 1, 1, 0, 0, 1, 0, 0, 0;
     0, 0, 0, 1, 0, 1, 0, 0, 0;
     0, 0, 0, 0, 1, 1, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 1, 0, 0]

/-- `B ⊕ ⟨100⟩`: codewords `(x₀, x₀, x₁, x₁, x₂, x₂, x₃, 0, 0)`. -/
def GB2 : Matrix (Fin 4) (Fin 9) F2 :=
  !![1, 1, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 1, 1, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 1, 1, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 1, 0, 0]

def codeA1 : Code 9 := LinearMap.range GA1.vecMulLinear
def codeB1 : Code 9 := LinearMap.range GB1.vecMulLinear
def codeA2 : Code 9 := LinearMap.range GA2.vecMulLinear
def codeB2 : Code 9 := LinearMap.range GB2.vecMulLinear

theorem injective_GA1 : Function.Injective GA1.vecMulLinear := by
  intro x y h
  have key : ∀ x y : Fin 4 → F2, x ᵥ* GA1 = y ᵥ* GA1 → x = y := by decide
  exact key x y h

theorem injective_GB1 : Function.Injective GB1.vecMulLinear := by
  intro x y h
  have key : ∀ x y : Fin 4 → F2, x ᵥ* GB1 = y ᵥ* GB1 → x = y := by decide
  exact key x y h

theorem injective_GA2 : Function.Injective GA2.vecMulLinear := by
  intro x y h
  have key : ∀ x y : Fin 4 → F2, x ᵥ* GA2 = y ᵥ* GA2 → x = y := by decide
  exact key x y h

theorem injective_GB2 : Function.Injective GB2.vecMulLinear := by
  intro x y h
  have key : ∀ x y : Fin 4 → F2, x ᵥ* GB2 = y ᵥ* GB2 → x = y := by decide
  exact key x y h

theorem weightDist_codeA1_eq_codeB1 (w : ℕ) : weightDist codeA1 w = weightDist codeB1 w := by
  unfold codeA1 codeB1
  rw [weightDist_range _ injective_GA1, weightDist_range _ injective_GB1]
  rcases Nat.lt_or_ge 9 w with hw | hw
  · rw [filter_weight_eq_empty (⇑GA1.vecMulLinear) hw,
      filter_weight_eq_empty (⇑GB1.vecMulLinear) hw]
  · interval_cases w <;> decide

theorem weightDist_codeA2_eq_codeB2 (w : ℕ) : weightDist codeA2 w = weightDist codeB2 w := by
  unfold codeA2 codeB2
  rw [weightDist_range _ injective_GA2, weightDist_range _ injective_GB2]
  rcases Nat.lt_or_ge 9 w with hw | hw
  · rw [filter_weight_eq_empty (⇑GA2.vecMulLinear) hw,
      filter_weight_eq_empty (⇑GB2.vecMulLinear) hw]
  · interval_cases w <;> decide

theorem codeA1_weight_two_meet :
    ∀ x ∈ codeA1, ∀ y ∈ codeA1, hammingNorm x = 2 → hammingNorm y = 2 → x ≠ y →
      ∃ i, x i ≠ 0 ∧ y i ≠ 0 := by
  have key : ∀ m m' : Fin 4 → F2, hammingNorm (m ᵥ* GA1) = 2 →
      hammingNorm (m' ᵥ* GA1) = 2 → m ᵥ* GA1 ≠ m' ᵥ* GA1 →
      ∃ i, (m ᵥ* GA1) i ≠ 0 ∧ (m' ᵥ* GA1) i ≠ 0 := by decide
  rintro x ⟨m, rfl⟩ y ⟨m', rfl⟩
  exact key m m'

theorem codeA2_weight_two_meet :
    ∀ x ∈ codeA2, ∀ y ∈ codeA2, hammingNorm x = 2 → hammingNorm y = 2 → x ≠ y →
      ∃ i, x i ≠ 0 ∧ y i ≠ 0 := by
  have key : ∀ m m' : Fin 4 → F2, hammingNorm (m ᵥ* GA2) = 2 →
      hammingNorm (m' ᵥ* GA2) = 2 → m ᵥ* GA2 ≠ m' ᵥ* GA2 →
      ∃ i, (m ᵥ* GA2) i ≠ 0 ∧ (m' ᵥ* GA2) i ≠ 0 := by decide
  rintro x ⟨m, rfl⟩ y ⟨m', rfl⟩
  exact key m m'

theorem isospectralInequivalent_codeA1_codeB1 : IsospectralInequivalent codeA1 codeB1 :=
  ⟨isospectral_of_weightDist weightDist_codeA1_eq_codeB1,
    not_permEquiv_of_disjoint codeA1_weight_two_meet
      (b₁ := ![1, 1, 0, 0, 0, 0, 0, 0, 0]) (b₂ := ![0, 0, 1, 1, 0, 0, 0, 0, 0])
      (LinearMap.mem_range.2 ⟨![1, 0, 0, 0], by decide⟩)
      (LinearMap.mem_range.2 ⟨![0, 1, 0, 0], by decide⟩) (by decide) (by decide)
      (by decide) (by decide)⟩

theorem isospectralInequivalent_codeA2_codeB2 : IsospectralInequivalent codeA2 codeB2 :=
  ⟨isospectral_of_weightDist weightDist_codeA2_eq_codeB2,
    not_permEquiv_of_disjoint codeA2_weight_two_meet
      (b₁ := ![1, 1, 0, 0, 0, 0, 0, 0, 0]) (b₂ := ![0, 0, 1, 1, 0, 0, 0, 0, 0])
      (LinearMap.mem_range.2 ⟨![1, 0, 0, 0], by decide⟩)
      (LinearMap.mem_range.2 ⟨![0, 1, 0, 0], by decide⟩) (by decide) (by decide)
      (by decide) (by decide)⟩

/-- `A₁` has no codeword of weight `1`. -/
theorem weightDist_codeA1_one : weightDist codeA1 1 = 0 := by
  unfold codeA1
  rw [weightDist_range _ injective_GA1]
  decide

/-- `A₂` and `B₂` each have exactly one codeword of weight `1`. -/
theorem weightDist_codeA2_one : weightDist codeA2 1 = 1 := by
  unfold codeA2
  rw [weightDist_range _ injective_GA2]
  decide

theorem weightDist_codeB2_one : weightDist codeB2 1 = 1 := by
  unfold codeB2
  rw [weightDist_range _ injective_GB2]
  decide

/-- **Uniqueness fails**: `(A₁, B₁)` and `(A₂, B₂)` are two isospectral inequivalent pairs
of `[9,4]` codes, and `A₁` is equivalent to neither `A₂` nor `B₂`. -/
theorem not_uniqueAtNineFour : ¬ UniqueAtNineFour := by
  intro h
  rcases h codeA1 codeB1 codeA2 codeB2 (finrank_range _ injective_GA1)
      (finrank_range _ injective_GB1) (finrank_range _ injective_GA2)
      (finrank_range _ injective_GB2) isospectralInequivalent_codeA1_codeB1
      isospectralInequivalent_codeA2_codeB2 with ⟨h₁, -⟩ | ⟨h₁, -⟩
  · exact not_permEquiv_of_weightDist_ne (w := 1)
      (by rw [weightDist_codeA1_one, weightDist_codeA2_one]; decide) h₁
  · exact not_permEquiv_of_weightDist_ne (w := 1)
      (by rw [weightDist_codeA1_one, weightDist_codeB2_one]; decide) h₁

/-- **Conjecture 00000007965 is false**: its second claim fails. -/
theorem conjecture_00000007965_false : ¬ ConjectureClause2 :=
  fun h => not_minimalAtNineFour h.1

/-- The conjecture is the conjunction of three claims; whatever the first (`P`) and the
third (`Q`) claim mean, the conjunction is false. -/
theorem conjecture_00000007965_false' (P Q : Prop) : ¬ (P ∧ ConjectureClause2 ∧ Q) :=
  fun h => conjecture_00000007965_false h.2.1

end Submission00000007965

#print axioms Submission00000007965.conjecture_00000007965_false
#print axioms Submission00000007965.not_uniqueAtNineFour
