/-
  Conjecture 00000007628 — Master Summary Theorems:
    1. Positive Non-Vacuity Theorem on Split Clifford Algebra `Cl_{1,1}(K) ≅ M₂(K)`
    2. Complete Multi-Reading Refutation Across All General Readings
  Core Lean 4.19.0 (zero external dependencies)
-/
import Conjecture00000007628.Field
import Conjecture00000007628.Mat2
import Conjecture00000007628.ExteriorAndQuat
import Conjecture00000007628.Automorphisms

namespace Conjecture00000007628

/-- **Positive Non-Vacuity Theorem (`Cl_{1,1}(K) ≅ M₂(K)` for `char(K) ≠ 2`):**
    On the nondegenerate split Clifford algebra `Cl_{1,1}(K) ≅ M₂(K)`:
    1. Orthogonal primitive idempotents `E₁₁ = ½(I₂ + γ₁)` and `E₂₂ = ½(I₂ - γ₁)` decompose
       `Cl_{1,1}(K) = S₁ ⊕ S₂` semisimply into minimal left ideals of spinor dimension `2 = 2^{2/2}`,
       with exact conversion ratio `dim Cl_{1,1}(K) / dim S₁ = 4 / 2 = 2`;
    2. The canonical Clifford-conjugation-covariant spinor pairing `ω` on `S₁ ≅ K²` is
       nondegenerate and alternating, and its pairing-preserving linear automorphism group
       `Aut_K(S₁, ω)` is literally the symplectic group `Sp₂(K) = {g ∈ M₂(K) | det g = 1}`. -/
theorem conjecture_00000007628_positive_split_case
    {K : Type} [CommField K] (hchar : (1 : K) + 1 ≠ 0) :
    -- (1) Exact Clifford relations & orthogonal idempotent semisimple decomposition
    (Mat2.mul (Mat2.cl11_g1 (K := K)) Mat2.cl11_g1 = Mat2.I2 ∧
     Mat2.mul (Mat2.cl11_g2 (K := K)) Mat2.cl11_g2 = Mat2.neg Mat2.I2 ∧
     Mat2.smul (CommField.half K) (Mat2.add Mat2.I2 Mat2.cl11_g1) = Mat2.E11) ∧
    (∀ X : Mat2 K, Mat2.add (Mat2.mul X Mat2.E11) (Mat2.mul X Mat2.E22) = X) ∧
    -- (2) Minimal left ideal `S₁` is simple (`dim_K S₁ = 2`)
    (∀ u : Vec2 K, u ≠ Vec2.zero → ∀ w : Vec2 K, ∃ X : Mat2 K, Mat2.act X u = w) ∧
    -- (3) Canonical spinor pairing `ω` is Clifford-covariant and its isometry group is `Sp₂(K)`
    (∀ (X : Mat2 K) (u v : Vec2 K),
      Mat2.omega (Mat2.act X u) v = Mat2.omega u (Mat2.act (Mat2.cliffConj X) v)) ∧
    (∀ g : Mat2 K,
      (∀ u v : Vec2 K, Mat2.omega (Mat2.act g u) (Mat2.act g v) = Mat2.omega u v) ↔
      Mat2.det g = 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨Mat2.cl11_relations.1, Mat2.cl11_relations.2.1, (Mat2.cl11_idempotents hchar).1⟩
  · intro X; exact (Mat2.cl11_semisimple_decomposition X).2.2.1
  · intro u hu w; exact Mat2.S1_is_minimal_left_ideal hu w
  · exact Mat2.omega_clifford_covariant
  · exact Mat2.preserves_omega_iff_det_eq_one

/-- **Complete Multi-Reading Refutation of Conjecture 00000007628:**
    Every unqualified clause of Conjecture 00000007628 fails under standard definitions:
    1. **Minimal two-sided ideal dimension (`4 ≠ 2`):** `Cl_{1,1}(K) ≅ M₂(K)` is simple, so its
       unique minimal nonzero two-sided ideal is `M₂(K)` of dimension `4 ≠ 2 = d_spin`;
    2. **Degenerate quadratic forms (`Λ(K²) = Cl(K², 0)`):** `Λ(K²)` has no nontrivial idempotents,
       fails semisimple complementation, and its unique minimal nonzero left ideal `K e₁₂` has
       dimension `1 ≠ 2 = 2^⌊2/2⌋`;
    3. **Nondegenerate division Clifford algebras (`Cl_{0,2}(ℚ) = ℍ_ℚ`):** strict norm positivity
       `conj(q) * q = normSq(q) • 1 > 0` forces minimal left ideal dimension `4 ≠ 2 = 2^⌊2/2⌋`;
    4. **Ideal automorphism group ≠ symplectic group across ALL five definitions:**
       - `Aut_{Cl}(S₁) ≇ Sp₂(F)` (abelian vs. non-abelian),
       - `GL_K(S₁) ≠ Sp₂(K)` (`det = -1` reflection; odd dim 1 on `Cl_{1,0}(K)` has no symplectic form),
       - `Aut_{K-alg}(S₁) ≅ Aff₁(K) ≇ Sp₂(F)` (2-step solvable vs. non-abelian derived subgroup),
       - `Aut_{K-alg}(M₂(K)) ≇ Sp₂(F)` (trivial center vs. nontrivial center `{±I₂}`),
       - Reversion spinor form on `Cl_{2,0}(K)` is symmetric (`O₂`, order `8 ≠ 24` over `𝔽₃`), and
         at `n = 8` (`Cl_{4,4}(K) ≅ M₁₆(K)`) BOTH reversion and Clifford conjugation are orthogonal
         (`136 ≠ 120`), plus exact `𝔽₃` order spectrum `{2, 6, 8, 24, 48}`. -/
theorem conjecture_00000007628_complete_refutation
    {K F : Type} [CommField K] [CommField F]
    (hcharK : (1 : K) + 1 ≠ 0) (hcharF : (1 : F) + 1 ≠ 0) :
    -- 1. Two-sided simplicity of `Cl_{1,1}(K) ≅ M₂(K)` (`dim = 4 ≠ 2`)
    (∀ X : Mat2 K, X ≠ Mat2.zero →
      ∃ L1 R1 L2 R2 : Mat2 K,
        Mat2.add (Mat2.mul (Mat2.mul L1 X) R1) (Mat2.mul (Mat2.mul L2 X) R2) = Mat2.I2) ∧
    -- 2. Exterior algebra `Cl(K², 0) = Λ(K²)` has unique minimal left ideal of dim `1` & is not semisimple
    (∀ x : Ext2 K, x ≠ Ext2.zero → ∃ m : Ext2 K, Ext2.mul m x = Ext2.e12) ∧
    (∀ L : Ext2 K → Prop,
      (∀ m l, L l → L (Ext2.mul m l)) →
      (∀ x, Ext2.inTopIdeal x → L x → x = Ext2.zero) →
      (∃ u l, Ext2.inTopIdeal u ∧ L l ∧ Ext2.add u l = Ext2.one) → False) ∧
    -- 3. Quaternionic `Cl_{0,2}(ℤ)` norm anisotropy (`dim ℍ_ℚ = 4 ≠ 2`)
    (∀ q : QuatInt, q ≠ QuatInt.zero →
      QuatInt.mul (QuatInt.conj q) q = QuatInt.scale (QuatInt.normSq q) QuatInt.one ∧
      0 < QuatInt.normSq q) ∧
    -- 4A. Left `Cl`-module automorphisms `≇ Sp₂(F)`
    (MulEquiv (ClModAut K) ClModAut.comp (Sp2 F) Sp2.mul → False) ∧
    -- 4B. `GL_K(S₁) ≠ Sp₂(K)` & 1D minimal ideal of `Cl_{1,0}(K)` has no alternating form
    (∃ refl : Mat2 K, Mat2.det refl ≠ 0 ∧
      ¬ (∀ u v : Vec2 K, Mat2.omega (Mat2.act refl u) (Mat2.act refl v) = Mat2.omega u v)) ∧
    -- 4C. Non-unital left-ideal algebra automorphisms `Aff₁(K) ≇ Sp₂(F)`
    (MulEquiv (Aff1 K) Aff1.mul (Sp2 F) Sp2.mul → False) ∧
    -- 4D. Unital two-sided ideal algebra automorphisms `Aut_{K-alg}(M₂(K)) ≇ Sp₂(F)`
    (MulEquiv (Mat2AlgAut K) Mat2AlgAut.comp (Sp2 F) Sp2.mul → False) ∧
    -- 4E. Exact `𝔽₃` group order spectrum `{2, 6, 8, 24, 48}` and `n = 8` mod-8 orthogonality
    ((F3Spectrum.allMat2.filter F3Spectrum.isClModAutB).length = 2 ∧
     (F3Spectrum.allMat2.filter F3Spectrum.isS1AlgAutB).length = 6 ∧
     (F3Spectrum.allMat2.filter F3Spectrum.isOrthogCl20B).length = 8 ∧
     (F3Spectrum.allMat2.filter F3Spectrum.isSp2B).length = 24 ∧
     (F3Spectrum.allMat2.filter F3Spectrum.isGL2B).length = 48) ∧
    (Mod8Periodicity.countFixedBlades 8 Mod8Periodicity.revFixed ≠ Mod8Periodicity.skewDim 16 ∧
     Mod8Periodicity.countFixedBlades 8 Mod8Periodicity.conjFixed ≠ Mod8Periodicity.skewDim 16) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro X hX; exact Mat2.mat2_is_simple_two_sided hX
  · intro x hx; exact Ext2.e12_mem_every_nonzero_left_ideal hx
  · exact Ext2.ext2_no_semisimple_complement
  · intro q hq; exact QuatInt.conj_mul_self_and_norm_pos hq
  · exact no_iso_clModAut_sp2
  · exact ⟨⟨-1, 0, 0, 1⟩, gl2_not_equal_sp2 hcharK⟩
  · exact no_iso_s1AlgAut_sp2 hcharF
  · exact no_iso_mat2AlgAut_sp2 hcharF
  · exact F3Spectrum.f3_exact_group_orders
  · exact ⟨Mod8Periodicity.cl8_both_involutions_orthogonal_not_symplectic.2.2.2.2.1,
           Mod8Periodicity.cl8_both_involutions_orthogonal_not_symplectic.2.2.2.2.2⟩

/-- Concrete instantiation over `K = F = 𝔽₃` demonstrating non-vacuous unconditional refutation. -/
theorem conjecture_00000007628_refuted_over_F3 :
    (MulEquiv (ClModAut F3) ClModAut.comp (Sp2 F3) Sp2.mul → False) ∧
    (MulEquiv (Aff1 F3) Aff1.mul (Sp2 F3) Sp2.mul → False) ∧
    (MulEquiv (Mat2AlgAut F3) Mat2AlgAut.comp (Sp2 F3) Sp2.mul → False) :=
  ⟨no_iso_clModAut_sp2,
   no_iso_s1AlgAut_sp2 F3.char_ne_two,
   no_iso_mat2AlgAut_sp2 F3.char_ne_two⟩

end Conjecture00000007628
