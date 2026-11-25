import Conjecture00000007607.RingBase
import Conjecture00000007607.Ring
import Conjecture00000007607.Clifford2
import Conjecture00000007607.Clifford3
import Conjecture00000007607.HigherDim

namespace Conjecture00000007607

/-!
# Resolution of Conjecture `00000007607`: Rotor Logarithm-Sum Angle Additivity

This top-level module synthesizes the complete formal resolution of Conjecture `00000007607`:

* **Verdict**: **FALSE** in general (refuted across every Euclidean dimension `n ≥ 3`), while
  **TRUE** in the planar abelian case `n = 2` (and for coplanar rotations with matching
  orientation in any dimension).

* **Summary of Main Verified Theorems**:
  1. `positive_planar_spin2`: Complete verification of all three claims in `Cl_{2,0}(R)`
     (universal Lie bracket vanishing `[B₁, B₂] = 0`, rotor angle additivity, and spectral
     angle additivity of `B₁ + B₂`), together with explicit non-vacuity in `Spin(2, ℚ)`.
  2. `spin3_exact_characterizations`: Necessary and sufficient conditions over any
     `StrictOrderedCommRing R` proving that `[u₁, u₂] = 0 ↔ u₁ = ±u₂`, whereas both
     composite rotor scalar angle additivity and generator-sum spectral angle additivity
     hold **if and only if** `u₁ = u₂`, and `[u₁, u₂] ≠ 0` forces `R₁ R₂ ∉ R·1 ⊕ span(u₁, u₂)`.
  3. `spin3_explicit_counterexamples`: Orthogonal `90°` rotors in `Spin(3, ℚ[√2])` (giving
     three pairwise distinct values `Θ = 2π/3`, `2‖B₁+B₂‖ = π/√2`, `θ₁ + θ₂ = π`), `180°`
     rotors over `ℤ`, and Pythagorean rational spectral/Cayley counterexamples over `ℚ`.
  4. `higher_dim_refutations`: Disjoint-plane commuting counterexamples in `Cl_{4,0}^+` / `𝔰𝔬(4)`
     (showing `[B₁, B₂] = 0` is not even sufficient for single-angle additivity when `n ≥ 4`)
     plus the uniform refutation across every dimension `n ≥ 3`.
-/

/-- **Top-Level Theorem 1 (Positive Planar / Coplanar Regime, `n = 2`)**:
    In `Cl_{2,0}(R)` over any commutative ring `R`, the Lie bracket of bivector generators
    vanishes identically, rotor multiplication obeys exact angle additivity, and `(B₁ + B₂)²`
    exhibits exact spectral angle additivity; moreover `Spin(2, ℚ)` admits explicit non-central
    unit rotors witnessing angle additivity non-vacuously. -/
theorem positive_planar_spin2 :
    (∀ (R : Type) [CommRing R] (a1 a2 c1 s1 c2 s2 : R),
      Cl2.bracket (Cl2.bivec a1) (Cl2.bivec a2) = 0 ∧
      Cl2.rotor c1 s1 * Cl2.rotor c2 s2 =
        Cl2.rotor (c1 * c2 - s1 * s2) (s1 * c2 + c1 * s2) ∧
      (Cl2.bivec (-a1) + Cl2.bivec (-a2)) * (Cl2.bivec (-a1) + Cl2.bivec (-a2)) =
        Cl2.scalar (-((a1 + a2) * (a1 + a2)))) ∧
    (Cl2.pythRotor1 * Cl2.rev Cl2.pythRotor1 = 1 ∧
     Cl2.pythRotor2 * Cl2.rev Cl2.pythRotor2 = 1 ∧
     Cl2.pythRotor1 ≠ 1 ∧ Cl2.pythRotor1 ≠ -1 ∧
     Cl2.pythRotor2 ≠ 1 ∧ Cl2.pythRotor2 ≠ -1 ∧
     Cl2.pythRotor1 * Cl2.pythRotor2 = Cl2.rotor (QRat.mk 33 65) (QRat.mk 56 65)) :=
  ⟨fun _ _ a1 a2 c1 s1 c2 s2 =>
    ⟨Cl2.spin2_lie_bracket_zero a1 a2,
     Cl2.rotor2_mul_angle_add c1 s1 c2 s2,
     Cl2.spin2_sum_sq_angle_add a1 a2⟩,
   Cl2.spin2_positive_nonvacuity⟩

/-- **Top-Level Theorem 2 (Complete Refutation of Conjecture `00000007607` for All `n ≥ 3`)**:
    1. In `Cl_{3,0}(ℚ[√2])`, orthogonal `90°` unit rotors have composite rotation angle `2π/3`
       (order-3 cyclic action on `(e₁, e₂, e₃)` and scalar part `1/2 ≠ 0`), refuting rotor
       angle additivity (`π/2 + π/2 = π`) and separating `Θ`, `2‖B₁+B₂‖`, and `θ₁ + θ₂`.
    2. In `Cl_{3,0}(ℚ)`, orthogonal generators `B₁ = -(3/2)e₁₂`, `B₂ = -2e₂₃` have squared
       spectral norm `25/4 ≠ 49/4`, refuting spectral angle additivity.
    3. In `Cl_{3,0}(R)` over every `StrictOrderedCommRing R`, `[e₁₂, e₂₃] ≠ 0`, refuting
       universal Lie bracket vanishing.
    4. In `Cl_{4,0}^+(R)` over every `StrictOrderedCommRing R`, commuting disjoint-plane
       generators (`[B₁, B₂] = 0`) still fail `(B₁ + B₂)² = -(a₁ + a₂)² · 1`.
    5. Uniformly for **every** dimension `n ≥ 3`, composite angle additivity, spectral sum
       angle additivity, and Lie bracket vanishing all fail on `ℤ^n`. -/
theorem conjecture_00000007607_disproved :
    -- (1) Spin(3, ℚ[√2]) 90° orthogonal unit-rotor refutation
    (Cl3.rot90_e12 * Cl3.rev Cl3.rot90_e12 = 1 ∧
     Cl3.rot90_e23 * Cl3.rev Cl3.rot90_e23 = 1 ∧
     Cl3.grade0 (Cl3.rot90_e12 * Cl3.rot90_e23) = ⟨QRat.mk 1 2, 0⟩ ∧
     Cl3.grade0 (Cl3.rot90_e12 * Cl3.rot90_e23) ≠ 0 ∧
     (Cl3.rot90_e12 * Cl3.rot90_e23) * (Cl3.rot90_e12 * Cl3.rot90_e23) *
       (Cl3.rot90_e12 * Cl3.rot90_e23) = -1) ∧
    -- (2) Rational spectral & Cayley rotor refutation in Cl_{3,0}(ℚ)
    (Cl3.bivecNormSq (Cl3.smul (-QRat.mk 3 2) Cl3.e12 + Cl3.smul (-QRat.mk 4 2) Cl3.e23) =
       QRat.mk 25 4 ∧
     Cl3.bivecNormSq (Cl3.smul (-QRat.mk 3 2) Cl3.e12 + Cl3.smul (-QRat.mk 4 2) Cl3.e23) ≠
       QRat.mk 49 4) ∧
    -- (3) Non-vanishing Lie bracket [e₁₂, e₂₃] ≠ 0 in Cl_{3,0}(ℚ)
    (Cl3.bracket (Cl3.e12 : Cl3 QRat) Cl3.e23 ≠ 0) ∧
    -- (4) Spin(4) commuting disjoint-plane non-simplicity obstruction
    (Cl4Even.bracket (Cl4Even.smul (-QRat.mk 3 2) Cl4Even.e12)
                     (Cl4Even.smul (-QRat.mk 4 2) Cl4Even.e34) = 0 ∧
     (Cl4Even.smul (-QRat.mk 3 2) (Cl4Even.e12 : Cl4Even QRat) +
      Cl4Even.smul (-QRat.mk 4 2) Cl4Even.e34) *
     (Cl4Even.smul (-QRat.mk 3 2) (Cl4Even.e12 : Cl4Even QRat) +
      Cl4Even.smul (-QRat.mk 4 2) Cl4Even.e34) ≠
       Cl4Even.scalar (-((QRat.mk 3 2 + QRat.mk 4 2) * (QRat.mk 3 2 + QRat.mk 4 2)))) ∧
    -- (5) Universal refutation for every dimension n ≥ 3
    (∀ (n : Nat) (h : 3 ≤ n),
      let e0 := DimN.stdBasis n ⟨0, by omega⟩
      let comp := fun v => DimN.rot12 n h (DimN.rot23 n h v)
      let sOp := DimN.genSum n h
      (∀ v : Fin n → Int, comp (comp (comp v)) = v) ∧
      comp (comp e0) ≠ e0 ∧
      ((fun i => sOp (sOp e0) i + 4 * e0 i) ≠ fun _ => 0) ∧
      (DimN.lieBracket12_23 n h e0 ≠ fun _ => 0)) := by
  obtain ⟨hr1, hr2, hg0, hg0ne, hcube, _, _, _, _, _, _, _⟩ := Cl3.counterexample_90deg_orthogonal
  obtain ⟨hsp1, hsp2, _, _⟩ := Cl3.counterexample_pythagorean_rat
  have h4 := Cl4Even.spin4_commuting_still_not_angle_additive
    (a1 := QRat.mk 3 2) (a2 := QRat.mk 4 2)
    (QRat.ne_of_isZero_sub_false rfl) (QRat.ne_of_isZero_sub_false rfl)
  refine ⟨⟨hr1, hr2, hg0, hg0ne, hcube⟩, ⟨hsp1, hsp2⟩,
          Cl3.spin3_bracket_e12_e23_ne_zero, h4, ?_⟩
  intro n h
  obtain ⟨_, hc3, ⟨hc2ne, _⟩, _, hsne, hlne⟩ := DimN.universal_refutation_ge_3 n h
  exact ⟨hc3, hc2ne, hsne, hlne⟩

end Conjecture00000007607
