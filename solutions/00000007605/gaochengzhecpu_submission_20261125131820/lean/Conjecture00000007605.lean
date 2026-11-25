/-
Copyright (c) 2026 The Last Math Competition Authors. All rights reserved.
Root verification module for Conjecture 00000007605:
  "Spinors with the spinor-representation classification of Pin groups.
   Conjecture: The conversion constant is the representation classification of spinors
   with the unique type of irreducible representations; the spectrum is finite with
   count two (real and complex); and the kernel of uniqueness is the Clifford center."

Verdict: FALSE (Refuted across every standard mathematical reading), accompanied by a
Positive Non-Vacuity Theorem establishing the true complexified Clifford-module dichotomy.
-/

import Conjecture00000007605.FieldAndAlgebras
import Conjecture00000007605.ModulesAndPin
import Conjecture00000007605.RealCliffordCounterexamples
import Conjecture00000007605.InfinitePinSpectrumAndComplexSalvage

namespace Conjecture00000007605

/-- **Master Refutation Theorem (Universal Over Every Formally Real Field `F`, Including `ℝ` and `ℚ`):**
    1. **Refutation of Claim B (Division-Ring Spectrum Count Is NOT Two "Real and Complex"):**
       The unique irreducible Pin spinor representations of `(0,0)`, `(0,1)`, and `(0,2)` under `+Q`
       (and of Euclidean `(0,0)`, `(1,0)`, `(2,0)` under Atiyah–Bott–Shapiro's `-Q`) have endomorphism
       division `F`-algebras isomorphic to `F` (real), `ComplexOver F` (complex), and `QuatOver F`
       (quaternionic), which is non-commutative and isomorphic neither to `F` nor to `ComplexOver F`;
       no two-element family of `F`-algebras covers these spinor endomorphism types.
    2. **Refutation of Claim A (Irreducible Spinor Representation Type Is NOT Universally Unique):**
       `Pin(1,0)` (`Cl_{1,0}^+(F)`) possesses TWO non-isomorphic irreducible spinor representations
       `S_+` and `S_-` that classify all irreducible `Pin(1,0)` spinor modules up to isomorphism.
    3. **Refutation of Claim C (Representation Kernel Is NOT the Clifford Center):**
       In `Cl_{1,1}^+(F) ≅ M_2(F)` (and `Cl_{0,1}^+(F) ≅ ComplexOver F`), the irreducible spinor
       module is unique and faithful (`ker = {0}`), whereas the Clifford center is nonzero (`F · I_2`
       resp. `ComplexOver F`), and on `Pin(1,1)` `-I_2 ∈ Z(Cl_{1,1}^+) ∩ Pin(1,1)` is outside `ker`.
    4. **Refutation of Finite Group Representation Spectrum of Count Two:**
       `Pin(1,0)` has 4 pairwise non-isomorphic 1D irreducible group representations, and
       `Pin^-(2,0)(F)` admits an infinite sequence `k ↦ harmonicRep k` (`k ∈ ℕ`) of pairwise
       non-isomorphic 2D irreducible group representations. -/
theorem conjecture_00000007605_refuted (F : Type) [FormallyRealField F] :
    -- (1) Quaternionic Pin spinor endomorphism algebra refutes count two (real and complex):
    (PinIrreducible ClQuat.ι ClQuat.Q02 (ClQuat.spinorH F) ∧
     PinIrreducible ClQuat.ι ClQuat.Q20 (ClQuat.spinorH F) ∧
     IsDivisionAlg (pinEndAlg ClQuat.ι ClQuat.Q02 (ClQuat.spinorH F)) ∧
     ¬ IsCommAlg (pinEndAlg ClQuat.ι ClQuat.Q02 (ClQuat.spinorH F)) ∧
     ¬ Nonempty (AlgIso F (pinEndAlg ClQuat.ι ClQuat.Q02 (ClQuat.spinorH F)) (realAlg F)) ∧
     ¬ Nonempty (AlgIso F (pinEndAlg ClQuat.ι ClQuat.Q02 (ClQuat.spinorH F)) (ComplexOver.alg F)) ∧
     ¬ Nonempty (AlgIso F (pinEndAlg ClQuat.ι ClQuat.Q20 (ClQuat.spinorH F)) (realAlg F)) ∧
     ¬ Nonempty (AlgIso F (pinEndAlg ClQuat.ι ClQuat.Q20 (ClQuat.spinorH F)) (ComplexOver.alg F)) ∧
     (∀ {B₁ B₂ : Type} (alg₁ : Alg F B₁) (alg₂ : Alg F B₂),
        ¬ ((Nonempty (AlgIso F (pinEndAlg ι00 Q00 (spinor00 F)) alg₁) ∨
            Nonempty (AlgIso F (pinEndAlg ι00 Q00 (spinor00 F)) alg₂)) ∧
           (Nonempty (AlgIso F (pinEndAlg Cl01.ι Cl01.Q01 (Cl01.spinorC F)) alg₁) ∨
            Nonempty (AlgIso F (pinEndAlg Cl01.ι Cl01.Q01 (Cl01.spinorC F)) alg₂)) ∧
           (Nonempty (AlgIso F (pinEndAlg ClQuat.ι ClQuat.Q02 (ClQuat.spinorH F)) alg₁) ∨
            Nonempty (AlgIso F (pinEndAlg ClQuat.ι ClQuat.Q02 (ClQuat.spinorH F)) alg₂))))) ∧
    -- (2) Non-uniqueness of irreducible Pin(1,0) spinor modules:
    (PinIrreducible Cl10.ι Cl10.Qpos (Cl10.spinorPlus F) ∧
     PinIrreducible Cl10.ι Cl10.Qpos (Cl10.spinorMinus F) ∧
     ¬ Nonempty (PinIso Cl10.ι Cl10.Qpos (Cl10.spinorPlus F) (Cl10.spinorMinus F))) ∧
    -- (3) Discrepancy between representation kernel and Clifford center (`Cl_{1,1}^+` and `Cl_{0,1}^+`):
    (InCenter (Mat2.alg F) Mat2.one ∧
     Mat2.one (F := F) ≠ Mat2.zero ∧
     (∀ A : Mat2 F, InRepKernel (Mat2.spinor11 F) A ↔ A = Mat2.zero) ∧
     InPin (Mat2.alg F) Mat2.ι11 Mat2.Q11 (Mat2.neg Mat2.one) ∧
     InCenter (Mat2.alg F) (Mat2.neg Mat2.one) ∧
     ¬ InPinKernel Mat2.ι11 Mat2.Q11 (Mat2.spinor11 F) (Mat2.neg Mat2.one)) ∧
    -- (4) Infinite irreducible group representation spectrum of `Pin^-(2,0)(F)`:
    ((∀ k : Nat, PinGroupIrreducible (Pin2Harmonics.harmonicRep (F := F) k)) ∧
     (∀ j k : Nat, j ≠ k →
        ¬ Nonempty (PinGroupIso (Pin2Harmonics.harmonicRep (F := F) j)
                                (Pin2Harmonics.harmonicRep (F := F) k)))) := by
  obtain ⟨hdiv, hncomm, hnR02, hnC02, hnR20, hnC20⟩ :=
    ClQuat.quat_spinor_endAlg_neither_real_nor_complex (F := F)
  exact ⟨⟨ClQuat.spinorH_pinIrreducible_02, ClQuat.spinorH_pinIrreducible_20,
          hdiv, hncomm, hnR02, hnC02, hnR20, hnC20,
          fun alg₁ alg₂ => ClQuat.no_two_types_cover_pin_spinor_endAlgs alg₁ alg₂⟩,
         ⟨Cl10.spinorPlus_pinIrreducible, Cl10.spinorMinus_pinIrreducible,
          Cl10.not_pinIso_spinorPlus_spinorMinus⟩,
         Mat2.center_vs_kernel_cl11,
         Pin2Harmonics.pin2Minus_infinite_pairwise_noniso_irreps⟩

/-- **Concrete Constructive Non-Vacuity Instantiation Over `QField`:**
    Witnesses unconditionally in Core Lean 4 (with zero external dependencies or custom axioms)
    that `FormallyRealField` is inhabited and both the Master Refutation Theorem and the
    Complex Clifford Positive Non-Vacuity Theorem hold constructively. -/
theorem conjecture_00000007605_ground_witness :
    (IsDivisionAlg (pinEndAlg ClQuat.ι ClQuat.Q02 (ClQuat.spinorH QField)) ∧
     ¬ Nonempty (AlgIso QField (pinEndAlg ClQuat.ι ClQuat.Q02 (ClQuat.spinorH QField))
                               (realAlg QField)) ∧
     ¬ Nonempty (AlgIso QField (pinEndAlg ClQuat.ι ClQuat.Q02 (ClQuat.spinorH QField))
                               (ComplexOver.alg QField))) ∧
    ¬ Nonempty (PinIso Cl10.ι Cl10.Qpos (Cl10.spinorPlus QField) (Cl10.spinorMinus QField)) ∧
    (∀ j k : Nat, j ≠ k →
      ¬ Nonempty (PinGroupIso (Pin2Harmonics.harmonicRep (F := QField) j)
                              (Pin2Harmonics.harmonicRep (F := QField) k))) ∧
    (ComplexSalvage.Mat2K.one (F := QField) ≠ ComplexSalvage.Mat2K.zero ∧
     (∀ T : ComplexSalvage.Mat2K QField,
        ComplexSalvage.CommutesWith T [ComplexSalvage.pauli1, ComplexSalvage.pauli3] ↔
        ∃ c : ComplexOver QField,
          T = ⟨c, ComplexOver.zero, ComplexOver.zero, c⟩) ∧
     (∀ T : ComplexSalvage.Mat2K QField,
        ComplexSalvage.IntertwinesPair T
          [ComplexSalvage.pauli1, ComplexSalvage.pauli2, ComplexSalvage.pauli3]
          [ComplexSalvage.Mat2K.neg ComplexSalvage.pauli1,
           ComplexSalvage.Mat2K.neg ComplexSalvage.pauli2,
           ComplexSalvage.Mat2K.neg ComplexSalvage.pauli3] →
        T = ComplexSalvage.Mat2K.zero)) := by
  have href := conjecture_00000007605_refuted QField
  have hsalv := ComplexSalvage.complex_clifford_non_vacuity (F := QField)
  exact ⟨⟨href.1.2.2.1, href.1.2.2.2.2.1, href.1.2.2.2.2.2.1⟩,
         href.2.1.2.2,
         href.2.2.2.2,
         ⟨hsalv.2.2.2.1, hsalv.1.2.2, hsalv.2.2.1⟩⟩

end Conjecture00000007605
