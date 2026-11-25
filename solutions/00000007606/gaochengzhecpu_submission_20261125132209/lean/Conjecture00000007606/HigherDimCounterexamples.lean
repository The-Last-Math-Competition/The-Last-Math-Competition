/-
  Conjecture 00000007606 — Higher-Dimensional Counterexamples (`n = 4` and `n = 6`)

  Refutes BOTH natural readings of "Definition: Rotors as unit elements of the even subalgebra":
    1. **Invertible even elements `(Cl_{4,0}(K)⁺)ˣ` (`n = 4`):**
       Over ANY ordered field `K` (including concrete `ℚ` and `ℝ`), the invertible even
       element `x = 1 + 2 e_{1234} ∈ (Cl_{4,0}(K)⁺)ˣ` (inverse `-(1 - 2 e_{1234}) / 3`)
       does NOT preserve the vector space `V ⊂ Cl_{4,0}(K)` under `Ad_x(v) = x v x⁻¹`
       (`Ad_x(e_4)` acquires a nonzero grade-3 trivector component `(-4/3) e_{123} ∉ V`).
    2. **Unit-norm even elements `{x ∈ Cl_{6,0}(K)⁺ : x x̃ = 1}` (`n = 6`, Chevalley–Porteous):**
       Even restricting to unit Clifford norm `x x̃ = x̃ x = 1` inside `Cl_{6,0}(K)⁺`,
       over ANY ordered field `K` (including concrete `ℚ` and `ℝ`), the unit-norm even
       element `x = (3/5) + (4/5) e_{123456}` satisfies `x ∈ Cl_{6,0}(K)⁺` and
       `x x̃ = x̃ x = 1`, yet `Ad_x(e_6) = x e_6 x⁻¹` acquires a nonzero grade-5
       pentavector component `(24/25) e_{12345} ∉ V`.
-/

import Conjecture00000007606.Clifford

namespace Conjecture00000007606

abbrev sig30 (K : Type) [FieldK K] : List K := [FieldK.one, FieldK.one, FieldK.one]
abbrev sig40 (K : Type) [FieldK K] : List K := FieldK.one :: sig30 K
abbrev sig50 (K : Type) [FieldK K] : List K := FieldK.one :: sig40 K
abbrev sig60 (K : Type) [FieldK K] : List K := FieldK.one :: sig50 K

section HigherDimFailure
variable {K : Type} [O : OrderedFieldK K]

private def three : K := FieldK.add FieldK.two FieldK.one
private def four : K := FieldK.add FieldK.two FieldK.two
private def five : K := FieldK.add four FieldK.one

private theorem pos_ne_zero {a : K} (hpos : O.le FieldK.one a) : a ≠ FieldK.zero := by
  intro h0
  rw [h0] at hpos
  exact FieldK.lt_irrefl_zero_one hpos

private theorem one_le_add_nonneg {a b : K} (ha : O.le FieldK.one a) (hb : O.le FieldK.zero b) :
    O.le FieldK.one (FieldK.add a b) := by
  have h1 := O.add_le_add_left FieldK.zero b a hb
  rw [FieldK.add_zero] at h1
  exact O.le_trans _ _ _ ha h1

private theorem one_le_two : O.le FieldK.one (FieldK.two : K) :=
  one_le_add_nonneg (O.le_refl FieldK.one) O.zero_le_one

private theorem three_ne_zero : (three : K) ≠ FieldK.zero :=
  pos_ne_zero (one_le_add_nonneg one_le_two O.zero_le_one)

private theorem four_ne_zero : (four : K) ≠ FieldK.zero :=
  pos_ne_zero (one_le_add_nonneg one_le_two (FieldK.two_pos.1))

private theorem five_ne_zero : (five : K) ≠ FieldK.zero :=
  pos_ne_zero (one_le_add_nonneg
    (one_le_add_nonneg one_le_two (FieldK.two_pos.1)) O.zero_le_one)

/-! ### 1. Dimension `n = 4`: `(Cl_{4,0}(K)⁺)ˣ` Fails to Preserve `V` -/

private theorem omega2_sq_local :
    let s2 : List K := [FieldK.one, FieldK.one]
    Cl.mul s2 (Cl.omega s2) (Cl.omega s2) = Cl.neg s2 (Cl.one s2) := by
  intro s2
  apply Prod.ext <;> apply Prod.ext <;>
    dsimp [s2, Cl.mul, Cl.omega, Cl.invol, Cl.neg, Cl.one, Cl.zero, Cl.add, Cl.smul] <;>
    simp only [FieldK.zero_mul, FieldK.mul_zero, FieldK.one_mul, FieldK.mul_one,
               FieldK.add_zero, FieldK.zero_add, FieldK.neg_zero, FieldK.neg_neg,
               FieldK.mul_neg, FieldK.neg_mul]

private theorem omega3_sq :
    Cl.mul (sig30 K) (Cl.omega (sig30 K)) (Cl.omega (sig30 K)) =
    Cl.neg (sig30 K) (Cl.one (sig30 K)) := by
  let s2 : List K := [FieldK.one, FieldK.one]
  have h_inv2 : Cl.invol s2 (Cl.omega s2) = Cl.omega s2 := by
    rw [Cl.invol_omega s2]
    dsimp [s2, List.length]
    rfl
  apply Prod.ext
  · change Cl.add s2 (Cl.mul s2 (Cl.zero s2) (Cl.zero s2))
             (Cl.smul FieldK.one s2 (Cl.mul s2 (Cl.omega s2) (Cl.invol s2 (Cl.omega s2)))) =
           Cl.neg s2 (Cl.one s2)
    rw [Cl.zero_mul, h_inv2, omega2_sq_local, Cl.one_smul, Cl.zero_add]
  · change Cl.add s2 (Cl.mul s2 (Cl.zero s2) (Cl.omega s2))
             (Cl.mul s2 (Cl.omega s2) (Cl.invol s2 (Cl.zero s2))) =
           Cl.neg s2 (Cl.zero s2)
    rw [Cl.zero_mul, Cl.invol_zero, Cl.mul_zero, Cl.add_zero, Cl.neg_zero]

private theorem invol_omega3 :
    Cl.invol (sig30 K) (Cl.omega (sig30 K)) = Cl.neg (sig30 K) (Cl.omega (sig30 K)) := by
  rw [Cl.invol_omega (sig30 K)]
  dsimp [sig30, List.length]
  rfl

/-- **Refutation 2A(ii) (`n = 4`, `(Cl_{4,0}(K)⁺)ˣ` fails `x V x⁻¹ ⊆ V`):**
    Over ANY ordered field `K` (including `ℚ` and `ℝ`), `x = 1 + 2 e_{1234}` is an
    invertible element of the even subalgebra `Cl_{4,0}(K)⁺`, yet `Ad_x(e_4) = x e_4 x⁻¹`
    is NOT in the vector subspace `V`. -/
theorem cl40_even_unit_fails_to_preserve_V :
    let s4 := sig40 K
    let s3 := sig30 K
    let x : Cl K s4 := (Cl.one s3, Cl.smul FieldK.two s3 (Cl.omega s3))
    let negInv3 := FieldK.neg (FieldK.inv (three : K))
    let twoThirds := FieldK.mul FieldK.two (FieldK.inv (three : K))
    let x_inv : Cl K s4 := (Cl.smul negInv3 s3 (Cl.one s3), Cl.smul twoThirds s3 (Cl.omega s3))
    let e4Vec : Vec K s4 := (Cl.vecZero s3, FieldK.one)
    Cl.invol s4 x = x ∧
    Cl.invol s4 x_inv = x_inv ∧
    Cl.mul s4 x x_inv = Cl.one s4 ∧
    Cl.mul s4 x_inv x = Cl.one s4 ∧
    ¬ ∃ w : Vec K s4, Cl.mul s4 (Cl.mul s4 x (Cl.embedVec s4 e4Vec)) x_inv = Cl.embedVec s4 w := by
  intro s4 s3 x negInv3 twoThirds x_inv e4Vec
  have h3nz : (three : K) ≠ FieldK.zero := three_ne_zero
  have h_coeff1 : FieldK.add negInv3 (FieldK.mul FieldK.two twoThirds) = FieldK.one := by
    dsimp [negInv3, twoThirds]
    have hn1 : FieldK.neg (FieldK.inv (three : K)) =
               FieldK.mul (FieldK.neg FieldK.one) (FieldK.inv three) :=
      (FieldK.neg_one_mul _).symm
    have h22 : FieldK.mul (FieldK.two : K) FieldK.two = four := by
      dsimp [four]; unfold FieldK.two; rw [FieldK.left_distrib, FieldK.mul_one]
    rw [hn1, ← FieldK.mul_assoc FieldK.two FieldK.two (FieldK.inv three), h22,
        ← FieldK.right_distrib]
    have hsum : FieldK.add (FieldK.neg FieldK.one) (four : K) = three := by
      dsimp [four, three]
      rw [← FieldK.add_assoc (FieldK.neg FieldK.one) FieldK.two FieldK.two]
      have hn12 : FieldK.add (FieldK.neg FieldK.one) (FieldK.two : K) = FieldK.one := by
        unfold FieldK.two
        rw [← FieldK.add_assoc, FieldK.add_left_neg, FieldK.zero_add]
      rw [hn12, FieldK.add_comm FieldK.one FieldK.two]
    rw [hsum, FieldK.mul_right_inv h3nz]
  have h_coeff2 : FieldK.add twoThirds (FieldK.mul FieldK.two negInv3) = FieldK.zero := by
    dsimp [negInv3, twoThirds]
    rw [FieldK.mul_neg, FieldK.add_right_neg]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · apply Prod.ext
    · exact Cl.invol_one s3
    · change Cl.neg s3 (Cl.invol s3 (Cl.smul FieldK.two s3 (Cl.omega s3))) =
             Cl.smul FieldK.two s3 (Cl.omega s3)
      rw [Cl.invol_smul, invol_omega3, Cl.smul_neg, Cl.neg_neg]
  · apply Prod.ext
    · change Cl.invol s3 (Cl.smul negInv3 s3 (Cl.one s3)) = Cl.smul negInv3 s3 (Cl.one s3)
      rw [Cl.invol_smul, Cl.invol_one]
    · change Cl.neg s3 (Cl.invol s3 (Cl.smul twoThirds s3 (Cl.omega s3))) =
             Cl.smul twoThirds s3 (Cl.omega s3)
      rw [Cl.invol_smul, invol_omega3, Cl.smul_neg, Cl.neg_neg]
  · apply Prod.ext
    · change Cl.add s3 (Cl.mul s3 (Cl.one s3) (Cl.smul negInv3 s3 (Cl.one s3)))
               (Cl.smul FieldK.one s3
                 (Cl.mul s3 (Cl.smul FieldK.two s3 (Cl.omega s3))
                   (Cl.invol s3 (Cl.smul twoThirds s3 (Cl.omega s3))))) =
             Cl.one s3
      rw [Cl.one_mul, Cl.one_smul, Cl.invol_smul, invol_omega3,
          Cl.smul_mul_left, Cl.smul_mul_right, Cl.mul_neg, omega3_sq,
          Cl.neg_neg, Cl.smul_smul, ← Cl.add_smul, h_coeff1, Cl.one_smul]
    · change Cl.add s3 (Cl.mul s3 (Cl.one s3) (Cl.smul twoThirds s3 (Cl.omega s3)))
               (Cl.mul s3 (Cl.smul FieldK.two s3 (Cl.omega s3))
                 (Cl.invol s3 (Cl.smul negInv3 s3 (Cl.one s3)))) =
             Cl.zero s3
      rw [Cl.one_mul, Cl.invol_smul, Cl.invol_one, Cl.smul_mul_left, Cl.smul_mul_right,
          Cl.mul_one, Cl.smul_smul, ← Cl.add_smul, h_coeff2, Cl.zero_smul]
  · apply Prod.ext
    · change Cl.add s3 (Cl.mul s3 (Cl.smul negInv3 s3 (Cl.one s3)) (Cl.one s3))
               (Cl.smul FieldK.one s3
                 (Cl.mul s3 (Cl.smul twoThirds s3 (Cl.omega s3))
                   (Cl.invol s3 (Cl.smul FieldK.two s3 (Cl.omega s3))))) =
             Cl.one s3
      rw [Cl.smul_mul_left, Cl.one_mul, Cl.one_smul, Cl.invol_smul, invol_omega3,
          Cl.smul_mul_left, Cl.smul_mul_right, Cl.mul_neg, omega3_sq, Cl.neg_neg,
          Cl.smul_smul, FieldK.mul_comm twoThirds FieldK.two, ← Cl.add_smul, h_coeff1, Cl.one_smul]
    · change Cl.add s3 (Cl.mul s3 (Cl.smul negInv3 s3 (Cl.one s3)) (Cl.smul FieldK.two s3 (Cl.omega s3)))
               (Cl.mul s3 (Cl.smul twoThirds s3 (Cl.omega s3)) (Cl.invol s3 (Cl.one s3))) =
             Cl.zero s3
      rw [Cl.smul_mul_left, Cl.one_mul, Cl.invol_one, Cl.smul_mul_left, Cl.mul_one,
          Cl.smul_smul, FieldK.mul_comm negInv3 FieldK.two, ← Cl.add_smul,
          FieldK.add_comm (FieldK.mul FieldK.two negInv3) twoThirds, h_coeff2, Cl.zero_smul]
  · intro ⟨w, hw⟩
    have he4 : Cl.embedVec s4 e4Vec = Cl.eTop FieldK.one s3 :=
      Cl.embedVec_top FieldK.one s3
    rw [he4] at hw
    have hfst : (Cl.mul s4 (Cl.mul s4 x (Cl.eTop FieldK.one s3)) x_inv).1 =
                Cl.embedVec s3 w.1 := congrArg Prod.fst hw
    change Cl.add s3
             (Cl.mul s3
               (Cl.add s3 (Cl.mul s3 (Cl.one s3) (Cl.zero s3))
                 (Cl.smul FieldK.one s3 (Cl.mul s3 (Cl.smul FieldK.two s3 (Cl.omega s3)) (Cl.invol s3 (Cl.one s3)))))
               (Cl.smul negInv3 s3 (Cl.one s3)))
             (Cl.smul FieldK.one s3
               (Cl.mul s3
                 (Cl.add s3 (Cl.mul s3 (Cl.one s3) (Cl.one s3))
                   (Cl.mul s3 (Cl.smul FieldK.two s3 (Cl.omega s3)) (Cl.invol s3 (Cl.zero s3))))
                 (Cl.invol s3 (Cl.smul twoThirds s3 (Cl.omega s3))))) =
           Cl.embedVec s3 w.1 at hfst
    rw [Cl.mul_zero, Cl.invol_one, Cl.mul_one, Cl.one_smul, Cl.zero_add,
        Cl.one_mul, Cl.invol_zero, Cl.mul_zero, Cl.add_zero,
        Cl.smul_mul_left, Cl.smul_mul_right, Cl.mul_one, Cl.smul_smul,
        Cl.one_smul, Cl.one_mul, Cl.invol_smul, invol_omega3, Cl.smul_neg,
        ← Cl.neg_one_smul s3 (Cl.smul twoThirds s3 (Cl.omega s3)), Cl.smul_smul,
        ← Cl.add_smul] at hfst
    have hleaf := congrArg (fun z : Cl K s3 => z.2.2.2) hfst
    dsimp [s3, sig30, Cl.smul, Cl.omega, Cl.embedVec, Cl.scalar, Cl.zero] at hleaf
    rw [FieldK.mul_one] at hleaf
    have hcoeff_eq : FieldK.add (FieldK.mul FieldK.two negInv3)
                                (FieldK.mul (FieldK.neg FieldK.one) twoThirds) =
                     FieldK.neg (FieldK.mul four (FieldK.inv three)) := by
      dsimp [negInv3, twoThirds, four]
      rw [FieldK.mul_neg, FieldK.neg_one_mul, ← FieldK.neg_add,
          ← FieldK.right_distrib]
    rw [hcoeff_eq] at hleaf
    have h4_inv3_nz : FieldK.mul (four : K) (FieldK.inv three) ≠ FieldK.zero :=
      FieldK.mul_ne_zero four_ne_zero (FieldK.inv_ne_zero h3nz)
    have hneg_zero : FieldK.mul (four : K) (FieldK.inv three) = FieldK.zero := by
      rw [← FieldK.neg_neg (FieldK.mul four (FieldK.inv three)), hleaf, FieldK.neg_zero]
    exact h4_inv3_nz hneg_zero

/-! ### 2. Dimension `n = 6`: Unit-Norm Even Elements `{x ∈ Cl_{6,0}⁺ : x x̃ = 1}` Fail `x V x⁻¹ ⊆ V` -/

private theorem omega5_props :
    Cl.invol (sig50 K) (Cl.omega (sig50 K)) = Cl.neg (sig50 K) (Cl.omega (sig50 K)) ∧
    Cl.rev (sig50 K) (Cl.omega (sig50 K)) = Cl.omega (sig50 K) ∧
    Cl.mul (sig50 K) (Cl.omega (sig50 K)) (Cl.omega (sig50 K)) = Cl.one (sig50 K) := by
  let s4 := sig40 K
  let s3 := sig30 K
  have h_inv4 : Cl.invol s4 (Cl.omega s4) = Cl.omega s4 := by
    rw [Cl.invol_omega s4]
    dsimp [s4, sig40, sig30, List.length]
    rfl
  have h_sq4 : Cl.mul s4 (Cl.omega s4) (Cl.omega s4) = Cl.one s4 := by
    apply Prod.ext
    · change Cl.add s3 (Cl.mul s3 (Cl.zero s3) (Cl.zero s3))
               (Cl.smul FieldK.one s3 (Cl.mul s3 (Cl.omega s3) (Cl.invol s3 (Cl.omega s3)))) =
             Cl.one s3
      rw [Cl.zero_mul, invol_omega3, Cl.mul_neg, omega3_sq, Cl.neg_neg,
          Cl.one_smul, Cl.zero_add]
    · change Cl.add s3 (Cl.mul s3 (Cl.zero s3) (Cl.omega s3))
               (Cl.mul s3 (Cl.omega s3) (Cl.invol s3 (Cl.zero s3))) =
             Cl.zero s3
      rw [Cl.zero_mul, Cl.invol_zero, Cl.mul_zero, Cl.add_zero]
  have h_rev4 : Cl.rev s4 (Cl.omega s4) = Cl.omega s4 := by
    have h_rev3 : Cl.rev s3 (Cl.omega s3) = Cl.neg s3 (Cl.omega s3) := by
      let s2 : List K := [FieldK.one, FieldK.one]
      have h_rev2 : Cl.rev s2 (Cl.omega s2) = Cl.neg s2 (Cl.omega s2) := by
        apply Prod.ext <;> apply Prod.ext <;>
          dsimp [s2, Cl.rev, Cl.omega, Cl.invol, Cl.neg, Cl.zero, Cl.one] <;>
          simp only [FieldK.neg_zero, FieldK.neg_neg]
      apply Prod.ext
      · change Cl.rev s2 (Cl.zero s2) = Cl.neg s2 (Cl.zero s2)
        rw [Cl.rev_zero, Cl.neg_zero]
      · change Cl.invol s2 (Cl.rev s2 (Cl.omega s2)) = Cl.neg s2 (Cl.omega s2)
        rw [h_rev2, Cl.invol_neg, Cl.invol_omega s2]
        dsimp [s2, List.length]
        rfl
    apply Prod.ext
    · exact Cl.rev_zero s3
    · change Cl.invol s3 (Cl.rev s3 (Cl.omega s3)) = Cl.omega s3
      rw [h_rev3, Cl.invol_neg, invol_omega3, Cl.neg_neg]
  refine ⟨by rw [Cl.invol_omega (sig50 K)]; dsimp [sig50, sig40, sig30, List.length]; rfl,
          ?_, ?_⟩
  · apply Prod.ext
    · exact Cl.rev_zero s4
    · change Cl.invol s4 (Cl.rev s4 (Cl.omega s4)) = Cl.omega s4
      rw [h_rev4, h_inv4]
  · apply Prod.ext
    · change Cl.add s4 (Cl.mul s4 (Cl.zero s4) (Cl.zero s4))
               (Cl.smul FieldK.one s4 (Cl.mul s4 (Cl.omega s4) (Cl.invol s4 (Cl.omega s4)))) =
             Cl.one s4
      rw [Cl.zero_mul, h_inv4, h_sq4, Cl.one_smul, Cl.zero_add]
    · change Cl.add s4 (Cl.mul s4 (Cl.zero s4) (Cl.omega s4))
               (Cl.mul s4 (Cl.omega s4) (Cl.invol s4 (Cl.zero s4))) =
             Cl.zero s4
      rw [Cl.zero_mul, Cl.invol_zero, Cl.mul_zero, Cl.add_zero]

/-- **Refutation 2B (`n = 6`, Chevalley–Porteous Unit-Norm Counterexample):**
    Over ANY ordered field `K` (including `ℚ` and `ℝ`), the element
    `x = (3/5) · 1 + (4/5) · e_{123456} ∈ Cl_{6,0}(K)⁺` lies in the even subalgebra and
    has EXACT unit Clifford norm `x * x̃ = 1` and `x̃ * x = 1` (so `x⁻¹ = x̃`), YET
    `Ad_x(e_6) = x e_6 x⁻¹` is NOT in `V ⊂ Cl_{6,0}(K)`. -/
theorem cl60_unit_norm_even_fails_to_preserve_V :
    let s6 := sig60 K
    let s5 := sig50 K
    let c35 := FieldK.mul (three : K) (FieldK.inv (five : K))
    let s45 := FieldK.mul (four : K) (FieldK.inv (five : K))
    let x : Cl K s6 := (Cl.smul c35 s5 (Cl.one s5), Cl.smul s45 s5 (Cl.omega s5))
    let e6Vec : Vec K s6 := (Cl.vecZero s5, FieldK.one)
    Cl.invol s6 x = x ∧
    Cl.mul s6 x (Cl.rev s6 x) = Cl.one s6 ∧
    Cl.mul s6 (Cl.rev s6 x) x = Cl.one s6 ∧
    ¬ ∃ w : Vec K s6,
        Cl.mul s6 (Cl.mul s6 x (Cl.embedVec s6 e6Vec)) (Cl.rev s6 x) = Cl.embedVec s6 w := by
  intro s6 s5 c35 s45 x e6Vec
  obtain ⟨h_inv5, h_rev5, h_sq5⟩ := omega5_props (K := K)
  have h5nz : (five : K) ≠ FieldK.zero := five_ne_zero
  have h_pythag : FieldK.add (FieldK.mul c35 c35) (FieldK.mul s45 s45) = FieldK.one := by
    have h34_eq_55 : FieldK.add (FieldK.mul (three : K) three) (FieldK.mul four four) =
                     FieldK.mul five five := by
      have h55 : FieldK.mul (five : K) five =
                 FieldK.add (FieldK.add (FieldK.add four four) FieldK.one)
                            (FieldK.mul four four) := by
        dsimp [five]
        rw [FieldK.right_distrib, FieldK.left_distrib four, FieldK.left_distrib FieldK.one]
        simp only [FieldK.mul_one, FieldK.one_mul]
        rw [FieldK.add_assoc (FieldK.mul four four) four (FieldK.add four FieldK.one),
            ← FieldK.add_assoc four four FieldK.one,
            FieldK.add_comm (FieldK.mul four four)]
      have h33 : FieldK.mul (three : K) three =
                 FieldK.add (FieldK.add four four) FieldK.one := by
        have h22 : FieldK.mul (FieldK.two : K) FieldK.two = four := by
          dsimp [four]; unfold FieldK.two
          rw [FieldK.left_distrib, FieldK.mul_one]
        dsimp [three]
        rw [FieldK.right_distrib, FieldK.left_distrib FieldK.two, FieldK.left_distrib FieldK.one]
        simp only [FieldK.mul_one, FieldK.one_mul]
        rw [h22]
        dsimp [four]
        rw [FieldK.add_assoc (FieldK.add FieldK.two FieldK.two) FieldK.two (FieldK.add FieldK.two FieldK.one),
            ← FieldK.add_assoc FieldK.two FieldK.two FieldK.one,
            ← FieldK.add_assoc (FieldK.add FieldK.two FieldK.two) (FieldK.add FieldK.two FieldK.two) FieldK.one]
      rw [h55, h33]
    have hsq_factor : ∀ a : K,
        FieldK.mul (FieldK.mul a (FieldK.inv five)) (FieldK.mul a (FieldK.inv five)) =
        FieldK.mul (FieldK.mul a a) (FieldK.mul (FieldK.inv five) (FieldK.inv five)) := fun a => by
      rw [← FieldK.mul_assoc, FieldK.mul_assoc a (FieldK.inv five) a,
          FieldK.mul_comm (FieldK.inv five) a,
          ← FieldK.mul_assoc a a (FieldK.inv five), FieldK.mul_assoc]
    dsimp [c35, s45]
    rw [hsq_factor three, hsq_factor four, ← FieldK.right_distrib, h34_eq_55,
        FieldK.mul_assoc five five _, ← FieldK.mul_assoc five (FieldK.inv five) (FieldK.inv five),
        FieldK.mul_right_inv h5nz, FieldK.one_mul, FieldK.mul_right_inv h5nz]
  have h_rev_x : Cl.rev s6 x = (Cl.smul c35 s5 (Cl.one s5), Cl.neg s5 (Cl.smul s45 s5 (Cl.omega s5))) := by
    apply Prod.ext
    · change Cl.rev s5 (Cl.smul c35 s5 (Cl.one s5)) = Cl.smul c35 s5 (Cl.one s5)
      rw [Cl.rev_smul, Cl.rev_one]
    · change Cl.invol s5 (Cl.rev s5 (Cl.smul s45 s5 (Cl.omega s5))) =
             Cl.neg s5 (Cl.smul s45 s5 (Cl.omega s5))
      rw [Cl.rev_smul, h_rev5, Cl.invol_smul, h_inv5, Cl.smul_neg]
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply Prod.ext
    · change Cl.invol s5 (Cl.smul c35 s5 (Cl.one s5)) = Cl.smul c35 s5 (Cl.one s5)
      rw [Cl.invol_smul, Cl.invol_one]
    · change Cl.neg s5 (Cl.invol s5 (Cl.smul s45 s5 (Cl.omega s5))) = Cl.smul s45 s5 (Cl.omega s5)
      rw [Cl.invol_smul, h_inv5, Cl.smul_neg, Cl.neg_neg]
  · rw [h_rev_x]
    apply Prod.ext
    · change Cl.add s5
               (Cl.mul s5 (Cl.smul c35 s5 (Cl.one s5)) (Cl.smul c35 s5 (Cl.one s5)))
               (Cl.smul FieldK.one s5
                 (Cl.mul s5 (Cl.smul s45 s5 (Cl.omega s5))
                   (Cl.invol s5 (Cl.neg s5 (Cl.smul s45 s5 (Cl.omega s5)))))) =
             Cl.one s5
      rw [Cl.smul_mul_left, Cl.smul_mul_right, Cl.one_mul, Cl.smul_smul,
          Cl.invol_neg, Cl.invol_smul, h_inv5, Cl.smul_neg, Cl.neg_neg,
          Cl.smul_mul_left, Cl.smul_mul_right, h_sq5, Cl.one_smul, Cl.smul_smul,
          ← Cl.add_smul, h_pythag, Cl.one_smul]
    · change Cl.add s5
               (Cl.mul s5 (Cl.smul c35 s5 (Cl.one s5)) (Cl.neg s5 (Cl.smul s45 s5 (Cl.omega s5))))
               (Cl.mul s5 (Cl.smul s45 s5 (Cl.omega s5)) (Cl.invol s5 (Cl.smul c35 s5 (Cl.one s5)))) =
             Cl.zero s5
      rw [Cl.mul_neg, Cl.smul_mul_left, Cl.smul_mul_right, Cl.one_mul, Cl.smul_smul,
          Cl.invol_smul, Cl.invol_one, Cl.smul_mul_left, Cl.smul_mul_right, Cl.mul_one,
          Cl.smul_smul, FieldK.mul_comm s45 c35, Cl.add_left_neg]
  · rw [h_rev_x]
    apply Prod.ext
    · change Cl.add s5
               (Cl.mul s5 (Cl.smul c35 s5 (Cl.one s5)) (Cl.smul c35 s5 (Cl.one s5)))
               (Cl.smul FieldK.one s5
                 (Cl.mul s5 (Cl.neg s5 (Cl.smul s45 s5 (Cl.omega s5)))
                   (Cl.invol s5 (Cl.smul s45 s5 (Cl.omega s5))))) =
             Cl.one s5
      rw [Cl.smul_mul_left, Cl.smul_mul_right, Cl.one_mul, Cl.smul_smul,
          Cl.neg_mul, Cl.invol_smul, h_inv5,
          Cl.smul_mul_left, Cl.smul_mul_right, Cl.mul_neg,
          Cl.smul_neg, Cl.smul_neg, Cl.smul_neg, Cl.smul_neg, Cl.neg_neg,
          h_sq5, Cl.one_smul, Cl.smul_smul,
          ← Cl.add_smul, h_pythag, Cl.one_smul]
    · change Cl.add s5
               (Cl.mul s5 (Cl.smul c35 s5 (Cl.one s5)) (Cl.smul s45 s5 (Cl.omega s5)))
               (Cl.mul s5 (Cl.neg s5 (Cl.smul s45 s5 (Cl.omega s5)))
                 (Cl.invol s5 (Cl.smul c35 s5 (Cl.one s5)))) =
             Cl.zero s5
      rw [Cl.smul_mul_left, Cl.smul_mul_right, Cl.one_mul, Cl.smul_smul,
          Cl.invol_smul, Cl.invol_one, Cl.neg_mul, Cl.smul_mul_left, Cl.smul_mul_right,
          Cl.mul_one, Cl.smul_smul, FieldK.mul_comm s45 c35, Cl.add_right_neg]
  · intro ⟨w, hw⟩
    have he6 : Cl.embedVec s6 e6Vec = Cl.eTop FieldK.one s5 :=
      Cl.embedVec_top FieldK.one s5
    rw [he6, h_rev_x] at hw
    have hfst : (Cl.mul s6 (Cl.mul s6 x (Cl.eTop FieldK.one s5))
                  (Cl.smul c35 s5 (Cl.one s5), Cl.neg s5 (Cl.smul s45 s5 (Cl.omega s5)))).1 =
                Cl.embedVec s5 w.1 := congrArg Prod.fst hw
    change Cl.add s5
             (Cl.mul s5
               (Cl.add s5 (Cl.mul s5 (Cl.smul c35 s5 (Cl.one s5)) (Cl.zero s5))
                 (Cl.smul FieldK.one s5 (Cl.mul s5 (Cl.smul s45 s5 (Cl.omega s5)) (Cl.invol s5 (Cl.one s5)))))
               (Cl.smul c35 s5 (Cl.one s5)))
             (Cl.smul FieldK.one s5
               (Cl.mul s5
                 (Cl.add s5 (Cl.mul s5 (Cl.smul c35 s5 (Cl.one s5)) (Cl.one s5))
                   (Cl.mul s5 (Cl.smul s45 s5 (Cl.omega s5)) (Cl.invol s5 (Cl.zero s5))))
                 (Cl.invol s5 (Cl.neg s5 (Cl.smul s45 s5 (Cl.omega s5)))))) =
           Cl.embedVec s5 w.1 at hfst
    rw [Cl.mul_zero, Cl.invol_one, Cl.mul_one, Cl.one_smul, Cl.zero_add,
        Cl.smul_mul_left, Cl.mul_one, Cl.invol_zero, Cl.mul_zero, Cl.add_zero,
        Cl.smul_mul_left, Cl.smul_mul_right, Cl.mul_one, Cl.smul_smul,
        Cl.one_smul, Cl.invol_neg, Cl.invol_smul, h_inv5, Cl.smul_neg, Cl.neg_neg,
        Cl.one_mul, Cl.smul_smul,
        ← Cl.add_smul] at hfst
    have hleaf := congrArg (fun z : Cl K s5 => z.2.2.2.2.2) hfst
    dsimp [s5, sig50, sig40, sig30, Cl.smul, Cl.omega, Cl.embedVec, Cl.scalar, Cl.zero] at hleaf
    rw [FieldK.mul_one, FieldK.mul_comm s45 c35] at hleaf
    have h2_prod : FieldK.mul FieldK.two (FieldK.mul c35 s45) = FieldK.zero := by
      unfold FieldK.two
      rw [FieldK.right_distrib, FieldK.one_mul]
      exact hleaf
    have hc35_nz : c35 ≠ FieldK.zero :=
      FieldK.mul_ne_zero three_ne_zero (FieldK.inv_ne_zero h5nz)
    have hs45_nz : s45 ≠ FieldK.zero :=
      FieldK.mul_ne_zero four_ne_zero (FieldK.inv_ne_zero h5nz)
    have hnz : FieldK.mul FieldK.two (FieldK.mul c35 s45) ≠ FieldK.zero :=
      FieldK.mul_ne_zero O.two_ne_zero (FieldK.mul_ne_zero hc35_nz hs45_nz)
    exact hnz h2_prod

end HigherDimFailure

/-! ### Concrete Unconditional Instantiations Over `RatQ` (`ℚ`) -/

theorem rat_cl40_even_unit_counterexample :
    ∃ x x_inv : Cl RatQ (sig40 RatQ),
      Cl.invol (sig40 RatQ) x = x ∧
      Cl.invol (sig40 RatQ) x_inv = x_inv ∧
      Cl.mul (sig40 RatQ) x x_inv = Cl.one (sig40 RatQ) ∧
      Cl.mul (sig40 RatQ) x_inv x = Cl.one (sig40 RatQ) ∧
      ∃ v : Vec RatQ (sig40 RatQ),
        ¬ ∃ w : Vec RatQ (sig40 RatQ),
            Cl.mul (sig40 RatQ) (Cl.mul (sig40 RatQ) x (Cl.embedVec (sig40 RatQ) v)) x_inv =
              Cl.embedVec (sig40 RatQ) w := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := cl40_even_unit_fails_to_preserve_V (K := RatQ)
  exact ⟨_, _, h1, h2, h3, h4, (Cl.vecZero (sig30 RatQ), FieldK.one), h5⟩

theorem rat_cl60_chevalley_porteous_counterexample :
    ∃ x : Cl RatQ (sig60 RatQ),
      Cl.invol (sig60 RatQ) x = x ∧
      Cl.mul (sig60 RatQ) x (Cl.rev (sig60 RatQ) x) = Cl.one (sig60 RatQ) ∧
      Cl.mul (sig60 RatQ) (Cl.rev (sig60 RatQ) x) x = Cl.one (sig60 RatQ) ∧
      ∃ v : Vec RatQ (sig60 RatQ),
        ¬ ∃ w : Vec RatQ (sig60 RatQ),
            Cl.mul (sig60 RatQ) (Cl.mul (sig60 RatQ) x (Cl.embedVec (sig60 RatQ) v))
              (Cl.rev (sig60 RatQ) x) = Cl.embedVec (sig60 RatQ) w := by
  obtain ⟨h1, h2, h3, h4⟩ := cl60_unit_norm_even_fails_to_preserve_V (K := RatQ)
  exact ⟨_, h1, h2, h3, (Cl.vecZero (sig50 RatQ), FieldK.one), h4⟩

end Conjecture00000007606
