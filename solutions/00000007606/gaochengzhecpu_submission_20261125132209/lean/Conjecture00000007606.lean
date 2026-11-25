/-
  Conjecture 00000007606 — Complete Formal Resolution in Core Lean 4.19.0

  Summary of Main Formalized Results:
  ===================================
  A. POSITIVE CLASSICAL THEOREMS (Repaired Double Cover `Spin(V, Q) → SO(V, Q)`):
     1. `Cl.adjoint_preserves_quadForm` — Universal Adjoint Orthogonality (`Q(Ad_x v) = Q(v)`
        for ALL dimensions `n` and signatures).
     2. `Cl.spin_adjoint_kernel_eq_pm_one` — Universal Spin Kernel-Two Theorem: for ALL
        dimensions `n ≥ 0` and ALL nondegenerate signatures over any field of `char ≠ 2`,
        `ker(Ad : Spin(V, Q) → SO(V, Q)) = {+1, -1}` of exact cardinality `2` (`+1 ≠ -1`).
     3. `spin1_double_cover_and_pin1_twisted_adjoint` — Complete `Spin(1, K) ↠ SO(1, K)`
        kernel-2 surjection and comparison with twisted `Pin(1, K) ↠ O(1, K)`.
     4. `spin2_euclidean_double_cover_over_SO2` — Full classical double cover
        `Spin(2, E) ↠ SO(2, E)` over any Euclidean ordered field `E` (such as `ℝ`):
        surjective onto `SO(2, E)`, kernel `{+1, -1}` of cardinality `2`, exact 2-element
        fibers, plus concrete non-vacuity (`ratPythagRotor_isSpin_and_nontrivial`,
        `rat_rot90_not_in_spin2_image`, `qsqrt2_rot90_lifts_to_spin2`).

  B. COMPLETE REFUTATIONS OF THE STATED CONJECTURE & DEFINITION:
     1. Target Group Error (`O(V, Q)` vs `SO(V, Q)`):
        - `Cl.even_unit_never_covers_orthogonal_reflection` — For ALL dimensions `n ≥ 1`
          and ALL fields of `char ≠ 2`, NO invertible even element in `(Cl⁺)ˣ` (hence no
          element of `Spin`) ever covers the reflection `reflTop ∈ O(V, Q)` via `Ad`.
        - `Cl.odd_dim_no_clifford_unit_covers_reflection` — For ALL odd dimensions
          `n = 2m + 1 ≥ 1`, NOT EVEN `(Cl)ˣ` or `Pin` can cover `reflTop ∈ O(V, Q)` via
          the ordinary adjoint `Ad` (requiring the twisted adjoint `α(x) v x⁻¹`).
     2. Rotor Definition Error ("unit elements of the even subalgebra"):
        - `rat_even_units_infinite_kernel` — In `(Cl_{2,0}(ℚ)⁺)ˣ`, the kernel of `Ad` is
          infinite (`ℕ⁺ ↪ ker(Ad)` via nonzero scalar units `Kˣ · 1`), NOT of size `2`.
        - `cl40_even_unit_fails_to_preserve_V` & `rat_cl40_even_unit_counterexample` — In
          dimension `n = 4`, `x = 1 + 2 e_{1234} ∈ (Cl_{4,0}⁺)ˣ` fails `Ad_x(V) ⊆ V`.
        - `cl60_unit_norm_even_fails_to_preserve_V` & `rat_cl60_chevalley_porteous_counterexample` —
          In dimension `n = 6` (Chevalley–Porteous), even restricting to unit Clifford norm
          `x x̃ = x̃ x = 1` in `Cl_{6,0}⁺`, `x = 3/5 + (4/5) e_{123456}` fails `Ad_x(V) ⊆ V`.
     3. Boundary & Signature Failures:
        - `char_two_kernel_size_one` — Over `𝔽₂` (`char = 2`), `+1 = -1` and the kernel
          has cardinality `1 ≠ 2`.
        - `cl11_unit_norm_even_misses_neg_id_in_SO11` & `rat_cl11_unit_norm_misses_SO11` —
          In Lorentzian signature `(1, 1)`, `{x ∈ Cl_{1,1}⁺ : x x̃ = 1} = Spin⁺(1, 1)`
          misses `-I_2 ∈ SO(1, 1)` as well as reflections in `O(1, 1) \ SO(1, 1)`.
-/

import Conjecture00000007606.Field
import Conjecture00000007606.Clifford
import Conjecture00000007606.LowDimCovers
import Conjecture00000007606.HigherDimCounterexamples

namespace Conjecture00000007606

/-- Concrete rational instantiation of the Lorentzian `(1, 1)` component obstruction. -/
theorem rat_cl11_unit_norm_misses_SO11 :
    let s11 := sig11 RatQ
    let negIdVec : Vec RatQ s11 → Vec RatQ s11 := fun v => (((), FieldK.neg v.1.2), FieldK.neg v.2)
    (∀ v : Vec RatQ s11, Cl.quadForm s11 (negIdVec v) = Cl.quadForm s11 v) ∧
    ¬ ∃ x : Cl RatQ s11,
        Cl.invol s11 x = x ∧
        Cl.mul s11 x (Cl.rev s11 x) = Cl.one s11 ∧
        ∀ v : Vec RatQ s11,
          Cl.mul s11 (Cl.mul s11 x (Cl.embedVec s11 v)) (Cl.rev s11 x) =
            Cl.embedVec s11 (negIdVec v) :=
  cl11_unit_norm_even_misses_neg_id_in_SO11 (K := RatQ)

/-- Concrete rational instantiation of the universal `n ≥ 1` reflection obstruction
    (for every `n ≥ 1`, `Spin_n(ℚ)` and `(Cl_{n,0}(ℚ)⁺)ˣ` fail to cover `O_n(ℚ)`). -/
theorem rat_euclidean_even_units_never_cover_O_n (n : Nat)
    {x x_inv : Cl RatQ (FieldK.one :: List.replicate n (FieldK.one : RatQ))}
    (heven : Cl.invol (FieldK.one :: List.replicate n FieldK.one) x = x)
    (hx_r : Cl.mul (FieldK.one :: List.replicate n FieldK.one) x x_inv =
            Cl.one (FieldK.one :: List.replicate n FieldK.one))
    (hx_l : Cl.mul (FieldK.one :: List.replicate n FieldK.one) x_inv x =
            Cl.one (FieldK.one :: List.replicate n FieldK.one)) :
    ¬ (∀ v : Vec RatQ (FieldK.one :: List.replicate n FieldK.one),
        Cl.mul _ (Cl.mul _ x (Cl.embedVec _ v)) x_inv =
          Cl.embedVec _ (Cl.reflTop FieldK.one (List.replicate n FieldK.one) v)) :=
  Cl.even_unit_never_covers_orthogonal_reflection FieldK.one (List.replicate n FieldK.one)
    heven hx_r hx_l

end Conjecture00000007606
