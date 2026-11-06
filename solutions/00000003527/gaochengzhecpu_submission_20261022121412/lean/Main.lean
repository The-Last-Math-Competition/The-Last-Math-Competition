import Mathlib.SetTheory.Ordinal.FixedPoint
import Mathlib.SetTheory.Ordinal.Topology

/-! The classical fixed-point theorem for normal ordinal functions.
The two omega limits below are deliberately distinguished: the omega-th
fixed-point enumerand, and the least fixed point obtained by iterating f. -/

noncomputable section
universe u

namespace Conjecture3527

open Ordinal Function Set

variable (f : Ordinal.{u} → Ordinal.{u})

theorem fixed_points_closed (hf : IsNormal f) : IsClosed (fixedPoints f) := by
  have hc : Continuous f := (Ordinal.isNormal_iff_strictMono_and_continuous f).mp hf |>.2
  exact isClosed_eq hc continuous_id

theorem fixed_points_unbounded (hf : IsNormal f) : ¬ BddAbove (fixedPoints f) :=
  Ordinal.not_bddAbove_fp hf

theorem arbitrarily_large_fixed_point (hf : IsNormal f) (a : Ordinal.{u}) :
    ∃ b, a < b ∧ f b = b := by
  refine ⟨nfp f (Order.succ a), ?_, hf.nfp_fp _⟩
  exact (Order.lt_succ a).trans_le (Ordinal.le_nfp f _)

theorem enumeration_range (hf : IsNormal f) : Set.range (Ordinal.deriv f) = fixedPoints f := by
  ext a
  change (∃ b, Ordinal.deriv f b = a) ↔ f a = a
  exact hf.fp_iff_deriv.symm

theorem enumeration_normal : IsNormal (Ordinal.deriv f) := Ordinal.isNormal_deriv f

theorem enumeration_zero : Ordinal.deriv f 0 = nfp f 0 := Ordinal.deriv_zero_right f

theorem enumeration_successor (a : Ordinal.{u}) :
    Ordinal.deriv f (Order.succ a) = nfp f (Order.succ (Ordinal.deriv f a)) :=
  Ordinal.deriv_succ f a

theorem enumeration_limit {a : Ordinal.{u}} (ha : Order.IsSuccLimit a) :
    Ordinal.deriv f a = ⨆ b : Set.Iio a, Ordinal.deriv f b := by
  exact Ordinal.deriv_limit f ha

theorem enumeration_omega :
    Ordinal.deriv f ω = ⨆ n : ℕ, Ordinal.deriv f (n : Ordinal.{u}) :=
  (Ordinal.isNormal_deriv f).apply_omega0.symm

theorem iterate_omega (a : Ordinal.{u}) :
    nfp f a = ⨆ n : ℕ, (f^[n]) a :=
  (Ordinal.iSup_iterate_eq_nfp f a).symm

theorem least_fixed_point (hf : IsNormal f) (a : Ordinal.{u}) :
    a ≤ nfp f a ∧ f (nfp f a) = nfp f a ∧
    ∀ b, a ≤ b → f b = b → nfp f a ≤ b := by
  refine ⟨Ordinal.le_nfp f a, hf.nfp_fp a, ?_⟩
  intro b hab hb
  exact Ordinal.nfp_le_fp hf.monotone hab hb.le

/-- The two omega constructions must not be identified: already for identity,
the derivative's omega-th enumerand is omega, while iteration from zero stays zero. -/
theorem identity_limits :
    Ordinal.deriv (id : Ordinal.{u} → Ordinal.{u}) ω = ω ∧
      nfp (id : Ordinal.{u} → Ordinal.{u}) 0 = 0 := by
  constructor
  · rw [Ordinal.deriv_id_of_nfp_id Ordinal.nfp_id]
    rfl
  · rw [Ordinal.nfp_id]
    rfl

/-- Full universal statement, with the fixed-point enumeration and ordinary
iteration limits separately specified. Closed means genuinely order-topologically closed. -/
def FixedPointClaim : Prop :=
  ∀ f : Ordinal.{u} → Ordinal.{u}, IsNormal f →
    IsClosed (fixedPoints f) ∧ ¬ BddAbove (fixedPoints f) ∧
    Set.range (Ordinal.deriv f) = fixedPoints f ∧ IsNormal (Ordinal.deriv f) ∧
    Ordinal.deriv f 0 = nfp f 0 ∧
    (∀ a, Ordinal.deriv f (Order.succ a) = nfp f (Order.succ (Ordinal.deriv f a))) ∧
    (∀ a, Order.IsSuccLimit a → Ordinal.deriv f a = ⨆ b : Set.Iio a, Ordinal.deriv f b) ∧
    Ordinal.deriv f ω = (⨆ n : ℕ, Ordinal.deriv f (n : Ordinal.{u})) ∧
    ∀ a, nfp f a = (⨆ n : ℕ, (f^[n]) a) ∧ a ≤ nfp f a ∧
      f (nfp f a) = nfp f a ∧ (∀ b, a ≤ b → f b = b → nfp f a ≤ b)

theorem conjecture_3527_true : FixedPointClaim.{u} := by
  intro f hf
  refine ⟨fixed_points_closed f hf, fixed_points_unbounded f hf,
    enumeration_range f hf, enumeration_normal f, enumeration_zero f,
    enumeration_successor f, ?_, enumeration_omega f, ?_⟩
  · intro a ha
    exact enumeration_limit f ha
  · intro a
    exact ⟨iterate_omega f a, least_fixed_point f hf a⟩

#print axioms conjecture_3527_true
#print axioms fixed_points_closed
#print axioms enumeration_range
#print axioms enumeration_omega
#print axioms least_fixed_point
#print axioms identity_limits

end Conjecture3527
