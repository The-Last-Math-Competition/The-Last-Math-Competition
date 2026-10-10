import Mathlib

/-! Formal statement for Conjecture781: definitions only, ending in `Claim`. Split verbatim from the marked block of `Basic.lean`. -/

-- STATEMENT BEGIN
namespace C781

/-- "`1 + pℤ_p`": the units `u` of `ℤ_p` with `u - 1 ∈ pℤ_p`, as a subgroup of `ℤ_p^×`. -/
def U1 (p : ℕ) [Fact p.Prime] : Subgroup ℤ_[p]ˣ where
  carrier := {u | (p : ℤ_[p]) ∣ (u : ℤ_[p]) - 1}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Units.val_mul] at *
    have : (a : ℤ_[p]) * b - 1 = a * (b - 1) + (a - 1) := by ring
    rw [this]; exact dvd_add (dvd_mul_of_dvd_right hb _) ha
  one_mem' := by simp
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    have : ((a⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) - 1 = -(((a⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * ((a : ℤ_[p]) - 1)) := by
      linear_combination (1 : ℤ_[p]) * a.inv_mul
    rw [this]; exact (dvd_mul_of_dvd_right ha _).neg_right

/-- "quotient lattice of the integers": a lattice that is a surjective lattice-homomorphic image of
the chain `(ℤ, ≤)`, of the subgroup lattice of `ℤ` (the ideal lattice, i.e. the divisibility lattice
reversed), of its order dual (the divisibility lattice), or the subgroup lattice of `ℤ/nℤ`. -/
def QuotientLatticeOfInt (L : Type) [Lattice L] : Prop :=
  (∃ f : LatticeHom ℤ L, Function.Surjective f) ∨
  (∃ f : LatticeHom (AddSubgroup ℤ) L, Function.Surjective f) ∨
  (∃ f : LatticeHom (AddSubgroup ℤ)ᵒᵈ L, Function.Surjective f) ∨
  (∃ n : ℕ, Nonempty (AddSubgroup (ZMod n) ≃o L))

/-- "This subgroup lattice [of closed subgroups of `1 + pℤ_p`] is isomorphic to a quotient lattice of
the integers" (a lattice isomorphism is an order isomorphism). -/
def Conjecture (p : ℕ) [Fact p.Prime] : Prop :=
  ∃ (L : Type) (_ : Lattice L), QuotientLatticeOfInt L ∧ Nonempty (ClosedSubgroup (U1 p) ≃o L)

/-- The conjecture, for all primes `p`, fails (at `p = 2`). -/
def Claim : Prop := ¬ ∀ (p : ℕ) [Fact p.Prime], Conjecture p

end C781
-- STATEMENT END
