import Base
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace TLMC1043
/-- The usual elementary definition of primality. -/
def PrimeNat (p : Nat) : Prop := 2 ≤ p ∧ ∀ d : Nat, d ∣ p → d = 1 ∨ d = p

theorem eleven_prime : PrimeNat 11 := by
  constructor
  · decide
  · intro d hd
    have hb : d ≤ 11 := Nat.le_of_dvd (by decide) hd
    have hc : d=0 ∨ d=1 ∨ d=2 ∨ d=3 ∨ d=4 ∨ d=5 ∨ d=6 ∨ d=7 ∨ d=8 ∨ d=9 ∨ d=10 ∨ d=11 := by omega
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all

/-- All arithmetic is the standard core Lean residue arithmetic on Fin 11. -/
theorem reciprocal_law : ∀ x : F, x ≠ 0 → x * inv x = 1 := by decide
theorem inverse_zero : inv 0 = 0 := rfl

/-- An explicit polynomial, avoiding reliance on an unformalized interpolation theorem. -/
def witnessPolynomial (x : F) : F :=
  x - (x-7)^10 + (x-8)^10 - (x-9)^10 + (x-10)^10

theorem polynomial_represents_witness : ∀ x : F, witnessPolynomial x = witness x := by decide
end TLMC1043
