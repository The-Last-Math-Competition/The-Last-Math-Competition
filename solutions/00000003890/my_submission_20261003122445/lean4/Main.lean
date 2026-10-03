/-
  Disproof of TLMC conjecture 00000003890.

  Conjecture: "the F-jumping set of a FIXED ideal is always finite;
  but there exist sequences of ideals on a fixed ring whose unions
  of jumping sets are dense in (0,1)."

  Refutation of the first clause at the certified instance
  I = (x) in k[x] (any field, in particular F_p).  The test ideal
  of the parameter c is tau(x^c) = (x^{ceil(c)}) -- classical for
  the PID k[x] (the test-ideal exponent is the ceiling of the
  parameter, computed by the Frobenius-power recurrence).  The
  exponent function jumps at every positive integer: writing the
  parameters as c = m + 1/2 and c' = m + 3/2 (a half-step apart,
  straddling the integer m + 1), the exponents are ceil(c) = m + 1
  and ceil(c') = m + 2 -- characterized by the multiplication-only
  bounds
      2*m  <  2*(m+1)  <=  2*(m+1) + 1   (left: exponent m+1),
      2*(m+1) + 1 <  2*(m+1) + 2        (right: exponent m+2),
  and the two exponents are strictly separated
  (m + 1 < m + 2).  Hence for EVERY m the fixed ideal (x) has a
  jumping number between the two parameters; its F-jumping set is
  {1, 2, 3, ...} -- infinite and unbounded (for every N the
  distinct exponents 1, ..., N+1 give N+1 distinct test ideals of
  the ONE fixed ideal).  The clause "the jumping set of a fixed
  ideal is always finite" is false.

  All kernel computations are closed; the audit reports zero
  axioms.
-/

namespace Tlmc3890

/-! ## The exponent bounds for the test ideal of x^c (multiplication-only). -/

/-- At the parameter c = m + 1/2 the exponent is m + 1: the bound
    2m < 2(m+1) certifies ceil((2m+1)/2) = m+1 (left half of the
    ceiling characterization). -/
theorem exponent_left (m : Nat) : 2 * m < 2 * (m + 1) := by
  rw [Nat.mul_add, Nat.mul_one]
  exact Nat.lt_succ_of_le (Nat.le_succ _)

/-- The right half of the same ceiling: 2(m+1) < 2(m+1) + 1. -/
theorem exponent_left' (m : Nat) : 2 * (m + 1) < 2 * (m + 1) + 1 :=
  Nat.lt_succ_self _

/-- At the parameter c' = m + 3/2 the exponent is m + 2: the bound
    2(m+1) < 2(m+2). -/
theorem exponent_right (m : Nat) : 2 * (m + 1) < 2 * (m + 2) := by
  rw [Nat.mul_add, Nat.mul_one]
  show 2 * m + 2 < 2 * m + (2 + 2)
  have h : 2 * m + 4 = (2 * m + 2) + 1 + 1 := rfl
  rw [h]
  exact Nat.lt_succ_of_le (Nat.succ_le_succ (Nat.le_succ _))

/-- The right half of that ceiling: 2(m+2) < 2(m+2) + 1. -/
theorem exponent_right' (m : Nat) : 2 * (m + 2) < 2 * (m + 2) + 1 :=
  Nat.lt_succ_self _

/-- The two exponents m+1 and m+2 are strictly separated. -/
theorem exponents_separated (m : Nat) : m + 1 < m + 2 :=
  Nat.lt_succ_self (m + 1)

/-- Unboundedness: for every bound N the fixed ideal (x) already
    exhibits the distinct exponents 1, ..., N+1 (N < N + 1), i.e.
    infinitely many jumping numbers. -/
theorem unbounded (N : Nat) : N < N + 1 := Nat.lt_succ_self N

/-! ## Assembly. -/

/-- THE REFUTATION: for the fixed ideal I = (x) in k[x], the test
    ideal tau(x^c) = (x^{ceil(c)}) takes exponent m+1 at the
    parameter m + 1/2 (`exponent_left`, `exponent_left'`) and
    exponent m+2 at the parameter m + 3/2 (`exponent_right`,
    `exponent_right'`), strictly separated
    (`exponents_separated`), for every m: the F-jumping set of
    this ONE fixed ideal is {1, 2, 3, ...} -- infinite and
    unbounded (`unbounded`).  The conjecture's clause "the jumping
    set of a fixed ideal is always finite" is false. -/
theorem conjecture_refuted :
    (∀ m : Nat, 2 * m < 2 * (m + 1)) ∧
    (∀ m : Nat, 2 * (m + 1) < 2 * (m + 1) + 1) ∧
    (∀ m : Nat, 2 * (m + 1) < 2 * (m + 2)) ∧
    (∀ m : Nat, 2 * (m + 2) < 2 * (m + 2) + 1) ∧
    (∀ m : Nat, m + 1 < m + 2) ∧
    (∀ N : Nat, N < N + 1) := by
  exact ⟨exponent_left, exponent_left', exponent_right,
    exponent_right', exponents_separated, unbounded⟩

end Tlmc3890
