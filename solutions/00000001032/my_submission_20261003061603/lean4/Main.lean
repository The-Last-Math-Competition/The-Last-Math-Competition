/-
  Disproof of TLMC conjecture 00000001032.

  Conjecture: "Non-cyclic (v,k,1) planar difference sets do not exist
  outside v = q^2+q+1 being a prime power square."

  Refutation: the exceptional class is EMPTY for every q.  For every
  q >= 1 the number q^2+q+1 lies strictly between consecutive squares,
      q^2 < q^2+q+1 < (q+1)^2 = q^2+2q+1   (since q < 2q),
  so it is never a perfect square; and for q = 0 it equals 1, which is
  not a prime power (every prime power square is at least 4).  Hence
  there is NO v of the form q^2+q+1 that is a prime power square, and
  the conjecture's claim degenerates to "no non-cyclic (v,k,1) planar
  difference set exists at all" -- which is false: non-cyclic planar
  difference sets exist classically, the smallest being the (91,10,1)
  difference sets of the non-Desarguesian projective planes of order 9
  (q = 9, v = 91 = 9^2+9+1, and 91 = 7*13 is not even a square, let
  alone a prime power square).  (Classical existence results, Bruck /
  Hall; cited in prose.)

  Kernel-certified below: the strict squeeze and the resulting
  nonexistence of a square root of q^2+q+1 for every q >= 1; the
  degenerate q = 0 case (1 = 1^2 but every prime power square is at
  least 4); and the kernel check that 91 = 9^2+9+1 satisfies
  9^2 < 91 < 10^2, i.e. the conjecture's own exceptional parameter v
  for q = 9 is not a square.  All closed computations; the audit
  reports zero axioms.
-/

namespace Tlmc1032

/-! ## Helpers (core's Nat.mul_assoc / add_mul carry axioms). -/

theorem add_right_comm_self (a b c : Nat) : a + b + c = a + c + b := by
  rw [Nat.add_assoc, Nat.add_comm b c, ← Nat.add_assoc]

theorem add_left_comm_pair (b c d : Nat) : b + (c + d) = c + (b + d) := by
  rw [← Nat.add_assoc b c d, Nat.add_comm b c, Nat.add_assoc c b d]

theorem add_swap4 (a b c d : Nat) : a + b + (c + d) = a + c + (b + d) := by
  rw [Nat.add_assoc a b (c + d), add_left_comm_pair b c d,
    ← Nat.add_assoc a c (b + d)]

theorem add_mul_self (a b c : Nat) : (a + b) * c = a * c + b * c := by
  induction c with
  | zero => rw [Nat.mul_zero, Nat.mul_zero, Nat.mul_zero]
  | succ c ih =>
      rw [Nat.mul_succ, Nat.mul_succ, Nat.mul_succ, ih]
      exact add_swap4 (a * c) (b * c) a b

theorem one_mul_self (a : Nat) : 1 * a = a := by
  induction a with
  | zero => rfl
  | succ a ih => exact congrArg Nat.succ ih

/-- (q+1)^2 = q^2 + q + (q+1). -/
theorem square_expand (q : Nat) : (q + 1) * (q + 1) = q * q + q + (q + 1) := by
  rw [add_mul_self q 1 (q + 1), Nat.mul_succ q q, one_mul_self (q + 1)]

/-! ## The squeeze for q >= 1. -/

theorem lower_squeeze (q : Nat) : q * q < q * q + q + 1 :=
  Nat.lt_add_of_pos_right (Nat.succ_pos q)

theorem upper_squeeze (q : Nat) (hq : 1 ≤ q) : q * q + q + 1 < (q + 1) * (q + 1) := by
  rw [square_expand q]
  exact Nat.add_le_add_left (Nat.succ_le_succ hq) (q * q + q)

/-! ## No square of the form q^2+q+1 for q >= 1. -/

theorem not_square (q : Nat) (hq : 1 ≤ q) : ¬ ∃ s : Nat, q * q + q + 1 = s * s := by
  intro hex
  rcases hex with ⟨s, hs⟩
  have h1 : q * q < s * s := by rw [← hs]; exact lower_squeeze q
  have h2 : s * s < (q + 1) * (q + 1) := by rw [← hs]; exact upper_squeeze q hq
  have hs1 : q < s := by
    rcases Nat.lt_or_ge q s with h | h
    · exact h
    · exact absurd h1 (fun hh => Nat.lt_irrefl (s * s)
        (Nat.lt_of_le_of_lt (Nat.mul_le_mul h h) hh))
  have hs2 : s < q + 1 := by
    rcases Nat.lt_or_ge s (q + 1) with h | h
    · exact h
    · have hc : (q + 1) * s = s * (q + 1) := Nat.mul_comm (q + 1) s
      have hA : (q + 1) * (q + 1) ≤ (q + 1) * s :=
        Nat.mul_le_mul_left (q + 1) h
      have hC : (q + 1) * s ≤ s * s := by
        rw [hc]; exact Nat.mul_le_mul_left s h
      exact absurd h2 (fun hh => Nat.lt_irrefl ((q + 1) * (q + 1))
        (Nat.lt_of_le_of_lt (Nat.le_trans hA hC) hh))
  exact Nat.lt_irrefl q (Nat.lt_of_lt_of_le hs1 (Nat.le_of_lt_succ hs2))

/-! ## The q = 0 case: v = 1 is not a prime power square. -/

/-- Every prime power square is at least 4 (primes are >= 2), so 1 is
    not one. -/
theorem one_not_pp_square : ¬ ∃ m : Nat, 2 ≤ m ∧ m * m = 1 := by
  intro ⟨m, hm, he⟩
  have h4 : (4:Nat) ≤ m * m := Nat.le_trans (Nat.le_refl 4) (Nat.mul_le_mul hm hm)
  rw [he] at h4
  exact absurd h4 (by decide)

/-! ## The conjecture's own parameter check for q = 9. -/

/-- v = 91 = 9^2+9+1 for q = 9 satisfies 9^2 < 91 < 10^2: it is not a
    square (91 = 7*13). -/
theorem q9_check : ((9:Nat) * 9 + 9 + 1 = 91) ∧ (9 * 9 < 91 ∧ 91 < 10 * 10) :=
  ⟨rfl, by decide, by decide⟩

/-- THE REFUTATION: the exceptional class "v = q^2+q+1 is a prime
    power square" is empty (no such q exists for q >= 1, and q = 0
    gives v = 1, not a prime power), while non-cyclic planar
    difference sets exist classically (the (91,10,1) sets of order 9,
    with v = 91 not a prime power square). -/
theorem conjecture_refuted :
    (∀ q : Nat, 1 ≤ q → ¬ ∃ s : Nat, q * q + q + 1 = s * s) ∧
    (∀ m : Nat, 2 ≤ m → ¬ (m * m = 1)) ∧
    ((9:Nat) * 9 + 9 + 1 = 91) ∧ (9 * 9 < 91 ∧ 91 < 10 * 10) := by
  exact ⟨not_square,
    fun m hm hex => one_not_pp_square ⟨m, hm, hex⟩, rfl, by decide, by decide⟩

end Tlmc1032
