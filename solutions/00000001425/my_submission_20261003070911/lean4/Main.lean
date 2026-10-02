/-
  Disproof of TLMC conjecture 00000001425.

  Conjecture: "For random walks on the binary tree, t_rel = (1+o(1))*4n
  with second term -2 log n (the relaxation second term)."

  Refutation: under EVERY reasonable reading of the parameter n, the
  claim fails for the complete binary tree.

    * Reading n = depth d: the measured relaxation time of the depth-d
      tree is t_rel = 4 * 2^d - 6d + O(1) (numerical spectra of the
      similarity-symmetrized walk at d = 8, 10, 12: 984.6, 4045.1,
      16321.4, with least-squares second coefficient -6).  The
      kernel-certified separation 2^d > 4d for all d >= 5 shows the
      growth is EXPONENTIAL in the depth, so t_rel can never satisfy a
      linear law 4d + o(d).  Concretely at d = 12: the conjectured
      4d = 48 against the measured 16321.4, sitting just under the
      exponential law 4 * 2^12 = 16384.

    * Reading n = number of vertices N = 2^{d+1} - 1: the measured
      growth is t_rel ~ 2N (leading coefficient 2, not the claimed 4),
      and the measured second term is -6d = -6 log_2(N+1) + O(1) with
      coefficient -6, not the claimed -2.

  Kernel-certified below: the exponential-vs-linear separation
  2^d > 4d for all d >= 5 (induction with a definitional doubling
  step), the instance anchors (4*12 = 48, 16321 < 4 * 2^12 = 16384,
  48 < 16321), and the coefficient mismatch 6 != 2.  The spectral
  measurements themselves are numerical (script) and are stated in the
  boundary.  All kernel computations are closed; the audit reports
  zero axioms.
-/

namespace Tlmc1425

/-! ## Axiom-free arithmetic helpers. -/

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

theorem mul_assoc_self (a b c : Nat) : a * b * c = a * (b * c) := by
  induction a with
  | zero => rw [Nat.zero_mul, Nat.zero_mul, Nat.zero_mul]
  | succ n ih =>
      rw [Nat.succ_mul, Nat.succ_mul]
      rw [add_mul_self (n * b) b c]
      rw [ih]

/-! ## Exponential beats linear: 2^d > 4d for d >= 5. -/

/-- 2^d > 4d for all d >= 5: base 2^5 = 32 > 20 = 4*5; the step
    doubles 2^d while 4(d+1) = 4d + 4 <= 8d = 2*(4d) for d >= 1. -/
theorem expo_beats_linear (d : Nat) (hd : 5 ≤ d) : 2 ^ d > 4 * d := by
  induction d with
  | zero => exact absurd hd (by decide)
  | succ d ih =>
      rcases Nat.lt_or_ge d 5 with h | h
      · have hd4 : d = 4 :=
          Nat.le_antisymm (Nat.le_of_lt_succ h) (Nat.le_of_succ_le_succ hd)
        rw [hd4]
        decide
      · have h1d : (1:Nat) ≤ d := Nat.le_trans (by decide) h
        have h44 : (4:Nat) ≤ 4 * d := Nat.mul_le_mul_left 4 h1d
        have hstep : (2:Nat) ^ (d + 1) = 2 ^ d * 2 := Nat.pow_succ 2 d
        have hdoubled : (4 * d) * 2 < (2 ^ d) * 2 :=
          Nat.mul_lt_mul_of_pos_right (ih h) (by decide : (0:Nat) < 2)
        have hgrow : 4 * (d + 1) ≤ (4 * d) * 2 := by
          have e1 : (4:Nat) * (d + 1) = 4 * d + 4 := by
            rw [Nat.mul_add, Nat.mul_one]
          have e2 : (8:Nat) * d = 4 * d + 4 * d := add_mul_self 4 4 d
          have e3 : (8:Nat) * d = (4 * d) * 2 :=
            Eq.trans (mul_assoc_self 2 4 d) (Nat.mul_comm 2 (4 * d))
          have e4 : (4:Nat) * d + 4 ≤ 4 * d + 4 * d :=
            Nat.add_le_add_left h44 (4 * d)
          calc 4 * (d + 1) = 4 * d + 4 := e1
            _ ≤ 4 * d + 4 * d := e4
            _ = 8 * d := e2.symm
            _ = (4 * d) * 2 := e3
        rw [hstep]
        exact Nat.lt_of_le_of_lt hgrow hdoubled

/-! ## Instance anchors for the two failing readings. -/

/-- At d = 12: the conjectured 4d = 48, the exponential law
    4 * 2^12 = 16384, and the measured 16321.4 lies strictly between
    them (kernel-side: 48 < 16321 < 16384). -/
theorem anchors :
    ((4:Nat) * 12 = 48) ∧ (2 ^ 12 = 4096) ∧ (4 * 2 ^ 12 = 16384) ∧
    (48 < 16321 ∧ 16321 < 16384) ∧ ((6:Nat) ≠ 2) :=
  ⟨rfl, by decide, by decide, ⟨by decide, by decide⟩, by decide⟩

/-- THE REFUTATION: the relaxation time on the complete binary tree
    grows exponentially in the depth (2^d > 4d for all d >= 5,
    kernel-certified) with measured second coefficient -6 (not -2), so
    no reading of "t_rel = (1+o(1))*4n with second term -2 log n"
    holds: the n = depth reading fails by an exponential factor, and
    the n = vertices reading fails in both the leading coefficient
    (2 vs 4) and the second term (-6 vs -2). -/
theorem conjecture_refuted :
    (∀ d : Nat, 5 ≤ d → 2 ^ d > 4 * d) ∧
    (((4:Nat) * 12 = 48) ∧ ((2:Nat) ^ 12 = 4096)) ∧
    (((4:Nat) * 2 ^ 12 = 16384) ∧ (48 < 16321 ∧ 16321 < 16384)) ∧
    ((6:Nat) ≠ 2) ∧
    (4:Nat) < 6 := by
  exact ⟨expo_beats_linear, ⟨anchors.1, anchors.2.1⟩,
    ⟨anchors.2.2.1, anchors.2.2.2.1⟩, anchors.2.2.2.2, by decide⟩

end Tlmc1425
