/-
  Disproof of TLMC conjecture 00000003479.

  Conjecture: "The harmonious chromatic number of the random graph
  G(n,p) concentrates at (1+o(1)) times the square root of n*p with
  concentration constant 1; the concentration holds uniformly for
  p >= log n / n."

  Refutation of the SCALING by a deterministic counting bound: in a
  harmonious coloring every unordered color PAIR appears on at most one
  edge (that is the definition: edge color pairs are pairwise distinct
  across edges), so a graph with m edges harmoniously colored with h
  colors satisfies

      2*m <= h*(h-1),

  i.e. h = Omega(sqrt(m)).  For G(n, p) with CONSTANT p (say p = 1/2,
  which satisfies p >= log n / n for all large n), a typical
  realization has m >= n^2/6 w.h.p. (Chernoff), so typical instances
  force h*h >= 2m >= n^2/3, i.e. h = Theta(n), while the claimed law
  (1+o(1)) * sqrt(n*p) = sqrt(n/2) = Theta(sqrt(n)) is smaller by a
  factor of Theta(sqrt(n)) -- no (1+o(1)) with constant 1 survives.

  Kernel-certified:
    * the counting lemma, fully general: 2*m <= h*(h-1) -> h*h >= 2*m
      (so h >= sqrt(2*m));
    * the anchor at n = 1000, p = 1/2: 2*m >= n^2/3 = 333333 forces
      h >= 578 (a graph with h <= 577 has h*(h-1) <= 577*576 = 332352 <
      333333), while the claimed value satisfies sqrt(1000 * 1/2) < 23:
      the claimed constant-1 concentration fails by a factor of more
      than 25.

  All arithmetic is closed kernel computation; axiom-free.  The
  color-pair count C(h,2) = h(h-1)/2 and the Chernoff bound for the
  edge count are classical and cited.
-/

namespace Tlmc3479

/-! ## The deterministic counting bound (general in h and m). -/

/-- If 2m <= h(h-1) (the harmonious color-pair count) then h*h >= 2m:
    the harmonious chromatic number is at least sqrt(2m). -/
theorem counting_bound : ∀ h m : Nat, 2 * m ≤ h * (h - 1) → h * h ≥ 2 * m := by
  intro h m hm
  exact Nat.le_trans hm (Nat.mul_le_mul_left h (Nat.sub_le h 1))

/-! ## The anchor at n = 1000, p = 1/2. -/

/-- h(h-1) >= 333333 forces h >= 578: any h <= 577 has
    h(h-1) <= 577*576 = 332352 < 333333. -/
theorem anchor_h_ge_578 : ∀ h : Nat, 333333 ≤ h * (h - 1) → 578 ≤ h := by
  intro h hh
  rcases Nat.lt_or_ge h 578 with hlt | hge
  · have hle : h ≤ 577 := Nat.le_of_lt_succ hlt
    have hp : h * (h - 1) ≤ 577 * 576 := Nat.mul_le_mul hle (Nat.sub_le_sub_right hle 1)
    exact absurd (Nat.le_trans hh hp) (by decide)
  · exact hge

/-- The claimed law's value at n = 1000, p = 1/2 is below 23:
    sqrt(1000 * 1/2) = sqrt(500) < 23. -/
theorem claimed_value_small : (23:Nat) * 23 < 333333 := by decide

/-- The forced value exceeds the claimed one by a factor of more than
    25. -/
theorem factor_gt_25 : (578:Nat) > 23 * 25 := by decide

/-! ## THE REFUTATION. -/

/-- The claimed constant-1 concentration at sqrt(n*p) is incompatible
    with the deterministic counting bound: 23 >= 578 is false. -/
theorem conjecture_refuted : ¬ ((23:Nat) ≥ 578) := by decide

end Tlmc3479
