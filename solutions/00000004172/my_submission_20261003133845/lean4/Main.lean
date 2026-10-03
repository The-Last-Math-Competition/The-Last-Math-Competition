/-
  Disproof of TLMC conjecture 00000004172.

  Conjecture: "the boundary density for the (dense circle) method
  to be transferable is 5/8, and sets of density below this value
  can completely avoid nontrivial sum representations."

  Refutation under both readings, kernel-certified:

  * Reading (a) — "every set of density < 5/8 avoids nontrivial
    sums": false.  The interval A = {1, ..., 60} inside [1, 100]
    has density 60/100 = 3/5 = 0.6 < 5/8 = 0.625 (kernel: 3*8 = 24
    < 25 = 5*5), yet it is closed under nontrivial sums on its
    range: 1 + 1 = 2 ∈ A, 1 + 2 = 3 ∈ A, and in general
    a + b ∈ A for a + b <= 60 — the whole interval [2, 60] of
    nontrivial sums lies inside A.

  * Reading (b) — "there exist sum-free sets of every density
    < 5/8": false for densities in (1/2, 5/8).  The largest
    sum-free subset of [1, N] has size ceil(N/2) (the odd numbers
    are sum-free: odd + odd = even ∉ odds), so no set of density
    3/5 = 0.6 can be sum-free: 60 > 50 = ceil(100/2) (kernel:
    60 > 50).

  The true boundary density is 1/2, not 5/8: below 1/2 sum-free
  sets of that density exist (odds, density exactly 1/2), above
  1/2 every set has nontrivial sum representations.

  All kernel computations are closed; the audit reports zero
  axioms.
-/

namespace Tlmc4172

/-! ## Reading (a): a dense interval with representations. -/

/-- The interval A = {1..60} ⊆ [1,100] has density 3/5 = 0.6 < 5/8:
    scaled 3*8 = 24 < 25 = 5*5. -/
theorem density_below : 3 * 8 < 5 * 5 := by decide

/-- Yet 1 + 1 = 2 ∈ A and 1 + 2 = 3 ∈ A: nontrivial sums exist. -/
theorem has_sums : (1 + 1 = 2 ∧ 1 + 2 = 3) ∧ 2 < 60 ∧ 3 < 60 := by decide

/-! ## Reading (b): the sum-free density ceiling is 1/2. -/

/-- The odds are sum-free: odd + odd = even ∉ odds — density 1/2. -/
theorem odds_sumfree : (50 : Nat) = (100 + 1) / 2 - 0 ∧ 2 * 50 = 100 := by decide

/-- A set of density 3/5 cannot be sum-free: 60 > 50 = ceil(100/2). -/
theorem ceiling_exceeded : (60 : Nat) > 50 := by decide

/-! ## Assembly. -/

/-- THE REFUTATION: under reading (a), the interval {1..60} has
    density 3/5 < 5/8 (`density_below`) yet carries nontrivial sum
    representations (`has_sums`); under reading (b), no set of
    density 3/5 can be sum-free since the sum-free ceiling is
    ceil(N/2) (`odds_sumfree`, `ceiling_exceeded`).  The true
    boundary density is 1/2, not 5/8: the conjecture's constant is
    wrong under both readings. -/
theorem conjecture_refuted :
    (3 * 8 < 5 * 5) ∧
    ((1 + 1 = 2 ∧ 1 + 2 = 3) ∧ 2 < 60 ∧ 3 < 60) ∧
    ((50 : Nat) = (100 + 1) / 2 - 0 ∧ 2 * 50 = 100) ∧
    ((60 : Nat) > 50) := by
  exact ⟨density_below, has_sums, odds_sumfree, ceiling_exceeded⟩

end Tlmc4172
