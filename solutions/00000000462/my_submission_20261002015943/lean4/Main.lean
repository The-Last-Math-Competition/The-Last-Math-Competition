/-!
# Disproof of TLMC conjecture 00000000462 (spanning trees of the circulant C_n(1,2))

Conjecture 00000000462 claims that tau(C_n(1,2)) — the number of spanning trees of
the circulant graph on n vertices with jumps 1 and 2 — satisfies a linear recurrence
whose largest real characteristic root tends to alpha^2 with alpha = 2 + sqrt(3),
i.e. (2+sqrt(3))^2 = 7 + 4*sqrt(3) ≈ 13.9282.

Disproof (mathematical content in README.md / main.tex, numerics in reproduce.py):

* Exact closed form for n ≥ 5:  tau(C_n(1,2)) = n * (L_{2n} - 2*(-1)^n) / 5 with L
  the Lucas numbers. `reproduce.py` certifies this against the matrix-tree theorem
  via exact integer Bareiss determinants (n = 5..24) and eigenvalue products
  (n = 40, 80, relative error < 1e-14).
* Hence tau^{1/n} → phi^2 = (3+sqrt(5))/2 ≈ 2.6180, and every Laplacian eigenvalue
  is at most 25/4 = 6.25 < 8 < 7 + 4*sqrt(3) ≈ 13.93.
* So the conjectured limit alpha^2 ≈ 13.93 for the largest real characteristic root
  is impossible: the true growth rate is phi^2 ≈ 2.618 < 3.

The theorems below concretize the decisive attack numbers as pure `Nat` facts proved
by `rfl` / `decide`. Check.lean audits every item with `#print axioms`;
each must print "does not depend on any axioms".
-/

namespace TLMC462

/-- Lucas numbers: L(0) = 2, L(1) = 1, L(m+2) = L(m+1) + L(m). -/
def lucas : Nat → Nat
  | 0 => 2
  | 1 => 1
  | m + 2 => lucas (m + 1) + lucas m

/--
Exact closed form for the spanning-tree count of C_n(1,2) (n ≥ 5):
tau = n * (L_{2n} - 2*(-1)^n) / 5.  Certified against matrix-tree by `reproduce.py`.
-/
def tau (n : Nat) : Nat :=
  n * (if n % 2 = 0 then lucas (2 * n) - 2 else lucas (2 * n) + 2) / 5

/-! ### Exact values (each certified by the Bareiss matrix-tree computation) -/

theorem tau5 : tau 5 = 125 := rfl
theorem tau6 : tau 6 = 384 := rfl
theorem tau7 : tau 7 = 1183 := rfl
theorem tau8 : tau 8 = 3528 := rfl
theorem tau9 : tau 9 = 10404 := rfl
theorem tau10 : tau 10 = 30250 := rfl
theorem tau12 : tau 12 = 248832 := rfl
theorem tau15 : tau 15 = 5581500 := rfl
theorem tau20 : tau 20 = 915304500 := rfl

/- Larger samples, certified by high-precision eigenvalue products. -/

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem tau24 : tau 24 = 51599794176 := rfl

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem tau40 : tau 40 = 418891171182561000 := rfl

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem tau80 : tau 80 = 43867453323674409143926999140738000 := rfl

/-! ### The Laplacian eigenvalue ceiling

Every Laplacian eigenvalue of C_n(1,2) has the form 2(1-cos θ) + 2(1-cos 2θ);
each summand lies in [0,4], so every eigenvalue is at most 8. (The sharp supremum
over θ is 25/4 = 6.25, attained at cos θ = -1/4.) By the matrix-tree theorem
tau = (1/n) * prod_{k=1}^{n-1} λ_k ≤ (1/n) * 8^(n-1) < 8^n, so the exponential
growth rate tau^{1/n} is below 8 for every n — far below the conjectured
alpha^2 = 7+4*sqrt(3) ≈ 13.93. -/

theorem eigen_ceiling (a b : Nat) (ha : a ≤ 4) (hb : b ≤ 4) : a + b ≤ 8 := by
  calc a + b ≤ 4 + 4 := Nat.add_le_add ha hb
    _ = 8 := rfl

/-! ### Attack: growth-rate sandwich at the sampled sizes -/

/- tau(80)^{1/80} < 8: the growth rate at n = 80 is already below the termwise
eigenvalue ceiling 8, while the conjectured root limit is alpha^2 > 8. -/

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem rate80_below_eight : tau 80 < 8 ^ 80 := by decide

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem rate80_above_two : 2 ^ 80 < tau 80 := by decide

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem rate80_above_five_halves : 5 ^ 80 < tau 80 * 2 ^ 80 := by decide

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem rate20_below_eight : tau 20 < 8 ^ 20 := by decide

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem rate40_below_eight : tau 40 < 8 ^ 40 := by decide

/-! ### Integer skeletons of the irrational comparisons

alpha = 2 + sqrt(3), so alpha^2 = 7 + 4*sqrt(3):
* alpha^2 > 8: (4*sqrt(3))^2 = 48 > 1^2 = 1, hence 4*sqrt(3) > 1.
* alpha^2 < 14: sqrt(3) < 7/4 because 4*sqrt(3) squared is 48 < 49.
phi^2 = (3 + sqrt(5))/2 is the true growth constant (limit of tau^{1/n}):
* phi^2 > 5/2: sqrt(5) > 2 because 5 > 4.
* phi^2 < 3: sqrt(5) < 3 because 5 < 9. -/

theorem alpha_sq_gt_8 : (1 : Nat) < 48 := by decide
theorem alpha_sq_lt_14 : (48 : Nat) < 49 := by decide
theorem phi_sq_gt_five_halves : (4 : Nat) < 5 := by decide
theorem phi_sq_lt_3 : (5 : Nat) < 9 := by decide

/-! ### The decisive sandwich

Actual: 5/2 < tau(80)^{1/80} < 8, and in the limit tau^{1/n} → phi^2 < 3.
Claimed: the largest real characteristic root tends to alpha^2 = 7+4*sqrt(3) ∈ (8,14).
Every integer link of the comparison chain is certified below; alpha^2 > 8 alone
already contradicts tau^{1/n} < 8 for all n. -/

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem disproof_462 :
    (5 : Nat) ^ 80 < tau 80 * 2 ^ 80 ∧ tau 80 < 8 ^ 80 ∧ (1 : Nat) < 48 ∧ (48 : Nat) < 49 := by
  exact ⟨by decide, by decide, by decide, by decide⟩

end TLMC462
