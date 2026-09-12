/-
  Disproof of conjecture 00000001072 (Lean 4, core only — no Mathlib).

  Conjecture: G(n,k,q) = q^((n-k)*k) * [n choose k]_q is the number of
  k-dimensional planes of F_q^n, and its prime-factor spectrum
  (a) consists exactly of the primes <= q^n - 1, and
  (b) every prime factor divides some q^i - 1 with i <= n.

  We formalize two independent counterexamples:
  * refute_I : at (2,1,2), G = 6 has prime factor 2, but 2 divides neither
    2^1 - 1 = 1 nor 2^2 - 1 = 3.                          -> (b) fails
  * refute_II : at (2,1,3), G = 12 has spectrum {2,3}, but 5 <= 3^2-1 = 8
    and 7 <= 3^2-1, and neither 5 nor 7 divides 12.       -> (a) fails

  All proofs are axiom-free and `sorry`-free: closed `rfl` computations and
  pure constructor logic (case splits with `Nat.succ.inj` and
  `Nat.noConfusion`).  No `decide`, no `simp`.
-/

/-- Notation for the natural numbers (core Lean 4 without Mathlib has no `ℕ`). -/
notation "ℕ" => Nat

namespace Tlmc1072

/-- Product of `q^(a+i+1) - 1` for `i < b`, i.e. `prod_{i=1..b} (q^(a+i) - 1)`. -/
def prodPow (q a b : ℕ) : ℕ :=
  (List.range b).foldl (fun acc i => acc * (q ^ (a + i + 1) - 1)) 1

/-- Gaussian binomial coefficient `[n choose k]_q`. -/
def gauss (n k q : ℕ) : ℕ := prodPow q (n - k) k / prodPow q 0 k

/-- The conjecture's function `G(n,k,q) = q^((n-k)*k) * [n choose k]_q`. -/
def G (n k q : ℕ) : ℕ := q ^ ((n - k) * k) * gauss n k q

/-- `G(2,1,2) = 2^1 · (2^2-1)/(2-1) = 2 · 3 = 6`. -/
theorem G212 : G 2 1 2 = 6 := rfl

/-- `G(2,1,3) = 3^1 · (3^2-1)/(3-1) = 3 · 4 = 12`. -/
theorem G213 : G 2 1 3 = 12 := rfl

/-- Supporting value: `G(3,1,2) = 2^2 · (2^3-1)/(2-1) = 4 · 7 = 28`. -/
theorem G312 : G 3 1 2 = 28 := rfl

/-- `2^1 - 1 = 1` and `2^2 - 1 = 3`. -/
theorem q21 : 2 ^ 1 - 1 = 1 := rfl
theorem q22 : 2 ^ 2 - 1 = 3 := rfl

/- The non-divisibility facts below are proved by pure constructor logic:
case-split on the divisibility witness `c` in `n = m * c` and repeatedly apply
`Nat.succ.inj` until one side becomes `0`, closing by `Nat.noConfusion`.
No `decide`, no `simp`, no axioms. -/

theorem not_2_dvd_1 : ¬ ((2:ℕ) ∣ 1) := fun ⟨c, hc⟩ => by
  cases c with
  | zero => exact Nat.noConfusion hc
  | succ d => exact Nat.noConfusion (Nat.succ.inj hc)

theorem not_2_dvd_3 : ¬ ((2:ℕ) ∣ 3) := fun ⟨c, hc⟩ => by
  cases c with
  | zero => exact Nat.noConfusion hc
  | succ d =>
    have h1 : (1:ℕ) = 2 * d := Nat.succ.inj (Nat.succ.inj hc)
    cases d with
    | zero => exact Nat.noConfusion h1
    | succ e => exact Nat.noConfusion (Nat.succ.inj h1)

theorem not_5_dvd_12 : ¬ ((5:ℕ) ∣ 12) := fun ⟨c, hc⟩ => by
  cases c with
  | zero => exact Nat.noConfusion hc
  | succ d =>
    have h1 : (7:ℕ) = 5 * d := Nat.succ.inj (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj hc))))
    cases d with
    | zero => exact Nat.noConfusion h1
    | succ e =>
      have h2 : (2:ℕ) = 5 * e := Nat.succ.inj (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj h1))))
      cases e with
      | zero => exact Nat.noConfusion h2
      | succ f => exact Nat.noConfusion (Nat.succ.inj (Nat.succ.inj h2))

theorem not_7_dvd_12 : ¬ ((7:ℕ) ∣ 12) := fun ⟨c, hc⟩ => by
  cases c with
  | zero => exact Nat.noConfusion hc
  | succ d =>
    have h1 : (5:ℕ) = 7 * d := Nat.succ.inj (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj hc))))))
    cases d with
    | zero => exact Nat.noConfusion h1
    | succ e => exact Nat.noConfusion (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj (Nat.succ.inj h1)))))

/-- **Refutation I** at `(n,k,q) = (2,1,2)`:
the prime `2` divides `G(2,1,2) = 6`, but `2` divides neither `2^1 - 1 = 1`
nor `2^2 - 1 = 3`. Hence the claim that every prime factor of `G` divides
some `q^i - 1` with `i <= n` is false. -/
theorem refute_I :
    ¬ ((2:ℕ) ∣ 2 ^ 1 - 1) ∧ ¬ ((2:ℕ) ∣ 2 ^ 2 - 1) ∧ ((2:ℕ) ∣ 6) :=
  ⟨not_2_dvd_1, not_2_dvd_3, ⟨3, rfl⟩⟩

/-- **Refutation II** at `(n,k,q) = (2,1,3)`:
`5 < 3^2 - 1 = 8` and `7 < 3^2 - 1`, but neither `5` nor `7` divides
`G(2,1,3) = 12`. Hence the spectrum of `G` is a proper subset of the primes
`<= q^n - 1`; the word *exactly* fails. -/
theorem refute_II :
    ((5:ℕ) ≤ 3 ^ 2 - 1) ∧ ¬ ((5:ℕ) ∣ 12) ∧
    ((7:ℕ) ≤ 3 ^ 2 - 1) ∧ ¬ ((7:ℕ) ∣ 12) ∧ (7 < 3 ^ 2 - 1) :=
  ⟨Nat.le.step (Nat.le.step (Nat.le.step Nat.le.refl)),
   not_5_dvd_12,
   Nat.le.step Nat.le.refl,
   not_7_dvd_12,
   Nat.le.refl⟩

end Tlmc1072
