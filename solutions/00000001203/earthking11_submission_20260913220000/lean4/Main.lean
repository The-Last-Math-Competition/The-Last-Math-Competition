/-
  Disproof of conjecture `00000001203`: formalisation.

  Conjecture (as filed):

    Definition: An addition-subtraction game is a subtraction game whose legal
    moves are the fixed values in a set `S`; the SG period is the least positive
    period of `g(n)`.
    Conjecture: If `S ⊂ {1, …, k}`, then the period of `g` divides `2^k − 1` if
    and only if `S` is nonempty and does not contain `k`; when `k ∈ S` the
    period is exactly `k + 1`.

  We formalise an unconditional refutation, using the PRIMARY witness

      S = {1, 3},   k = 3,   g = 0, 1, 0, 1, 0, 1, …  (g n = n % 2),

  whose least period is `2`.  Because `k = 3 ∈ S`, the conjecture's second
  clause demands the period be exactly `k + 1 = 4`; it is `2`.  Crucially
  `max(S) = 3 = k`, so the two possible readings of the parameter `k`
  (ambient bound vs. `k = max(S)`) coincide and the refutation is
  interpretation-free.

  We additionally formalise the clause-1 witness `S = {1, 2}` (least period
  `3 = 2^2 − 1`, so the period DOES divide `2^k − 1` even though the conjecture
  requires it not to under the charitable reading `k = max(S) = 2`).

  The file uses CORE LEAN ONLY (`import Std`); no Mathlib, no `Finset`, no
  `ZMod`, and no `sorry`.  Plain `decide` cannot kernel-reduce a well-founded
  definition, so every numeric fact about `g` / `g12` is routed through the
  closed-form lemmas `g_eq` and `g12_eq`, proved by strong recursion.
-/

import Std

set_option maxRecDepth 1000000

namespace Tlmc1203

/-! ## The mex (minimal excludant) of a finite list -/

/-- Computable `mex` of a `List Nat`: the least natural number not occurring in
the list.  The fuel is `l.length + 1`, which is enough because `mex l ≤
l.length`. -/
def mex (l : List Nat) : Nat :=
  let rec go : Nat → Nat → Nat
    | 0, m => m
    | f + 1, m => if l.contains m then go f (m + 1) else m
  go (l.length + 1) 0

/-! ## The primary witness: `S = {1, 3}` -/

/-- SG sequence of the subtraction game with move set `S = {1, 3}`:
`g n = mex {g (n-1), g (n-3)}`, with `g 0 = 0`.  The three base cases make the
well-founded recursion structural modulo the two moves. -/
def g : Nat → Nat
  | 0 => 0
  | 1 => mex [g 0]
  | 2 => mex [g 1]
  | n + 3 => mex [g (n + 2), g n]
termination_by n => n
decreasing_by all_goals omega

/-- Closed form of the primary witness: `g n = n % 2`.  Proved by strong
recursion; each successor case reduces `mex` of two concrete residues, which
`decide` can evaluate after `Nat.mod_two_eq_zero_or_one` splits on `n % 2`. -/
theorem g_eq (n : Nat) : g n = n % 2 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    match n with
    | 0 => rw [g]
    | 1 =>
      rw [g]
      rw [ih 0 (by omega)]
      decide
    | 2 =>
      rw [g]
      rw [ih 1 (by omega)]
      decide
    | k + 3 =>
      rw [g]
      rw [ih (k + 2) (by omega), ih k (by omega)]
      have h : (k + 2) % 2 = k % 2 := by omega
      rw [h]
      rcases Nat.mod_two_eq_zero_or_one k with h0 | h1
      · rw [h0]
        have h3 : (k + 3) % 2 = 1 := by omega
        rw [h3]
        decide
      · rw [h1]
        have h3 : (k + 3) % 2 = 0 := by omega
        rw [h3]
        decide

/-- The period-2 relation on the primary witness, immediate from `g_eq`. -/
theorem g_period (n : Nat) : g (n + 2) = g n := by
  rw [g_eq (n + 2), g_eq n]
  omega

/-- `p` is the least positive period of the primary SG sequence `g`. -/
def IsLeastPeriod (p : Nat) : Prop :=
  0 < p ∧ (∀ n, g (n + p) = g n) ∧
    ∀ q, 0 < q → (∀ n, g (n + q) = g n) → p ≤ q

/-- The primary witness has least period `2`: it is period-2, and no positive
period `q < 2` exists. -/
theorem least_period_two : IsLeastPeriod 2 := by
  refine ⟨by omega, g_period, ?_⟩
  intro q hq hper
  match q with
  | 0 => omega
  | 1 =>
    exfalso
    have h1 : g 1 = g 0 := by simpa using hper 0
    rw [g_eq 1, g_eq 0] at h1
    omega
  | q + 2 => omega

/-- The conjecture's second clause, for `k = 3` and `S = {1, 3}`, demands the
least period be exactly `k + 1 = 4`.  It is not: `2` is the least period, so
`4` cannot be. -/
theorem not_least_period_four : ¬ IsLeastPeriod (3 + 1) := by
  intro h
  have hmin := h.2.2 2 (by omega) g_period
  omega

/-- `2 ∤ 2^3 − 1 = 7`: the literal-reading first clause for the (fragile)
witness `S = {1}` demands `2 ∣ 7`, which fails. -/
theorem two_not_dvd_seven : ¬ (2 ∣ 7) := by decide

/-! ## The clause-1 witness: `S = {1, 2}` -/

/-- SG sequence of the subtraction game with moves `{1, 2}`:
`g12 n = mex {g12 (n-1), g12 (n-2)}`. -/
def g12 : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => mex [g12 (n + 1), g12 n]
termination_by n => n
decreasing_by all_goals omega

/-- Closed form for the clause-1 witness: `g12 n = n % 3`. -/
theorem g12_eq (n : Nat) : g12 n = n % 3 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    match n with
    | 0 => rw [g12]
    | 1 => rw [g12]
    | n + 2 =>
      rw [g12]
      rw [ih (n + 1) (by omega), ih n (by omega)]
      have hlt : n % 3 < 3 := Nat.mod_lt n (by decide)
      have hdisj : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
      rcases hdisj with h | h | h
      · have h1 : (n + 1) % 3 = 1 := by omega
        have h2 : (n + 2) % 3 = 2 := by omega
        rw [h, h1, h2]
        decide
      · have h1 : (n + 1) % 3 = 2 := by omega
        have h2 : (n + 2) % 3 = 0 := by omega
        rw [h, h1, h2]
        decide
      · have h1 : (n + 1) % 3 = 0 := by omega
        have h2 : (n + 2) % 3 = 1 := by omega
        rw [h, h1, h2]
        decide

/-- The period-3 relation on the clause-1 witness. -/
theorem g12_period (n : Nat) : g12 (n + 3) = g12 n := by
  rw [g12_eq (n + 3), g12_eq n]
  omega

/-- `p` is the least positive period of the clause-1 SG sequence `g12`. -/
def IsLeastPeriod12 (p : Nat) : Prop :=
  0 < p ∧ (∀ n, g12 (n + p) = g12 n) ∧
    ∀ q, 0 < q → (∀ n, g12 (n + q) = g12 n) → p ≤ q

/-- The clause-1 witness `S = {1, 2}` has least period `3 = 2^2 − 1`. -/
theorem least_period_three_12 : IsLeastPeriod12 3 := by
  refine ⟨by omega, g12_period, ?_⟩
  intro q hq hper
  rcases Nat.lt_or_ge q 3 with hlt | hge
  · exfalso
    have hq12 : q = 1 ∨ q = 2 := by omega
    rcases hq12 with h1 | h2
    · subst h1
      have h := hper 0
      change g12 1 = g12 0 at h
      rw [g12_eq 1, g12_eq 0] at h
      omega
    · subst h2
      have h := hper 0
      change g12 2 = g12 0 at h
      rw [g12_eq 2, g12_eq 0] at h
      omega
  · exact hge

/-- The clause-1 witness set `S = {1, 2}` as a list. -/
def witness12 : List Nat := [1, 2]

/-- `3 ∣ 2^2 − 1 = 3`. -/
theorem three_dvd_two_sq_sub_one : 3 ∣ 2 ^ 2 - 1 := ⟨1, by decide⟩

/-- Under the charitable reading `k = max(S) = 2` (so `k ∈ S`), the conjecture's
first clause requires the period NOT to divide `2^k − 1`; but the period is `3`
and `3 ∣ 2^2 − 1 = 3`.  Hence clause 1 fails for `S = {1, 2}`.  (Under the
literal ambient reading with `k = 3`, `3 ∤ 2^3 − 1 = 7` while `k ∉ S`, so the
first clause fails there as well; see `two_not_dvd_seven` / the write-up.) -/
theorem clause1_fails_charitable :
    ¬ ((3 ∣ 2 ^ 2 - 1) ↔ (0 < witness12.length ∧ ¬ (2 ∈ witness12))) := by
  intro h
  have hrhs : ¬ (0 < witness12.length ∧ ¬ (2 ∈ witness12)) := by decide
  exact hrhs (h.mp three_dvd_two_sq_sub_one)

/-! ## The disproof package -/

/-- Conjecture `00000001203` is FALSE.

  * Primary witness (interpretation-free, `max(S) = k = 3`): `S = {1,3}` has
    least period `2`, but the second clause demands `k + 1 = 4`.
  * The first clause also fails: for `S = {1,2}` the least period is `3` and
    `3 ∣ 2^2 − 1`, contradicting the charitable reading `k = max(S) = 2`
    (which, since `k ∈ S`, requires the period NOT to divide `2^k − 1`). -/
theorem conjecture_00000001203_false :
    IsLeastPeriod 2 ∧ ¬ IsLeastPeriod (3 + 1) ∧
      IsLeastPeriod12 3 ∧ (3 ∣ 2 ^ 2 - 1) ∧
      ¬ ((3 ∣ 2 ^ 2 - 1) ↔ (0 < witness12.length ∧ ¬ (2 ∈ witness12))) :=
  ⟨least_period_two, not_least_period_four, least_period_three_12,
    three_dvd_two_sq_sub_one, clause1_fails_charitable⟩

/-! ## Machine evaluation (display only) -/

-- The first 20 values of the primary SG sequence.
#eval (List.range 20).map g
-- The first 20 values of the clause-1 SG sequence.
#eval (List.range 20).map g12

end Tlmc1203
