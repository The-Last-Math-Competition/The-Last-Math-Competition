/-
  Conjecture 00000007602 — Module 1: Binomial Zeros, Strictly Monotone Basis
  Tuples, and the Pigeonhole Threshold.

  Pure Core Lean 4.19.0 (zero external dependencies).
-/

namespace Conjecture00000007602

/-- Factorial `k!`. -/
def factorial : Nat → Nat
  | 0 => 1
  | k + 1 => (k + 1) * factorial k

theorem factorial_pos : ∀ k : Nat, 0 < factorial k
  | 0 => Nat.zero_lt_one
  | k + 1 => Nat.mul_pos (Nat.succ_pos k) (factorial_pos k)

theorem factorial_ne_zero (k : Nat) : factorial k ≠ 0 :=
  Nat.ne_of_gt (factorial_pos k)

/-- Binomial coefficient `choose n k` via Pascal's recurrence. -/
def choose : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => choose n k + choose n (k + 1)

@[simp] theorem choose_zero_right : ∀ n : Nat, choose n 0 = 1
  | 0 => rfl
  | _ + 1 => rfl

/-- Falling factorial `n * (n - 1) * ... * (n - k + 1)` on `Nat`. -/
def fallingFactorial : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => (n + 1) * fallingFactorial n k

@[simp] theorem fallingFactorial_zero_right : ∀ n : Nat, fallingFactorial n 0 = 1
  | 0 => rfl
  | _ + 1 => rfl

/-- Degree-`k` integer falling-factorial polynomial `x * (x - 1) * ... * (x - k + 1)`. -/
def fallingPoly (x : Int) : Nat → Int
  | 0 => 1
  | k + 1 => x * fallingPoly (x - 1) k

theorem choose_eq_zero_of_lt : ∀ {n k : Nat}, n < k → choose n k = 0
  | 0, _ + 1, _ => rfl
  | n + 1, k + 1, h => by
      have h1 : n < k := Nat.lt_of_succ_lt_succ h
      have h2 : n < k + 1 := Nat.lt_succ_of_lt h1
      simp [choose, choose_eq_zero_of_lt h1, choose_eq_zero_of_lt h2]

theorem choose_pos_of_le : ∀ {n k : Nat}, k ≤ n → 0 < choose n k
  | n, 0, _ => by simp
  | 0, _ + 1, h => absurd h (Nat.not_le_of_gt (Nat.succ_pos _))
  | n + 1, k + 1, h => by
      have hk : k ≤ n := Nat.le_of_succ_le_succ h
      have hpos : 0 < choose n k := choose_pos_of_le hk
      simp [choose]
      omega

/-- Exact integer vanishing threshold of `choose n k`: `choose n k = 0 ↔ n < k`. -/
theorem choose_eq_zero_iff (n k : Nat) : choose n k = 0 ↔ n < k := by
  constructor
  · intro hz
    cases Nat.lt_or_ge n k with
    | inl hlt => exact hlt
    | inr hge =>
        have hpos := choose_pos_of_le hge
        omega
  · exact choose_eq_zero_of_lt

/-- Positivity below and at the threshold: `0 < choose n k ↔ k ≤ n`. -/
theorem choose_pos_iff (n k : Nat) : 0 < choose n k ↔ k ≤ n := by
  constructor
  · intro hpos
    cases Nat.lt_or_ge n k with
    | inl hlt =>
        have hz := choose_eq_zero_of_lt hlt
        omega
    | inr hge => exact hge
  · exact choose_pos_of_le

/-- Top exterior degree has dimension `choose n n = 1`. -/
theorem choose_self : ∀ n : Nat, choose n n = 1
  | 0 => rfl
  | n + 1 => by
      have hz : choose n (n + 1) = 0 := choose_eq_zero_of_lt (Nat.lt_succ_self n)
      simp [choose, choose_self n, hz]

theorem choose_one (n : Nat) : choose n 1 = n := by
  induction n with
  | zero => rfl
  | succ m ih =>
      simp [choose, ih]
      omega

theorem fallingFactorial_succ_right :
    ∀ (n k : Nat), fallingFactorial n (k + 1) = (n - k) * fallingFactorial n k
  | 0, _ => by simp [fallingFactorial]
  | n + 1, 0 => by simp [fallingFactorial]
  | n + 1, k + 1 => by
      have ih := fallingFactorial_succ_right n k
      simp only [fallingFactorial, ih, Nat.succ_sub_succ_eq_sub]
      rw [← Nat.mul_assoc, Nat.mul_comm (n + 1) (n - k), Nat.mul_assoc]

/-- Polynomial-combinatorial bridge: `choose n k * k! = n * (n - 1) * ... * (n - k + 1)`. -/
theorem choose_mul_factorial :
    ∀ (n k : Nat), choose n k * factorial k = fallingFactorial n k
  | n, 0 => by simp [factorial]
  | 0, _ + 1 => by simp [choose, fallingFactorial]
  | n + 1, k + 1 => by
      have ih1 := choose_mul_factorial n k
      have ih2 := choose_mul_factorial n (k + 1)
      simp only [choose]
      rw [Nat.add_mul, ih2]
      have hfac : choose n k * factorial (k + 1) = (k + 1) * fallingFactorial n k := by
        calc
          choose n k * factorial (k + 1)
              = choose n k * ((k + 1) * factorial k) := rfl
          _ = (k + 1) * (choose n k * factorial k) := by
                rw [← Nat.mul_assoc, Nat.mul_comm (choose n k) (k + 1), Nat.mul_assoc]
          _ = (k + 1) * fallingFactorial n k := by rw [ih1]
      rw [hfac, fallingFactorial_succ_right n k]
      cases Nat.lt_or_ge n k with
      | inl hlt =>
          have hz : fallingFactorial n k = 0 := by
            rw [← ih1, choose_eq_zero_of_lt hlt, Nat.zero_mul]
          simp [fallingFactorial, hz]
      | inr hge =>
          rw [← Nat.add_mul]
          have hsum : k + 1 + (n - k) = n + 1 := by omega
          rw [hsum]
          rfl

theorem intCast_add (a b : Nat) : ((a + b : Nat) : Int) = (a : Int) + (b : Int) := by
  omega

theorem intCast_mul (a : Nat) : ∀ b : Nat, ((a * b : Nat) : Int) = (a : Int) * (b : Int)
  | 0 => by simp
  | b + 1 => by
      have h : a * (b + 1) = a * b + a := Nat.mul_succ a b
      rw [h, intCast_add, intCast_mul a b]
      have h1 : ((b + 1 : Nat) : Int) = (b : Int) + 1 := by omega
      rw [h1, Int.mul_add, Int.mul_one]

theorem fallingPoly_natCast :
    ∀ (k n : Nat), fallingPoly (n : Int) k = (fallingFactorial n k : Int)
  | 0, n => by simp [fallingPoly]
  | k + 1, 0 => by simp [fallingPoly, fallingFactorial]
  | k + 1, n + 1 => by
      have hsub : (((n + 1 : Nat) : Int) - 1) = (n : Int) := by omega
      simp only [fallingPoly, fallingFactorial, hsub, fallingPoly_natCast k n, intCast_mul]

/-- Exact integer roots of the degree-`k` binomial numerator `fallingPoly x k`:
    `x * (x - 1) * ... * (x - k + 1) = 0 ↔ x ∈ {0, 1, ..., k - 1}`. -/
theorem fallingPoly_eq_zero_iff :
    ∀ (k : Nat) (x : Int), fallingPoly x k = 0 ↔ ∃ j : Nat, j < k ∧ x = (j : Int)
  | 0, _ => by simp [fallingPoly]
  | k + 1, x => by
      simp only [fallingPoly, Int.mul_eq_zero]
      rw [fallingPoly_eq_zero_iff k (x - 1)]
      constructor
      · intro h
        cases h with
        | inl hx0 => exact ⟨0, Nat.succ_pos k, hx0⟩
        | inr hprev =>
            rcases hprev with ⟨j, hj, hxj⟩
            exact ⟨j + 1, Nat.succ_lt_succ hj, by omega⟩
      · rintro ⟨j, hj, rfl⟩
        cases j with
        | zero => exact Or.inl rfl
        | succ m =>
            right
            exact ⟨m, Nat.lt_of_succ_lt_succ hj, by omega⟩

/-- Enumeration of all strictly increasing `k`-tuples with entries `< n`,
    indexing the canonical exterior basis of `Λ^k(K^n)`. -/
def strictIncLists : Nat → Nat → List (List Nat)
  | _, 0 => [[]]
  | 0, _ + 1 => []
  | n + 1, k + 1 =>
      strictIncLists n (k + 1) ++ (strictIncLists n k).map (fun l => l ++ [n])

@[simp] theorem strictIncLists_zero_right : ∀ n : Nat, strictIncLists n 0 = [[]]
  | 0 => rfl
  | _ + 1 => rfl

/-- Exact exterior-basis count: `(strictIncLists n k).length = choose n k`. -/
theorem strictIncLists_length :
    ∀ (n k : Nat), (strictIncLists n k).length = choose n k
  | n, 0 => by simp
  | 0, _ + 1 => rfl
  | n + 1, k + 1 => by
      simp only [strictIncLists, choose, List.length_append, List.length_map,
        strictIncLists_length n (k + 1), strictIncLists_length n k]
      exact Nat.add_comm _ _

theorem strictIncLists_empty_iff (n k : Nat) :
    strictIncLists n k = [] ↔ n < k := by
  rw [← List.length_eq_zero_iff, strictIncLists_length, choose_eq_zero_iff]

/-- Strictly monotone multi-indices `I : Fin k → Fin n`. -/
def StrictMonoFin {k n : Nat} (I : Fin k → Fin n) : Prop :=
  ∀ a b : Fin k, a.val < b.val → (I a).val < (I b).val

/-- Helper: skip index `r` when mapping `Fin m → Fin (m + 1)`. -/
def skipFin {m : Nat} (r : Fin (m + 1)) (i : Fin m) : Fin (m + 1) :=
  if i.val < r.val then ⟨i.val, by omega⟩ else ⟨i.val + 1, by omega⟩

@[simp] theorem skipFin_val {m : Nat} (r : Fin (m + 1)) (i : Fin m) :
    (skipFin r i).val = if i.val < r.val then i.val else i.val + 1 := by
  unfold skipFin
  split <;> rfl

theorem skipFin_ne {m : Nat} (r : Fin (m + 1)) (i : Fin m) : skipFin r i ≠ r := by
  intro heq
  have hval : (skipFin r i).val = r.val := congrArg Fin.val heq
  rw [skipFin_val] at hval
  split at hval <;> omega

theorem skipFin_injective {m : Nat} (r : Fin (m + 1)) {i j : Fin m}
    (h : skipFin r i = skipFin r j) : i = j := by
  have hval : (skipFin r i).val = (skipFin r j).val := congrArg Fin.val h
  rw [skipFin_val, skipFin_val] at hval
  apply Fin.ext
  split at hval <;> split at hval <;> omega

/-- Finite Pigeonhole Principle: whenever `n < k`, no map `Fin k → Fin n` is injective;
    every multi-index `I : Fin k → Fin n` repeats at two distinct tensor positions. -/
theorem pigeonhole_fin :
    ∀ {n k : Nat}, n < k → ∀ (I : Fin k → Fin n), ∃ p q : Fin k, p ≠ q ∧ I p = I q
  | 0, k, h, I =>
      let p0 : Fin k := ⟨0, h⟩
      False.elim (Nat.not_lt_zero (I p0).val (I p0).isLt)
  | n + 1, k, h, I => by
      cases Classical.em (∃ p q : Fin k, p ≠ q ∧ I p = I q) with
      | inl hex => exact hex
      | inr hno =>
          have hinj : ∀ p q : Fin k, I p = I q → p = q := by
            intro p q hpq
            cases Classical.em (p = q) with
            | inl heq => exact heq
            | inr hne => exact False.elim (hno ⟨p, q, hne, hpq⟩)
          cases Classical.em (∃ r : Fin k, (I r).val = n) with
          | inr hnone =>
              let I' : Fin k → Fin n := fun p =>
                ⟨(I p).val, by
                  have hlt := (I p).isLt
                  have hne : (I p).val ≠ n := fun he => hnone ⟨p, he⟩
                  omega⟩
              have hnlt : n < k := by omega
              rcases pigeonhole_fin hnlt I' with ⟨p, q, hne, hpq⟩
              have hval : (I p).val = (I q).val := congrArg (@Fin.val n) hpq
              exact False.elim (hne (hinj p q (Fin.ext hval)))
          | inl hhit =>
              rcases hhit with ⟨r0, hr0⟩
              cases k with
              | zero => omega
              | succ m =>
                  have hnm : n < m := by omega
                  let I' : Fin m → Fin n := fun i =>
                    let x := skipFin r0 i
                    have hxne : x ≠ r0 := skipFin_ne r0 i
                    have hIxne : I x ≠ I r0 := fun he => hxne (hinj x r0 he)
                    have hvalne : (I x).val ≠ n := by
                      intro hv
                      apply hIxne
                      apply Fin.ext
                      omega
                    ⟨(I x).val, by
                      have hlt := (I x).isLt
                      omega⟩
                  rcases pigeonhole_fin hnm I' with ⟨i, j, hne, hij⟩
                  have hval : (I (skipFin r0 i)).val = (I (skipFin r0 j)).val :=
                    congrArg (@Fin.val n) hij
                  have hskip : skipFin r0 i = skipFin r0 j :=
                    hinj (skipFin r0 i) (skipFin r0 j) (Fin.ext hval)
                  exact False.elim (hne (skipFin_injective r0 hskip))

/-- Consequently, no strictly monotone map `Fin k → Fin n` exists when `n < k`. -/
theorem no_strictMonoFin_of_lt {n k : Nat} (h : n < k) (I : Fin k → Fin n) :
    ¬ StrictMonoFin I := by
  intro hmono
  rcases pigeonhole_fin h I with ⟨p, q, hne, hpq⟩
  have hval : p.val ≠ q.val := fun hv => hne (Fin.ext hv)
  cases Nat.lt_or_gt_of_ne hval with
  | inl hlt =>
      have := hmono p q hlt
      rw [hpq] at this
      exact Nat.lt_irrefl _ this
  | inr hgt =>
      have := hmono q p hgt
      rw [hpq] at this
      exact Nat.lt_irrefl _ this

end Conjecture00000007602
