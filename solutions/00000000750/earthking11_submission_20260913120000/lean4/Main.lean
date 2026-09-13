/-
  Refutation of conjecture 00000000750 -- finite-difference / Mahler-coefficient core.

  We work over `Int` / `Nat` only (core Lean, `import Std`, no Mathlib).
  The map under consideration is `f(x) = x + 1`, whose Mahler coefficients are
  `a_n = Δⁿ f (0)`.  Since `f(x) = x + 1 = C(x,0) + C(x,1)`, we have
  `(a_n) = (1, 1, 0, 0, 0, …)`.  Hence, reduced modulo `p^k`, the sequence is
  eventually constant `0`, so its minimal eventual period is `1` -- not the
  conjectured `p^{k-1}(p-1)`.

  The p-adic (Z_p) setting, Haar-measure preservation and minimality of `x + 1`
  are discussed in `../main.tex` and checked numerically in `../reproduce.py`.
-/
import Std

namespace Tlmc750

/-- Forward difference operator: `(Δ f)(n) = f(n+1) - f(n)`. -/
def diff (f : Int → Int) : Int → Int := fun n => f (n + 1) - f n

/-- `n`-fold forward difference, `diffN 0 f = f`, `diffN (n+1) f = Δ (diffN n f)`. -/
def diffN : Nat → (Int → Int) → Int → Int
  | 0, f => f
  | n + 1, f => diff (diffN n f)

/-- The `n`-th Mahler coefficient of `f`: `a_n = Δⁿ f (0)`. -/
def mahlerCoeff (f : Int → Int) (n : Nat) : Int := diffN n f 0

/-- The first difference of `x + 1` is the constant `1`. -/
theorem diff_id_add_one : diff (fun x : Int => x + 1) = fun _ : Int => 1 := by
  funext n
  show ((n + 1) + 1) - (n + 1) = 1
  omega

/-- The first difference of any constant function is the zero function. -/
theorem diff_const (c : Int) : diff (fun _ : Int => c) = fun _ : Int => 0 := by
  funext n
  show c - c = (0 : Int)
  omega

/-- The `(n+1)`-st difference of a constant function is the zero function. -/
theorem diffN_const (c : Int) :
    ∀ n : Nat, diffN (n + 1) (fun _ : Int => c) = fun _ : Int => 0 := by
  intro n
  induction n with
  | zero =>
      show diff (diffN 0 (fun _ : Int => c)) = fun _ : Int => 0
      exact diff_const c
  | succ m ih =>
      show diff (diffN (m + 1) (fun _ : Int => c)) = fun _ : Int => 0
      rw [ih]
      simpa using diff_const (0 : Int)

/-- The second and all higher differences of `x + 1` vanish identically. -/
theorem diffN_id_add_one_two_add :
    ∀ m : Nat, diffN (m + 2) (fun x : Int => x + 1) = fun _ : Int => 0 := by
  intro m
  induction m with
  | zero =>
      show diff (diffN 1 (fun x : Int => x + 1)) = fun _ : Int => 0
      have h1 : diffN 1 (fun x : Int => x + 1) = fun _ : Int => 1 := by
        exact diff_id_add_one
      rw [h1]
      simpa using diff_const (1 : Int)
  | succ m ih =>
      show diff (diffN (m + 2) (fun x : Int => x + 1)) = fun _ : Int => 0
      rw [ih]
      simpa using diff_const (0 : Int)

/-- Every finite difference of order at least `2` of `x + 1` vanishes at `0`:
this is the statement that the Mahler coefficient sequence is `(1,1,0,0,…)`. -/
theorem diff_id_add_one_vanishes :
    ∀ n : Nat, 2 ≤ n → diffN n (fun x : Int => x + 1) 0 = 0 := by
  intro n hn
  obtain ⟨m, hm⟩ := Nat.le.dest hn
  rw [← hm, Nat.add_comm 2 m]
  simpa using congrFun (diffN_id_add_one_two_add m) 0

/-- The Mahler coefficient sequence of `x + 1` is `(1, 1, 0, 0, 0, …)`. -/
theorem mahler_coeffs :
    mahlerCoeff (fun x : Int => x + 1) 0 = 1 ∧
    mahlerCoeff (fun x : Int => x + 1) 1 = 1 ∧
    (∀ n : Nat, 2 ≤ n → mahlerCoeff (fun x : Int => x + 1) n = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · show (fun x : Int => x + 1) 0 = 1
    decide
  · show diff (fun x : Int => x + 1) 0 = 1
    simpa using congrFun diff_id_add_one 0
  · intro n hn
    exact diff_id_add_one_vanishes n hn

/-- The conjectured exact period `p^{k-1}(p-1)` is not `1` for the listed `(p,k)`. -/
theorem claimed_ne_one_2_2 : ¬ ((2 : Nat) ^ (2 - 1) * (2 - 1) = 1) := by decide

/-- The conjectured exact period `p^{k-1}(p-1)` is not `1` for the listed `(p,k)`. -/
theorem claimed_ne_one_2_3 : ¬ ((2 : Nat) ^ (3 - 1) * (2 - 1) = 1) := by decide

/-- The conjectured exact period `p^{k-1}(p-1)` is not `1` for the listed `(p,k)`. -/
theorem claimed_ne_one_3_1 : ¬ ((3 : Nat) ^ (1 - 1) * (3 - 1) = 1) := by decide

/-- The conjectured exact period `p^{k-1}(p-1)` is not `1` for the listed `(p,k)`. -/
theorem claimed_ne_one_3_2 : ¬ ((3 : Nat) ^ (2 - 1) * (3 - 1) = 1) := by decide

/-- The conjectured exact period `p^{k-1}(p-1)` is not `1` for the listed `(p,k)`. -/
theorem claimed_ne_one_5_1 : ¬ ((5 : Nat) ^ (1 - 1) * (5 - 1) = 1) := by decide

/-- The conjectured exact period `p^{k-1}(p-1)` is not `1` for the listed `(p,k)`. -/
theorem claimed_ne_one_5_2 : ¬ ((5 : Nat) ^ (2 - 1) * (5 - 1) = 1) := by decide

/-- Core finite-difference content refuting conjecture 00000000750:
all Mahler coefficients of `x + 1` of order `≥ 2` vanish (so the coefficient
sequence is eventually constant `0`, with minimal eventual period `1`), while
the conjectured period `p^{k-1}(p-1)` differs from `1` for the listed `(p,k)`. -/
theorem conjecture_00000000750_false :
    (∀ n : Nat, 2 ≤ n → diffN n (fun x : Int => x + 1) 0 = 0) ∧
    (¬ ((2 : Nat) ^ (2 - 1) * (2 - 1) = 1)) ∧
    (¬ ((2 : Nat) ^ (3 - 1) * (2 - 1) = 1)) ∧
    (¬ ((3 : Nat) ^ (1 - 1) * (3 - 1) = 1)) ∧
    (¬ ((3 : Nat) ^ (2 - 1) * (3 - 1) = 1)) ∧
    (¬ ((5 : Nat) ^ (1 - 1) * (5 - 1) = 1)) ∧
    (¬ ((5 : Nat) ^ (2 - 1) * (5 - 1) = 1)) := by
  exact ⟨diff_id_add_one_vanishes,
         claimed_ne_one_2_2, claimed_ne_one_2_3,
         claimed_ne_one_3_1, claimed_ne_one_3_2,
         claimed_ne_one_5_1, claimed_ne_one_5_2⟩

end Tlmc750
