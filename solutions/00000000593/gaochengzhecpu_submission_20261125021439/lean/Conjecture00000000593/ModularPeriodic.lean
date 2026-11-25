/-
Copyright (c) 2026. All rights reserved.
 Formalization of Conjecture 00000000593:
 Modular periodic structure (quasi-polynomiality on residue classes modulo `D`)
 and its exact equivalence with denominator divisibility into `(1 - t^D)^n`.
-/
import Conjecture00000000593.ChainDivisibility

namespace Conjecture00000000593

/-- Forward difference operator `(Δ u)_q = u_{q+1} - u_q`. -/
def fwdDiff (u : Nat → Int) : Nat → Int :=
  fun q => u (q + 1) - u q

/-- Iterated forward difference `Δ^k u`. -/
def iterFwdDiff : Nat → (Nat → Int) → (Nat → Int)
  | 0, u => u
  | k + 1, u => iterFwdDiff k (fwdDiff u)

/-- Modular difference operator `(Δ_D a)_m = a_{m+D} - a_m` with period `D`. -/
def modDiff (D : Nat) (a : Series) : Series :=
  fun m => a (m + D) - a m

/-- Iterated modular difference `Δ_D^k a`. -/
def iterModDiff (D : Nat) : Nat → Series → Series
  | 0, a => a
  | k + 1, a => iterModDiff D k (modDiff D a)

theorem iterModDiff_shift_arg (D : Nat) :
    ∀ (k : Nat) (f : Series) (m : Nat),
      iterModDiff D k (fun x => f (x + D)) m = iterModDiff D k f (m + D)
  | 0, _, _ => rfl
  | k + 1, f, m => by
      simp only [iterModDiff]
      have hfn : (modDiff D fun x => f (x + D)) = fun x => modDiff D f (x + D) := by
        funext x
        unfold modDiff
        have hx : x + D + D = (x + D) + D := rfl
        rw [hx]
      rw [hfn]
      exact iterModDiff_shift_arg D k (modDiff D f) m

theorem foldr_replicate_shiftSub_succ (D n : Nat) (a : Series) :
    (List.replicate (n + 1) D).foldr shiftSub a =
      (List.replicate n D).foldr shiftSub (shiftSub D a) := by
  induction n with
  | zero => rfl
  | succ n' ih =>
    change shiftSub D ((List.replicate (n' + 1) D).foldr shiftSub a) =
      shiftSub D ((List.replicate n' D).foldr shiftSub (shiftSub D a))
    rw [ih]

theorem iterModDiff_congr_ge (D : Nat) :
    ∀ (k : Nat) {f g : Series} {M : Nat},
      (∀ x : Nat, M ≤ x → f x = g x) →
      ∀ m : Nat, M ≤ m → iterModDiff D k f m = iterModDiff D k g m
  | 0, _, _, _, hfg, m, hm => hfg m hm
  | k + 1, f, g, M, hfg, m, hm => by
      simp only [iterModDiff]
      apply iterModDiff_congr_ge D k _ m hm
      intro x hx
      unfold modDiff
      rw [hfg (x + D) (by omega), hfg x hx]

/-- **Exact Coefficient-Difference Identity:**
For every `D ≥ 1`, `n ≥ 0`, and `m ≥ 0`, the `(m + n * D)`-th coefficient of
`(1 - t^D)^n · a(t)` equals `(Δ_D^n a)_m`. -/
theorem chainProd_replicate_coeff_eq_iterModDiff {D : Nat} (hD : 1 ≤ D) :
    ∀ (n : Nat) (a : Series) (m : Nat),
      mulPolySeries (chainProd (List.replicate n D)) a (m + n * D) =
        iterModDiff D n a m
  | 0, a, m => by
      simp only [List.replicate, Nat.zero_mul, Nat.add_zero, chainProd, iterModDiff]
      rw [mulPolySeries_one_poly]
  | n + 1, a, m => by
      have hpos : ∀ d ∈ List.replicate (n + 1) D, 1 ≤ d := by
        intro d hd
        rw [List.eq_of_mem_replicate hd]
        exact hD
      have hpos_n : ∀ d ∈ List.replicate n D, 1 ≤ d := by
        intro d hd
        rw [List.eq_of_mem_replicate hd]
        exact hD
      rw [mulPolySeries_chainProd hpos a, foldr_replicate_shiftSub_succ]
      rw [← mulPolySeries_chainProd hpos_n (shiftSub D a)]
      have h_idx : m + (n + 1) * D = (m + D) + n * D := by
        rw [Nat.succ_mul]
        omega
      rw [h_idx, chainProd_replicate_coeff_eq_iterModDiff hD n (shiftSub D a) (m + D)]
      rw [← iterModDiff_shift_arg D n (shiftSub D a) m]
      have h_eq : ∀ x : Nat, 0 ≤ x → shiftSub D a (x + D) = modDiff D a x := by
        intro x _
        unfold shiftSub modDiff
        have hlt : ¬ (x + D < D) := by omega
        have hsub : x + D - D = x := by omega
        simp [hlt, hsub]
      rw [iterModDiff_congr_ge D n h_eq m (Nat.zero_le m)]
      rfl

/-- Integer-valued binomial coefficients `binom q j = C(q, j)`. -/
def binom : Nat → Nat → Int
  | _, 0 => 1
  | 0, _ + 1 => 0
  | q + 1, j + 1 => binom q j + binom q (j + 1)

theorem fwdDiff_binom_zero : fwdDiff (fun q => binom q 0) = fun _ => 0 := by
  funext q
  unfold fwdDiff binom
  simp

theorem fwdDiff_binom_succ (j : Nat) :
    fwdDiff (fun q => binom q (j + 1)) = fun q => binom q j := by
  funext q
  unfold fwdDiff
  simp only [binom]
  omega

/-- Newton discrete Taylor / quasi-polynomial expansion of order `< n`:
`newtonEval n u q = ∑_{j=0}^{n-1} (Δ^j u)_0 * C(q, j)`. -/
def newtonEval : Nat → (Nat → Int) → Nat → Int :=
  let rec go : Nat → Nat → (Nat → Int) → Nat → Int
    | 0, _, _, _ => 0
    | k + 1, j, u, q => u 0 * binom q j + go k (j + 1) (fwdDiff u) q
  fun n u q => go n 0 u q

theorem newtonEval_zero (u : Nat → Int) (q : Nat) : newtonEval 0 u q = 0 := rfl

theorem newtonEval_go_at_zero :
    ∀ (k j : Nat) (u : Nat → Int), newtonEval.go k (j + 1) u 0 = 0
  | 0, _, _ => rfl
  | k + 1, j, u => by
      simp only [newtonEval.go, binom, Int.mul_zero, Int.zero_add]
      exact newtonEval_go_at_zero k (j + 1) (fwdDiff u)

theorem newtonEval_succ_at_zero (n : Nat) (u : Nat → Int) :
    newtonEval (n + 1) u 0 = u 0 := by
  simp only [newtonEval, newtonEval.go, binom, Int.mul_one]
  rw [newtonEval_go_at_zero]
  exact Int.add_zero (u 0)

theorem fwdDiff_newtonEval_go :
    ∀ (k j : Nat) (u : Nat → Int) (q : Nat),
      newtonEval.go k (j + 1) u (q + 1) - newtonEval.go k (j + 1) u q =
        newtonEval.go k j u q
  | 0, _, _, _ => by simp [newtonEval.go]
  | k + 1, j, u, q => by
      simp only [newtonEval.go]
      have ih := fwdDiff_newtonEval_go k (j + 1) (fwdDiff u) q
      have hbin : binom (q + 1) (j + 1) = binom q j + binom q (j + 1) := rfl
      rw [hbin, Int.mul_add]
      omega

theorem fwdDiff_newtonEval_succ (n : Nat) (u : Nat → Int) :
    fwdDiff (newtonEval (n + 1) u) = newtonEval n (fwdDiff u) := by
  funext q
  change newtonEval (n + 1) u (q + 1) - newtonEval (n + 1) u q = newtonEval n (fwdDiff u) q
  unfold newtonEval
  simp only [newtonEval.go, binom, Int.mul_one]
  have h := fwdDiff_newtonEval_go n 0 (fwdDiff u) q
  omega

theorem eq_of_zero_and_fwdDiff_eq {f g : Nat → Int}
    (h0 : f 0 = g 0) (hd : ∀ q : Nat, fwdDiff f q = fwdDiff g q) :
    ∀ q : Nat, f q = g q
  | 0 => h0
  | q + 1 => by
      have ih := eq_of_zero_and_fwdDiff_eq h0 hd q
      have hq := hd q
      unfold fwdDiff at hq
      omega

theorem iterFwdDiff_newtonEval_eq_zero :
    ∀ (n : Nat) (u : Nat → Int) (q : Nat), iterFwdDiff n (newtonEval n u) q = 0
  | 0, _, _ => rfl
  | n + 1, u, q => by
      simp only [iterFwdDiff, fwdDiff_newtonEval_succ]
      exact iterFwdDiff_newtonEval_eq_zero n (fwdDiff u) q

/-- **Discrete Newton Quasi-Polynomial Theorem:**
`(Δ^n u)_q = 0` for all `q ≥ 0` if and only if `u_q = ∑_{j=0}^{n-1} (Δ^j u)_0 C(q, j)` for all `q ≥ 0`. -/
theorem iterFwdDiff_eq_zero_iff_newtonEval (n : Nat) (u : Nat → Int) :
    (∀ q : Nat, iterFwdDiff n u q = 0) ↔ (∀ q : Nat, u q = newtonEval n u q) := by
  induction n generalizing u with
  | zero =>
    constructor <;> (intro h q; exact h q)
  | succ n' ih =>
    constructor
    · intro h
      have h_du : ∀ q : Nat, fwdDiff u q = newtonEval n' (fwdDiff u) q :=
        (ih (fwdDiff u)).mp h
      apply eq_of_zero_and_fwdDiff_eq (newtonEval_succ_at_zero n' u).symm
      intro q
      rw [fwdDiff_newtonEval_succ, h_du q]
    · intro h q
      have hfn : u = newtonEval (n' + 1) u := funext h
      rw [hfn]
      exact iterFwdDiff_newtonEval_eq_zero (n' + 1) u q

theorem iterModDiff_residue_class (D : Nat) :
    ∀ (n : Nat) (a : Series) (c q : Nat),
      iterModDiff D n a (q * D + c) = iterFwdDiff n (fun q' => a (q' * D + c)) q
  | 0, _, _, _ => rfl
  | n + 1, a, c, q => by
      simp only [iterModDiff, iterFwdDiff]
      rw [iterModDiff_residue_class D n (modDiff D a) c q]
      have hfn : (fun q' => modDiff D a (q' * D + c)) = fwdDiff (fun q' => a (q' * D + c)) := by
        funext q'
        unfold modDiff fwdDiff
        have hidx : q' * D + c + D = (q' + 1) * D + c := by
          rw [Nat.succ_mul]
          omega
        rw [hidx]
      rw [hfn]

/-- **Eventual Modular Periodic Equivalence:**
For any `D ≥ 1`, `n ≥ 0`, threshold `m₀`, and coefficient sequence `a : Nat → Int`,
`(1 - t^D)^n · a(t)` has degree `< m₀ + n * D` if and only if `(Δ_D^n a)_m = 0` for all `m ≥ m₀`. -/
theorem eventual_modular_periodic_iff {D : Nat} (hD : 1 ≤ D) (n m₀ : Nat) (a : Series) :
    IsPolyBelow (m₀ + n * D) (mulPolySeries (chainProd (List.replicate n D)) a) ↔
      (∀ m : Nat, m₀ ≤ m → iterModDiff D n a m = 0) := by
  constructor
  · intro hpoly m hm
    rw [← chainProd_replicate_coeff_eq_iterModDiff hD n a m]
    exact hpoly (m + n * D) (by omega)
  · intro hdiff M hM
    have hsplit : M = (M - n * D) + n * D := by omega
    rw [hsplit, chainProd_replicate_coeff_eq_iterModDiff hD n a (M - n * D)]
    exact hdiff (M - n * D) (by omega)

/-- **Main Modular Periodic Structure (Quasi-Polynomial) Equivalence Theorem:**
For every period `D ≥ 1`, variable/pole bound `n ≥ 1`, and sequence `a : Nat → Int`:
1. `(1 - t^D)^n · a(t)` is a polynomial of degree `< n * D` (strictly proper rational series
   with denominator dividing `(1 - t^D)^n`),
2. if and only if `(Δ_D^n a)_m = 0` for all `m ≥ 0`,
3. if and only if on each residue class `c ∈ {0, ..., D - 1}`, `a_{q D + c}` is given for all
   `q ≥ 0` by the Newton binomial polynomial of degree `< n`. -/
theorem modular_periodic_iff {D : Nat} (hD : 1 ≤ D) (n : Nat) (a : Series) :
    (IsPolyBelow (n * D) (mulPolySeries (chainProd (List.replicate n D)) a) ↔
      (∀ m : Nat, iterModDiff D n a m = 0)) ∧
    ((∀ m : Nat, iterModDiff D n a m = 0) ↔
      (∀ c : Nat, c < D → ∀ q : Nat,
        a (q * D + c) = newtonEval n (fun q' => a (q' * D + c)) q)) := by
  refine ⟨?_, ?_⟩
  · have h0 := eventual_modular_periodic_iff hD n 0 a
    rw [Nat.zero_add] at h0
    constructor
    · intro hp m
      exact h0.mp hp m (Nat.zero_le m)
    · intro hd
      exact h0.mpr (fun m _ => hd m)
  · constructor
    · intro hall c _ q
      have h_res : ∀ q' : Nat, iterFwdDiff n (fun r => a (r * D + c)) q' = 0 := by
        intro q'
        rw [← iterModDiff_residue_class D n a c q']
        exact hall (q' * D + c)
      exact (iterFwdDiff_eq_zero_iff_newtonEval n (fun r => a (r * D + c))).mp h_res q
    · intro hqp m
      have hc : m % D < D := Nat.mod_lt m hD
      have hdiv : (m / D) * D + m % D = m := by
        have h1 := Nat.div_add_mod m D
        rw [Nat.mul_comm] at h1
        exact h1
      rw [← hdiv, iterModDiff_residue_class D n a (m % D) (m / D)]
      exact (iterFwdDiff_eq_zero_iff_newtonEval n (fun r => a (r * D + m % D))).mpr (hqp (m % D) hc) (m / D)

end Conjecture00000000593
