/-!
# Disproof of TLMC conjecture 00000001128 — Lean 4 certificate

Conjecture (verbatim): "Definition: M(w,j) is the maximal monomial coefficient in the
degree-j part of the Schubert polynomial S_w. Conjecture: M(w,j) equals
min(j, l(w), ceil(l(w)/2))! times a lattice-path count C(w), ..."

A lattice-path count `C(w)` is a non-negative integer, so the conjectural identity
implies `min(j, l(w), ceil(l(w)/2))!` divides `M(w,j)`. For `w = 321` in `S_3`:

* `l(321) = 3` (computed below from the one-line notation),
* `S_321 = x1^2*x2 + x1*x2^2` is homogeneous of degree 3 with both coefficients `1`
  (standard product formula `x1*(x1+x2)*x2` for the top Schubert polynomial; also
  re-derived independently in `reproduce.py` via the down-transition recurrence),
  hence `M(321, 3) = 1`,
* the conjectured factor is `min(3, 3, ceil(3/2))! = 2! = 2`,
* but `2 ∤ 1`: no `C : ℕ` satisfies `1 = 2 * C`, i.e. the conjecture would force the
  lattice-path count `C(321) = 1/2`, which does not exist.

This file imports nothing; every theorem is axiom-free (see Check.lean).
-/

/-! ## Data of the counterexample -/

/-- One-line notation of the permutation `321` in `S_3`. -/
def w321 : List Nat := [3, 2, 1]

/-- Inversion count `l(w)` of a permutation in one-line notation. -/
def invCount : List Nat → Nat
  | [] => 0
  | x :: xs => (xs.filter (fun y => y < x)).length + invCount xs

/-- `⌈n/2⌉` (for the positive integers used here). -/
def ceilHalf (n : Nat) : Nat := (n + 1) / 2

/-- Own factorial (avoids any dependency questions). -/
def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

/-- The Schubert polynomial `S_321 = x1^2*x2 + x1*x2^2` as a monomial list
`(exponent vector, coefficient)`; homogeneous of degree 3, so its degree-3 part is the
whole polynomial. Matches the top-element product formula `x1*(x1+x2)*x2` and the
independent recurrence computation in `reproduce.py`. -/
def poly321 : List (List Nat × Nat) := [([2, 1, 0], 1), ([1, 2, 0], 1)]

/-- Maximal monomial coefficient of the degree-`j` part of a monomial-list polynomial. -/
def maxCoeffDeg (p : List (List Nat × Nat)) (j : Nat) : Nat :=
  p.foldl (fun acc m => if m.1.sum = j then max acc m.2 else acc) 0

/-- `M(321, 3)`, the maximal monomial coefficient of the degree-3 part of `S_321`. -/
def M321 : Nat := maxCoeffDeg poly321 3

/-- The conjectured factor `min(j, l(w), ceil(l(w)/2))!` at `(w, j) = (321, 3)`. -/
def k : Nat := min 3 (min 3 (ceilHalf 3))

/-! ## The attack numbers, computed -/

/-- `l(321) = 3`: the inversions are (3,2), (3,1), (2,1). -/
theorem l321 : invCount w321 = 3 := rfl

/-- `⌈3/2⌉ = 2`. -/
theorem ceil3div2 : ceilHalf 3 = 2 := rfl

/-- The conjectured factor at the counterexample is `k = 2`. -/
theorem k_eq : k = 2 := rfl

/-- Hence the conjectured factor is `k! = 2`. -/
theorem fact_k : fact k = 2 := rfl

/-- `M(321, 3) = 1`: both degree-3 monomials `x1^2*x2` and `x1*x2^2` have coefficient 1. -/
theorem M321_eq : M321 = 1 := rfl

/-! ## The falsification -/

/-- The arithmetic core of the disproof: the conjectural identity
`M(w,j) = min(j, l(w), ceil(l(w)/2))! * C(w)` admits **no** lattice-path count
`C : ℕ` at `(w, j) = (321, 3)`, since it would require `1 = 2 * C`. -/
theorem falsified : ¬ ∃ C : Nat, M321 = fact k * C := by
  intro h
  cases h with
  | intro C h =>
    rw [M321_eq, fact_k] at h
    -- `h : 1 = 2 * C`, which is impossible for `C : ℕ` (proved below without omega,
    -- keeping the whole file axiom-free).
    cases C with
    | zero => exact Nat.noConfusion h
    | succ n =>
      have h2 : 2 ≤ 2 * (n + 1) := by
        rw [Nat.mul_succ]
        exact Nat.le_add_left 2 (2 * n)
      exact Nat.not_succ_le_self 1 (Nat.le_trans h2 (Nat.le_of_eq h.symm))
