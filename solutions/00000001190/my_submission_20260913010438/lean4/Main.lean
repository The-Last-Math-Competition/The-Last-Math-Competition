/-!
# Disproof of TLMC conjecture 00000001190 (counterexample at n = 2, q = 7)

We exhaustively enumerate all 7^4 = 2401 matrices `[[a, b], [c, d]]` over `F_7`,
keep those with `det ≠ 0` (this is `GL_2(F_7)`, 2016 elements), and machine-check:

* `count_gl2     : |GL_2(F_7)| = 2016`
* `count_order2  : #{M : M² = I, M ≠ I} = 57`   (formula claims 49)
* `count_order3  : #{M : M³ = I, M ≠ I} = 170`  (formula claims 0)
* `formula2      : Θ₂(7) = 49`
* `refute        : 57 ≠ 49 ∧ 170 ≠ 0`

Everything is proved by `decide` over the explicit enumeration:
zero axioms, zero `sorry`.

Note on the model: `F_7` is represented by the residues `{0,1,…,6}` in `Nat`
with explicit `% 7` arithmetic — the same ring as `ZMod 7` (or `Fin 7`), so all
element counts coincide. A matrix is a nested pair `(a, b, c, d)`
representing `[[a, b], [c, d]]`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

namespace Tlmc1190

/-- A 2x2 matrix over F_7, stored as `(a, b, c, d)` = `[[a, b], [c, d]]`,
entries kept in `{0,…,6}` (residues mod 7). -/
def M := Nat × Nat × Nat × Nat

/-- Matrix multiplication `[[a,b],[c,d]] * [[e,f],[g,h]]`, all entries mod 7. -/
def mul : M → M → M
  | (a, b, c, d), (e, f, g, h) =>
      ((a * e + b * g) % 7, (a * f + b * h) % 7,
       (c * e + d * g) % 7, (c * f + d * h) % 7)

/-- Determinant `a*d - b*c` mod 7. Entries are residues, so
`a*d % 7 + 21 - b*c % 7` is positive (no `Nat` underflow) and congruent to
`a*d - b*c` mod 7. -/
def det : M → Nat
  | (a, b, c, d) => (a * d % 7 + 21 - b * c % 7) % 7

/-- The identity matrix. -/
def one : M := (1, 0, 0, 1)

/-- Decidable equality on `M`, written explicitly as a Bool function. -/
def eqM : M → M → Bool
  | (a, b, c, d), (e, f, g, h) =>
      a == e && b == f && c == g && d == h

/-- `M ∈ GL_2(F_7)`, i.e. `det M ≠ 0`. -/
def isGl (m : M) : Bool := !(det m == 0)

/-- `M` has order exactly 2 (2 is prime, so `M ≠ I ∧ M² = I` suffices). -/
def isOrder2 (m : M) : Bool := !(eqM m one) && eqM (mul m m) one

/-- `M` has order exactly 3 (3 is prime, so `M ≠ I ∧ M³ = I` suffices). -/
def isOrder3 (m : M) : Bool := !(eqM m one) && eqM (mul m (mul m m)) one

/-- All 7^4 = 2401 matrices over F_7 (quadruple combination of `List.range 7`). -/
def matrices : List M :=
  (List.range 7).flatMap fun a =>
    (List.range 7).flatMap fun b =>
      (List.range 7).flatMap fun c =>
        (List.range 7).map fun d => (a, b, c, d)

/-- Brute force: `|GL_2(F_7)| = (7²−1)(7²−7) = 2016`. -/
theorem count_gl2 : (matrices.filter isGl).length = 2016 := by decide

/-- Brute force: 57 elements of order exactly 2, versus the formula's 49. -/
theorem count_order2 :
    (matrices.filter (fun m => isGl m && isOrder2 m)).length = 57 := by decide

/-- Brute force: 170 elements of order exactly 3, versus the formula's 0. -/
theorem count_order3 :
    (matrices.filter (fun m => isGl m && isOrder3 m)).length = 170 := by decide

/-! `Θ_r(q) = q^(n²−r) (q−1)^{-1} ∏_{i=1}^{r−1} (q^{n−i}−1)`; at `r = 2, n = 2, q = 7`
this is `7² · (7¹−1)/(7−1) = 49 · 6/6 = 49`. The sum for `p = 3` is empty (3 ∤ 2),
so the conjecture claims `N₃ = 0`. -/

/-- The single term `Θ₂(7)` of the conjectured sum (the only prime divisor of 2 is 2). -/
def theta2 : Nat := 7^(2*2-2) * ((7^(2-1) - 1) / (7-1))

/-- `Θ₂(7) = 49`: the formula's claimed value of `N₂`. -/
theorem formula2 : theta2 = 49 := rfl

/-- The conjecture's claim `N₃ = 0` (the sum over prime divisors of 2 omits 3). -/
theorem formula3 : (0 : Nat) = 0 := rfl

/-- Double refutation: both claimed values differ from the enumerated truth. -/
theorem refute : 57 ≠ 49 ∧ 170 ≠ 0 := ⟨by decide, by decide⟩

/-- The enumeration results are exactly the refuting numbers. -/
theorem refute_counts :
    (matrices.filter (fun m => isGl m && isOrder2 m)).length ≠ 49 ∧
    (matrices.filter (fun m => isGl m && isOrder3 m)).length ≠ 0 := by
  rw [count_order2, count_order3]
  decide

end Tlmc1190
