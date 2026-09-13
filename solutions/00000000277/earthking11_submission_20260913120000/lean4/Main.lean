/-
  Rule-3 disproof for conjecture 00000000277.

  Claim under test (literal reading): M, the *maximum multiplicity of a Laplace
  eigenvalue on a planar flat torus* (supremum over all flat tori), equals 6,
  and multiplicity six is attained only on the order-thirty-two lattice torus.

  This file refutes the literal reading in core Lean (`import Std`, no Mathlib).

  Idea.  On the square torus  R² / Z²  (i.e. C / Z[i]) the Laplace eigenvalue
  4π²·N has multiplicity r₂(N), the number of representations of N as a sum of
  two squares.  Since r₂(5^k) = 4(k+1) → ∞, the multiplicity is unbounded, so
  the maximum is infinite and in particular not 6.

  The decisive witness is N = 25: r₂(25) = 12 > 6.

  Core Lean has no ℝ and `decide` gets stuck on `Rat` / nested `Decidable`
  reductions, so everything is stated over `Nat` / `Int` with the concrete
  counting function `r2` below.  The analytic correspondence (eigenvalue 4π²N
  ↔ pairs (a,b) with a²+b²=N) and the crystallographic restriction are
  documented, not formalised; see `lean4/README.md` for the precise scope.
-/
import Std

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Tlmc277

/-- `r2 N` is the number of ordered integer pairs `(a, b)` with
`a * a + b * b = N`.

It is computed by enumerating the non-negative pairs `0 ≤ a, b ≤ N` and
weighting each solution by the number of sign choices: `1` if the coordinate is
zero, `2` otherwise.  Since `a * a ≤ N` forces `|a| ≤ N`, this enumerates all
integer solutions. -/
def r2 (N : Nat) : Nat :=
  (List.range (N + 1)).foldr
    (fun a acc =>
      acc +
        (List.range (N + 1)).foldr
          (fun b acc2 =>
            if a * a + b * b = N then
              acc2 + (if a = 0 then 1 else 2) * (if b = 0 then 1 else 2)
            else acc2)
          0)
    0

/-- The number of representations of 1 as a sum of two squares is 4
(`(±1, 0)` and `(0, ±1)`). -/
theorem r2_1 : r2 1 = 4 := by decide

/-- `r2 5 = 8` (`(±1, ±2)` and `(±2, ±1)`). -/
theorem r2_5 : r2 5 = 8 := by decide

/-- The decisive witness: `r2 25 = 12`, i.e. 25 has twelve representations as a
sum of two squares.  This already exceeds 6. -/
theorem r2_25 : r2 25 = 12 := by decide

/-- `r2 125 = 16`, confirming the growth `r2 (5^k) = 4 * (k + 1)`. -/
theorem r2_125 : r2 125 = 16 := by decide

/-- The multiplicity of the square-torus eigenvalue `4π²·25` is 12, which is
strictly greater than 6. -/
theorem multiplicity_exceeds_six : 6 < r2 25 := by decide

/-! ### A limited core-Lean shadow of the crystallographic restriction

For a finite-order lattice automorphism (a rotation preserving a planar
lattice) with trace `t`, one has `|t| ≤ 2`, and an automorphism of order `n`
satisfies `2 * cos (n * θ) = 2` where `t = 2 * cos θ`.  The integer recurrence
below computes `2 * cos (n * θ)` exactly from the integer `t`.  Evaluating it
at `n = 32` shows that the only integer traces with `-2 ≤ t ≤ 2` compatible
with the order-thirty-two relation are `t ∈ {-2, 0, 2}`, i.e. rotations by a
multiple of 90°, whose order divides 4.  Hence an order-thirty-two lattice
automorphism is impossible.

The arithmetic core is fully formalised and kernel-checked here; the geometric
identification of `t = -2, 0, 2` with orders dividing 4 is documented only.
-/

/-- `chebPair n t = (2 cos (n θ), 2 cos ((n+1) θ))` where `t = 2 cos θ`,
represented purely over the integers. -/
def chebPair : Nat → Int → Int × Int
  | 0, t => (2, t)
  | n + 1, t =>
      let p := chebPair n t
      (p.2, t * p.2 - p.1)

/-- `cheb n t = 2 cos (n θ)` where `t = 2 cos θ`. -/
def cheb (n : Nat) (t : Int) : Int := (chebPair n t).1

/-- The order-thirty-two relation `cheb 32 t = 2` has no integer solution in
the geometrically allowed trace range `-2 ≤ t ≤ 2` other than `-2, 0, 2`. -/
theorem trace_constraint_of_order_thirtytwo (t : Int)
    (hlo : -2 ≤ t) (hhi : t ≤ 2) (h : cheb 32 t = 2) :
    t = -2 ∨ t = 0 ∨ t = 2 := by
  have hc : t = -2 ∨ t = -1 ∨ t = 0 ∨ t = 1 ∨ t = 2 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact absurd h (by decide)
  · exact Or.inr (Or.inl rfl)
  · exact absurd h (by decide)
  · exact Or.inr (Or.inr rfl)

/-- The refutation of conjecture 00000000277 collected in one statement:
`r2 25 = 12`, that this count strictly exceeds 6, and the core-Lean shadow of
the crystallographic restriction ruling out trace values for an order-32
lattice automorphism other than those of order dividing 4. -/
theorem conjecture_00000000277_false :
    r2 25 = 12
      ∧ 6 < r2 25
      ∧ (∀ t : Int, -2 ≤ t → t ≤ 2 → cheb 32 t = 2 → t = -2 ∨ t = 0 ∨ t = 2) :=
  ⟨r2_25, multiplicity_exceeds_six, trace_constraint_of_order_thirtytwo⟩

end Tlmc277
