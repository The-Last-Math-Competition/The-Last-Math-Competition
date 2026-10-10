import Mathlib

/-! Formal statement for Conjecture1305: definitions only, ending in `Claim`. Split verbatim from the marked block of `Basic.lean`. -/

-- STATEMENT BEGIN
namespace C1305

open Metric

/-- "the domain in C^2 whose complement is the lattice Z^2": `D = C^2 \ Z^2`
(`Z^2` is the set of points `(m, n)` with `m, n` integers). -/
def D : Set (ℂ × ℂ) := {z | ∀ m n : ℤ, z ≠ ((m : ℂ), (n : ℂ))}

/-- Poincare distance of the unit disc (curvature `-4` normalisation),
`ρ(a,b) = artanh |(a-b)/(1 - conj a * b)| = (1/2) log ((1+x)/(1-x))`. Other normalisations differ by a
positive constant factor and do not change vanishing or positivity. -/
noncomputable def poincare (a b : ℂ) : ℝ :=
  Real.artanh ‖(a - b) / (1 - (starRingEnd ℂ) a * b)‖

/-- A holomorphic disc in `D`: a map holomorphic on the open unit disc with values in `D`. -/
def IsDisc (f : ℂ → ℂ × ℂ) : Prop :=
  DifferentiableOn ℂ f (ball 0 1) ∧ Set.MapsTo f (ball 0 1) D

/-- `Chain p q c`: a finite chain of holomorphic discs in `D` from `p` to `q` of total Poincare
length `c` (the empty chain joins `p` to `p` with length `0`; each link is a disc `f` with
`f a = q'`, `f b = r` for `a, b` in the unit disc, costing `ρ(a,b)`). -/
inductive Chain : ℂ × ℂ → ℂ × ℂ → ENNReal → Prop
  | refl (p : ℂ × ℂ) : Chain p p 0
  | step {p q r : ℂ × ℂ} {c : ENNReal} (f : ℂ → ℂ × ℂ) (a b : ℂ) :
      Chain p q c → IsDisc f → a ∈ ball (0 : ℂ) 1 → b ∈ ball (0 : ℂ) 1 → f a = q → f b = r →
      Chain p r (c + ENNReal.ofReal (poincare a b))

/-- "The Kobayashi metric d_K" (the Kobayashi pseudodistance of `D`): the infimum of the lengths of
all finite holomorphic disc chains in `D` from `p` to `q` (`⊤` if there is none). -/
noncomputable def dK (p q : ℂ × ℂ) : ENNReal := sInf {c | Chain p q c}

/-- Reading A: first coordinate is "horizontal", second is "vertical": `d_K` degenerates
horizontally (vanishes between points with equal second coordinate) and does not degenerate
vertically (positive between distinct points with equal first coordinate). -/
def ReadingA : Prop :=
  (∀ p ∈ D, ∀ q ∈ D, p.2 = q.2 → dK p q = 0) ∧
  (∀ p ∈ D, ∀ q ∈ D, p.1 = q.1 → p ≠ q → 0 < dK p q)

/-- Reading B: the same with the roles of the two coordinates exchanged. -/
def ReadingB : Prop :=
  (∀ p ∈ D, ∀ q ∈ D, p.1 = q.1 → dK p q = 0) ∧
  (∀ p ∈ D, ∀ q ∈ D, p.2 = q.2 → p ≠ q → 0 < dK p q)

/-- The conjecture: "d_K degenerates in the horizontal direction but not in the vertical direction",
in either assignment of the names horizontal/vertical to the two coordinates. -/
def Conjecture : Prop := ReadingA ∨ ReadingB

/-- What this package proves: neither reading holds, and in fact `d_K` vanishes between any two
points of `D` (so no reading asking for positive distance anywhere can hold). -/
def Claim : Prop := ¬ Conjecture ∧ (∀ p ∈ D, ∀ q ∈ D, dK p q = 0)

end C1305
-- STATEMENT END
