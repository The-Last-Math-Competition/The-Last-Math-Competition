import Std

/-!
# Disproof of conjecture 00000000982

Conjecture (file `conjectures/00000000982.md`):

> Fixed points of the Berezin transform on Fock space are radial functions,
> and the cardinality of the fixed-point set is at most 2.

We refute both claims.  On the Fock space with the Gaussian measure
`(1/π) e^{-|w|²} dA(w)`, the (diagonal) Berezin transform is the Gaussian
convolution
`B f(z) = (1/π) ∫ f(w) e^{-|w-z|²} dA(w) = e^{Δ/4} f(z)`,
and it fixes every holomorphic function in `F²` (every holomorphic function is
harmonic, and `e^{Δ/4}` acts as the identity on harmonic functions).  In
particular:

* `f(z) = z` lies in `F²` (with `‖z‖² = 1`), is fixed, and is **not** radial:
  `|1| = |i| = 1` but `f(1) = 1 ≠ i = f(i)`;
* `1, z, z², z³, …` are all fixed and pairwise distinct, so the fixed-point set
  is infinite and cannot have cardinality `≤ 2`.

## Scope of this file

Core Lean 4 has no `ℝ`/`ℂ` and no integrals, so this file cannot formalise the
Fock-space integral itself.  It formalises, over the integer lattice
`ℤ × ℤ ⊂ ℂ` (which is enough for the distinguishing evaluations), the two
structural facts the refutation turns on:

* `z_not_radial` / `nonradial_witness`: there are two lattice points with equal
  squared modulus whose values under `z ↦ z` differ;
* `three_distinct_functions`: `1`, `z`, `z²` are pairwise distinct functions.

The analytic inputs — the convolution identity `B = e^{Δ/4}` and the fact that
`B` fixes every holomorphic function in `F²` — are proved in `main.tex` and
verified numerically in `reproduce.py`.

Everything below is proved in core Lean 4 (`import Std` only, no Mathlib, no
`sorry`, no `axiom`, no `native_decide` / `ofReduceBool`).
-/

set_option maxRecDepth 100000

namespace Tlmc982

/-- Squared modulus `|p|² = x² + y²` on the integer lattice `ℤ × ℤ ⊂ ℂ`. -/
def sqmod (p : Int × Int) : Int := p.1 * p.1 + p.2 * p.2

/-- The literal radiality predicate on `Int`-valued functions: `g` is radial
when it is constant on squared-modulus level sets. -/
def RadialInt (g : Int × Int → Int) : Prop :=
  ∀ p q : Int × Int, sqmod p = sqmod q → g p = g q

/-- Radiality for a function with values in an arbitrary type.  Instantiating
`α = Int` recovers the literal `RadialInt` definition above; the general
codomain lets us test the `ℂ`-valued coordinate functions, which we model as
`Int × Int`-valued (real and imaginary parts). -/
def Radial {α : Type} (g : Int × Int → α) : Prop :=
  ∀ p q : Int × Int, sqmod p = sqmod q → g p = g q

/-- The lattice model of the coordinate function `z ↦ z`: the identity. -/
def idZ (p : Int × Int) : Int × Int := p

/-- The lattice model of the constant function `1 = 1 + 0i`. -/
def constOne (_ : Int × Int) : Int × Int := (1, 0)

/-- The lattice model of `z ↦ z²`, in coordinates
`(x, y) ↦ (x² − y², 2xy)`. -/
def sqZ (p : Int × Int) : Int × Int :=
  (p.1 * p.1 - p.2 * p.2, 2 * p.1 * p.2)

/-! ### `z` is not radial -/

/-- The distinguishing computation: `(1,0)` and `(0,1)` have the same squared
modulus `1` but are distinct. -/
theorem nonradial_witness :
    ∃ p q : Int × Int, sqmod p = sqmod q ∧ p ≠ q := by
  refine ⟨(1, 0), (0, 1), ?_, ?_⟩ <;> decide

/-- The coordinate function `z` is **not** radial: `(1,0)` and `(0,1)` have
equal squared modulus, but `z` takes the values `(1,0) ≠ (0,1)` on them. -/
theorem z_not_radial : ¬ Radial idZ := by
  intro h
  have hs : sqmod (1, 0) = sqmod (0, 1) := by decide
  have hv : idZ (1, 0) = idZ (0, 1) := h (1, 0) (0, 1) hs
  exact absurd hv (by decide)

/-! ### `1`, `z`, `z²` are pairwise distinct -/

theorem one_ne_z : constOne ≠ idZ := by
  intro h
  have hv : constOne (0, 0) = idZ (0, 0) := by rw [h]
  exact absurd hv (by decide)

theorem one_ne_sq : constOne ≠ sqZ := by
  intro h
  have hv : constOne (0, 0) = sqZ (0, 0) := by rw [h]
  exact absurd hv (by decide)

/-- `z` and `z²` differ at `(2,0)`: `(2,0) ≠ (4,0)`. -/
theorem z_ne_sq : idZ ≠ sqZ := by
  intro h
  have hv : idZ (2, 0) = sqZ (2, 0) := by rw [h]
  exact absurd hv (by decide)

/-- Three pairwise distinct functions `1`, `z`, `z²`. -/
theorem three_distinct_functions :
    constOne ≠ idZ ∧ constOne ≠ sqZ ∧ idZ ≠ sqZ :=
  ⟨one_ne_z, one_ne_sq, z_ne_sq⟩

/-! ### The conjecture is false -/

/-- Conjecture 00000000982 is false: the fixed-point candidate `z` (which the
analytic part fixes, `Bz = z`) is not radial, and there are at least three
(hence more than two) pairwise distinct such functions `1, z, z²`.  The
analytic input `Bz = z = B(z²)` is established in `main.tex` and checked in
`reproduce.py`. -/
theorem conjecture_00000000982_false :
    (¬ Radial idZ) ∧
    (∃ p q : Int × Int, sqmod p = sqmod q ∧ p ≠ q) ∧
    constOne ≠ idZ ∧ constOne ≠ sqZ ∧ idZ ≠ sqZ :=
  ⟨z_not_radial, nonradial_witness, one_ne_z, one_ne_sq, z_ne_sq⟩

end Tlmc982
