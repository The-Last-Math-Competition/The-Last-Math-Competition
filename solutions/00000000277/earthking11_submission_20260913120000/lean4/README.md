# Lean formalisation scope (conjecture 00000000277)

Toolchain: `leanprover/lean4:v4.33.1`. Project: `tlmc277`.
Core Lean only (`import Std`); **no Mathlib**, no `sorry`, no `axiom`, no
`native_decide`.

## What is formalised

All of the following are in `Main.lean` and kernel-checked by `lake build`.

### 1. The `r₂` counts (decisive)

`r2 N` counts the ordered integer pairs `(a, b)` with `a*a + b*b = N`, by
enumerating non-negative pairs `0 ≤ a, b ≤ N` and weighting each coordinate by
`2` for a non-zero coordinate and `1` for zero (accounting for the signs). This
is a pure `Nat` computation, so it is fully reducible by the kernel.

* `r2_1   : r2 1 = 4`
* `r2_5   : r2 5 = 8`
* `r2_25  : r2 25 = 12`   ← decisive witness
* `r2_125 : r2 125 = 16`
* `multiplicity_exceeds_six : 6 < r2 25`

`r2_25` together with the analytic correspondence (documented below) says that
the square torus `R²/Z²` has an eigenvalue `4π²·25` of multiplicity `12 > 6`.
The sequence `r2(5^k) = 4(k+1)` (checked for `k = 0..3` in Lean, `k = 0..5` in
`reproduce.py`) is what makes the multiplicity unbounded.

### 2. A limited trace obstruction to order 32

Integer Chebyshev recurrence: `chebPair n t = (2cos(nθ), 2cos((n+1)θ))`
where `t = 2cos θ`, and `cheb n t = 2cos(nθ)`, all over `Int`.

* `trace_constraint_of_order_thirtytwo :`
  `∀ t : Int, -2 ≤ t → t ≤ 2 → cheb 32 t = 2 → t = -2 ∨ t = 0 ∨ t = 2`.

Interpretation: a finite-order rotation preserving a planar lattice has
`|trace| ≤ 2`, and an order-32 rotation would satisfy the order-32 relation
`cheb 32 t = 2`. The lemma shows the only allowed integer traces are
`-2, 0, 2`, i.e. rotations by multiples of 90°, whose order divides 4. So no
order-32 rotation is compatible with the arithmetic.

### 3. Collected statement

`conjecture_00000000277_false` is the conjunction of `r2 25 = 12`,
`6 < r2 25`, and the trace statement above.

## What is NOT formalised (documented only)

These require `ℝ`, `ℂ`, Fourier analysis, or algebraic number theory and are
therefore out of scope for core Lean. They are stated and proved in `main.tex`
and checked numerically in `reproduce.py`.

1. **Eigenvalue–multiplicity correspondence.** That on `R²/Λ` the Laplace
   eigenvalues are `4π²|k|²` (`k ∈ Λ*`) and the multiplicity of `4π²N` is the
   number of dual-lattice vectors of squared length `N`. In particular, that on
   the square torus this multiplicity is `r₂(N)`.
2. **Jacobi's two-square theorem** `r₂(N) = 4(d₁(N) − d₃(N))`, and hence
   `r₂(5^k) = 4(k+1)` for all `k`. In Lean we verify the concrete values
   `k = 0..3` by kernel computation rather than proving the general formula.
3. **The unboundedness conclusion** `M = ∞` (the `r₂` values themselves are
   formalised; the passage from unbounded `r₂` to unbounded spectral
   multiplicity uses item 1).
4. **The full crystallographic restriction**: that a finite-order planar
   lattice automorphism has order in `{1,2,3,4,6}` and that the largest
   automorphism group of a planar lattice has order 12 (dihedral of the
   hexagonal lattice). Only the exact integer Chebyshev core at `n = 32` is
   formalised.
5. **The geometric identification** of traces `-2, 0, 2` with rotations of
   order dividing `4` (i.e. that the corresponding automorphism is `±I` or a
   90° rotation).

## Honest qualification

If `M` were intended as the multiplicity of the **first non-zero** eigenvalue
only, then `6` is correct (hexagonal lattice). This is a mathematical fact
outside the Lean formalisation. The order-32 clause is impossible under both
readings, and the literal reading gives `M = ∞`; hence the conjecture is false
as written.

## Axiom audit

`Check.lean` prints (via `#print axioms`):

```
'Tlmc277.r2_1' does not depend on any axioms
'Tlmc277.r2_5' does not depend on any axioms
'Tlmc277.r2_25' does not depend on any axioms
'Tlmc277.r2_125' does not depend on any axioms
'Tlmc277.multiplicity_exceeds_six' does not depend on any axioms
'Tlmc277.trace_constraint_of_order_thirtytwo' depends on axioms: [propext, Quot.sound]
'Tlmc277.conjecture_00000000277_false' depends on axioms: [propext, Quot.sound]
```

`propext` and `Quot.sound` are standard core axioms; there is no `sorryAx` and
no `Lean.ofReduceBool` (`ofReduceBool`).

## Reproduce

```bash
export PATH="/opt/homebrew/bin:$PATH"
cd lean4
lake build
lake env lean Check.lean
```
