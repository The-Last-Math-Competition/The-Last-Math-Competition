# Disproof of conjecture 00000007615

## Result

The dimension-only double-star sign law stated in the conjecture fails for the standard Hodge star of a two-dimensional pseudo-Riemannian space of signature `(1,1)`. On one-forms the actual star squares to `+1`, whereas the stated exponent `p(n-p)` gives `(-1)^(1·1) = -1`.

## The actual object and definition

Work on the real covector space `V* = ℝ²`, with oriented basis `e₁,e₂`, volume form `e₁ ∧ e₂`, and inverse-metric pairing

`⟨(a,b),(c,d)⟩ = -ac + bd`.

The diagonal entries `(-1,+1)` give signature `(1,1)`. The coefficient of the wedge product relative to the chosen volume form is

`(a,b) ∧ (c,d) = ad - bc`.

Define the Hodge star by its standard characterization

`α ∧ ⋆β = ⟨α,β⟩ (e₁ ∧ e₂)`

for all covectors `α,β`. Solving this identity gives `⋆(c,d)=(-d,-c)`. The Lean file verifies the defining identity for every pair, proves uniqueness of the map satisfying it, and proves `(⋆⋆)(a,b)=(a,b)`.

For `e₁=(1,0)`, the conjectured dimension-only exponent is `1·(2−1)=1`, so its predicted result is `−e₁`; the actual result is `+e₁`. These vectors differ, giving a concrete counterexample to the stated sign law and therefore to the conjecture as written.

## Scope

The conjecture does not specify a positive-definite metric or restrict the Hodge star to Riemannian manifolds. This counterexample uses the standard pseudo-Riemannian Hodge star and states that scope explicitly. It does not disprove the separate identity restricted to positive-definite Riemannian metrics; adding that restriction would change the problem statement.

## Verification

- Lean: `leanprover/lean4:v4.33.1`
- Mathlib: `0df444a360eaa60ab8c11dca51a86af692955474`
- Build: run `cd lean && lake build`
- Axiom audit: run `cd lean && lake env lean Check.lean`
- The audited theorems use only the standard dependencies `propext`, `Classical.choice`, and `Quot.sound`; none has `sorryAx` or a custom axiom.
- The full derivation and exact correspondence with the conjecture are in `solution.tex` and `solution.pdf`.
