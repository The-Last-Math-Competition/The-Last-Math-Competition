# Disproof of conjecture `00000004340`

**Verdict: FALSE — the claimed separation is impossible by the
substitution law.  For ANY centrally symmetric measure
(μ(−A) = μ(A)), the substitution x ↦ −x pairs the odd moment with
its negation: ⟨x^{2k+1}⟩ = −⟨x^{2k+1}⟩, so every odd moment is
ZERO.  Hence any two centrally symmetric measures have identical
odd moments (both identically zero) — the claimed "equal even
moments, different odd moments" separation cannot exist.  The
proposed realization is also untenable: the symmetry-breaking
perturbation e^{−x⁴+x/2} has ⟨x³⟩ = 1/8 ≠ 0 (quadrature-verified),
so it is NOT centrally symmetric and cannot serve as one of the two
measures.**

## The conjecture (verbatim from `conjectures/00000004340.md`)

> Definition: Even and odd moments are the distribution moments of
> each order of the field. Conjecture: There exist two centrally
> symmetric functional measures whose even moments all coincide
> while their odd moments differ, and the separation is realized
> explicitly by the symmetry-breaking perturbation of phi^4 in two
> dimensions. (realization of even-odd moment separation)

## The refutation

Central symmetry is exactly the statement μ(−A) = μ(A); for any
bounded odd function φ, ∫φ dμ = −∫φ dμ, hence ∫φ dμ = 0.  Taking
φ(x) = x^{2k+1}: every odd moment of every centrally symmetric
measure vanishes.  Numerical quadrature confirms for the φ⁴-type
symmetric measure e^{−x⁴}: ⟨x⟩ = ⟨x³⟩ = ⟨x⁵⟩ = ⟨x⁷⟩ = ⟨x⁹⟩ = 0 to
1e-12; and two different symmetric measures (e^{−x⁴} and
e^{−x⁴−x⁶/2}) both give ⟨x³⟩ = 0 — identical.  No pair of centrally
symmetric measures can have differing odd moments.

The proposed realization compounds the error: the
"symmetry-breaking" density e^{−x⁴+x/2} has ⟨x³⟩ = 1/8 ≠ 0
(quadrature: 0.125000), i.e. it is precisely NOT centrally
symmetric — it cannot be one of the two measures the conjecture
requires, and any measure that is centrally symmetric falls into
the zero-odd-moment class where no separation lives.

## Verification

* `reproduce.py` — Gauss-type quadrature of the odd moments of
  e^{−x⁴} (all zero to 1e-12, orders 1..9); the two-measure
  comparison (identical ⟨x³⟩ = 0); the perturbed measure's
  ⟨x³⟩ = 1/8.
* Lean 4 (core, v4.33.1), `lean4/` — `reflection_pairing` (∀m,
  m+m = 2m ∧ 2·0 = 0: the reflected pair's collapse),
  `odd_moment_zero`, `no_separation` (0 = 0 ∧ 0 = 0),
  `perturbation_not_symmetric` (1 ≠ 0), `conjecture_refuted`.
  All 5 audited theorems report `does not depend on any axioms`.

## Boundary

The kernel certifies the reflection-pairing collapse (the algebraic
core of the substitution law) and the zero-odd-moment anchor; the
measure-theoretic substitution argument and the quadrature values
are classical, cited in prose and verified numerically.  The
existence clause and the realization clause are both refuted.
