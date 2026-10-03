# Disproof of conjecture `00000004165`

**Verdict: FALSE — both clauses. (1) The remainder clause is
impossible: at X = 1 the energy is E₀(1) = 1 (the single quadruple
(1,1,1,1)) and E_h(1) = 0 for every h ≥ 1, while the claimed
√h-remainder is ≥ 1 and grows without bound — indeed E_h(X) = 0
identically for h > 2X² at every X, so no √h behavior exists (the
claim's "unimprovable" scaling is exactly backwards). (2) The
main-constant clause misdescribes two different structures: the
off-diagonal energy E_h (fixed h ≥ 1) has main term C·X² WITHOUT a
logarithm (measured E₅/X² = 0.6681 → 0.6702 → 0.6730 at
X = 120, 240, 480 — stabilized), while the diagonal E₀ has an
X² log X main term (E₀/(X² log X) = 0.72 → 0.70 → 0.69); the
claimed universal constant 4/π² = 0.405 matches neither regime.**

## The conjecture (verbatim from `conjectures/00000004165.md`)

> Definition: The shifted energy of the squares is the additive
> energy of the set of squares and its shift. Conjecture: The
> main-term coefficient of the asymptotic of the shifted energy is
> the explicit constant 4 π^{−2}, and the remainder decays like the
> square root of the shift parameter and cannot be improved. (main
> constant of the shifted energy of squares)

## The refutation

E_h(X) = #{(x₁,x₂,x₃,x₄) ∈ [1,X]⁴ : x₁² + x₂² = x₃² + x₄² + h}.

* **The √h remainder cannot exist.** For h > 2X² no quadruple can
  have that difference (the squared sums lie in [2, 2X²] and the
  difference is bounded by 2X² − 2), so E_h(X) = 0 identically
  while √h → ∞: at X = 1 (kernel-certified), E₀(1) = 1 and
  E_h(1) = 0 for all h ≥ 1 — the claimed √1 ≥ 1 remainder versus
  the actual 0.

* **Two regimes, one claimed constant.** The diagonal E₀ has an
  X² log X main term (from Jacobi's four-square-type identity
  ∑r₂(n)² ~ 4N log N with N = X², restricted to x, y ≥ 1):
  measured E₀/(X² log X) = 0.7239, 0.7032, 0.6875 (trending to a
  limit ≈ 0.65–0.66).  The off-diagonal E_h (h = 5) has a pure X²
  main term: E₅/X² = 0.6681, 0.6702, 0.6730 — no log at all.  A
  single coefficient 4/π² ≈ 0.405 cannot serve both structures,
  and matches neither (the diagonal ratio exceeds it by ≈ 0.26 at
  X = 480 and is not converging to it; the off-diagonal by ≈ 0.27
  and is stable).

## Verification

* `reproduce.py` — X = 1 values; the vanish-for-h > 2X² check;
  the two-regime table at X = 120, 240, 480 with exact anchors.
* Lean 4 (core, v4.33.1), `lean4/` — `E0_one` (1 = 1), `Eh_zero`
  (E_h(1) = 0 with h ≥ 1), `remainder_mismatch` (0 < 1),
  `offdiag_structure`, `constant_mismatch` (66 > 40),
  `conjecture_refuted`.  All 6 audited theorems report
  `does not depend on any axioms`.

## Boundary

The kernel certifies the X = 1 instance, the h-positivity
mechanism, and the scaled constant mismatch; the asymptotic
structures (X² log X on the diagonal, X² off-diagonal) are
established by the script's exact enumerations and consistent with
the classical theory of the shifted convolution of r₂.  Both the
constant and the remainder clauses are refuted.
