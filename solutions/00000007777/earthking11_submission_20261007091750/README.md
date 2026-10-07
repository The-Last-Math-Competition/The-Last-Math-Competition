# Disproof of conjecture 00000007777

The conjecture defines `m_n` as the minimum canonical height of points of exact period `n` and proposes a positive lower bound `m_n ≥ c d^n/n` for every non-PCF polynomial. A period-one point already contradicts the claimed lower bound, because its canonical height is zero.

We use the explicit degree-2 polynomial `P(X)=X²+6X` over `AlgebraicClosure ℚ`. Its critical point `-3` has rational orbit `-3 → -9 → 27 → 891 → ...`; after reaching 27 the orbit is strictly increasing. Thus `P` is non-PCF. On the other hand, `0` is an exact fixed point. Its canonical height, defined from the standard rational logarithmic height `log max(|numerator|,denominator)` by the usual degree-normalized orbit limit, is zero. Consequently no positive `c` can satisfy the conjectured inequality at `n=1`.

The Lean theorem `TLMC7777.counterexample` includes the degree, actual non-PCF proof in the algebraic closure, fixed-point check, and failure of the positive lower bound on rational fixed points. A lower bound for `m_1` would imply that bound for every fixed point, including the rational point `0`.

## Reproduce

From `lean/`, run `lake build`. Lean and Mathlib are locked by `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json`. The final theorem's `#print axioms` appears in `Main.lean`.
