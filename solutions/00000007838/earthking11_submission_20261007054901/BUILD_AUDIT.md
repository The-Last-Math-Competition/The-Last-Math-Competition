# Verification audit

- Lean toolchain: `leanprover/lean4:v4.33.1`.
- Mathlib revision: `0df444a360eaa60ab8c11dca51a86af692955474`, pinned in the Lake configuration and manifest.
- `lake build`: passed on 2026-10-07.
- `lake env lean Check.lean`: passed. `#print axioms` for `evenNumbers_compl_infinite`, `no_literal_hyperelliptic_star_semigroup`, and `literal_example_clause_false` reports only `[propext, Classical.choice, Quot.sound]`, with no `sorryAx` or user-declared axioms.
- A source scan found no uses of `sorry`, `admit`, `native_decide`, or custom axioms.
- No brute-force computation is required. The proof establishes that all odd naturals lie outside the specified even-number set and that there are infinitely many odd naturals.
- Semantic scope: the result uses the literal set `{0,2,4,...}` and the standard finite-gap condition for Weierstrass semigroups. It does not claim a numerical invariant for a corrected, finite-genus hyperelliptic semigroup.
