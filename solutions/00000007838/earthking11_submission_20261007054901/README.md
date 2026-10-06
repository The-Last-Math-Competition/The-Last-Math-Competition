# Disproof of conjecture 00000007838

## Result and scope

The conjecture names the displayed set `{0, 2, 4, ...}` as a hyperelliptic Weierstrass semigroup. Read literally, this is the set of all nonnegative even integers. Its complement contains every positive odd integer and is therefore infinite. A Weierstrass semigroup on a genus-`g` curve is a numerical semigroup and has only finitely many gaps (in fact, exactly `g`). Thus the named set cannot be a Weierstrass semigroup, so the conjecture's asserted example does not exist as stated. This already disproves the full conjunction; the other clauses need not be addressed.

The Lean formalization treats the ellipsis as the standard unbounded set of even natural numbers and formalizes the necessary finite-complement condition for a Weierstrass semigroup. It proves directly that no such semigroup can equal that set. It does not replace the statement with the corrected finite-genus hyperelliptic semigroup. If that was intended, the problem needs to be revised before it can be assessed under that different reading.

## Files and verification

- `solution.tex` and `solution.pdf`: mathematical explanation and scope.
- `lean/`: self-contained Lean 4 project with the formal proof and axiom checks.
- `BUILD_AUDIT.md`: exact toolchain, dependency revision, and verification results.

From `lean/`, run:

```text
lake build
lake env lean Check.lean
```
