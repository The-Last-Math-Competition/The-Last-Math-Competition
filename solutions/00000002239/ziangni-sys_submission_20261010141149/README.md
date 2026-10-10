# Disproof of 00000002239

Two distinct nonconstant meromorphic functions share the four finite small functions enumerated by the source, counting multiplicities. The omitted targets have empty divisors; the other two have identical preimages and actual analytic vanishing orders, proved using nonvanishing local analytic units.

- `report.tex`, `report.pdf`: complete mathematical argument and pole interpretation.
- `lean/Main.lean`: actual complex exponential quotients, Mathlib meromorphy and analytic orders, exact shared divisors, distinctness, and the canonical constant-characteristic/little-o calculation.
- `VERIFICATION.md`: validation record.

## Reproduce

Install Lean 4.19.0 with elan, enter `lean/`, and run `lake build`. The project pins Mathlib to `c44e0c8ee63ca166450922a373c7409c5d26b00b`; all dependencies are public Git sources. Local caches and build products are excluded.

The source lists a1, a2, a3, a5, which is four targets. This submission refutes that assertion and does not refute a five-value uniqueness theorem.
