# Disproof of conjecture 00000000650

The counterexample is the trefoil `T(2,3)`, whose bridge number is 2 and Seifert genus is 1. Substitution makes each proposed lower bound read `2 >= 3`. The PDF gives the standard knot-theoretic justification of these invariants; the Lean project verifies both formulas and the arithmetic contradiction.

## Contents

- `main.tex`, `main.pdf`: proof report.
- `lean4/`: Lean 4.33.1 project (`Main.lean`, `Check.lean`).
- `verification.txt`: build and axiom audit.
