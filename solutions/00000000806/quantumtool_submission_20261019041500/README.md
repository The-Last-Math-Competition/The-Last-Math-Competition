# Disproof of conjecture 00000000806

Under the standard convention that Laplace eigenvalues are listed with multiplicity, the union of two congruent disjoint disks has a repeated first eigenvalue. Thus `lambda_1 = lambda_2`, the spectral gap is zero, and the ratio is zero rather than the claimed `3/4`.

The LaTeX report explains the direct-sum spectral argument. The Lean 4 project verifies the repeated-eigenvalue gap and the rational arithmetic contradiction. It uses no `sorry`, `admit`, `native_decide`, or custom axioms.

## Contents

- `main.tex`, `main.pdf`: disproof report.
- `lean4/`: self-contained Lean 4.33.1 project.
- `verification.txt`: build and axiom audit.
