# Disproof of conjecture 00000000140

The proposed edge-weight law is described as the natural-density distribution on all primes. This does not define a countably additive probability distribution on the countably infinite prime set. If every prime singleton had the same mass, a positive mass would make sufficiently large finite sets exceed total mass one; a zero mass would, by countable additivity, give the entire prime set mass zero. Therefore the i.i.d. random edge weights in the statement are not defined as written, so neither is the asserted MST limit.

The Lean project formalizes the finite-additivity obstruction for a positive common atom mass. The report gives the countable-additivity argument for the zero-mass case and the link to the stated probability model. Choosing a particular non-uniform distribution on primes would define a different conjecture.

## Contents

- main.tex, main.pdf: disproof and measure-theoretic explanation.
- lean4/: self-contained Lean 4 project.
- verification.txt: build and axiom audit.
