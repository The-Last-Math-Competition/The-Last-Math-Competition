# Disproof of conjecture 00000000143

The conjecture asks for independent uniform choices of primes. There is no uniform probability distribution on the countably infinite set of primes: if every prime singleton has the same mass, that mass must be zero (or the sum of infinitely many equal positive masses exceeds one), and zero singleton masses sum to total mass zero on a countable space. Thus the stated random experiment is not defined, so the claimed probability-one equivalence cannot hold as written.

The Lean 4 project formalizes the finite-additivity obstruction for equal positive rational atom masses p/q: no such mass can keep every finite partial sum bounded by total probability one. The paper gives the countable-additivity and Archimedean argument for arbitrary positive real masses, then applies it to the primes. Lean does not formalize that measure-theoretic bridge or prime countability. No sorry, admit, native_decide, or custom axioms are used.

## Contents

- main.tex, main.pdf: disproof and measure-theoretic explanation.
- lean4/: self-contained Lean 4 project.
- verification.txt: build and axiom audit.
