# Disproof of conjecture 00000000114

The conjecture states convergence to an exponential law for the raw consecutive prime gaps. Under the usual empirical interpretation, each coordinate of each gap vector is a positive integer. Its empirical distributions are therefore supported on the integer lattice, so they cannot converge weakly to a continuous exponential law. For example, the open interval (1/4, 1/2) contains no integer, so every empirical gap distribution assigns it mass zero, while every exponential distribution assigns it positive mass. The customary prime-gap conjecture concerns gaps normalized by a growing scale such as log p_n; that normalization is absent here.

The Lean 4 project checks the arithmetic core that no natural number lies strictly between 1/4 and 1/2 (after multiplying by four). The report supplies the weak-convergence and marginalization argument; those measure-theoretic facts are not formalized in Lean. No sorry, admit, native_decide, or custom axioms are used.

## Contents

- main.tex, main.pdf: disproof and explanation of the missing normalization.
- lean4/: self-contained Lean 4 project.
- verification.txt: build and axiom audit.
