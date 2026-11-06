# Disproof of 00000000644: the explicit Burau spectral condition fails

At the nonzero real parameter t = 3/4, the actual standard three-strand Burau generator sigma1 has the complex eigenvalue -3/4, below the source's required real-part bound -1/2. Both reduced and unreduced representations are covered, including every invertible complex change of basis.

Lean defines the actual Artin B3 presentation, checks the standard generator determinants and braid relations for every nonzero complex parameter, and constructs genuine homomorphisms to GL2(C) and GL3(C). Nonzero complex eigenvectors give actual Mathlib HasEigenvalue results. A general conjugacy theorem preserves those eigenvalues, and the final theorems negate the universal spectral requirement over legal real specializations.

The reduced matrices are exactly [Morier-Genoud, Ovsienko and Veselov, equation (1.1), pp.1–2](https://arxiv.org/abs/2309.04240). The unreduced blocks are [Kassel–Turaev, Braid Groups, Section3.1.1, pp.93–94](https://web.math.ucsb.edu/~bigelow/books/kasselturaev.pdf). The chosen parameter has imaginary part zero and real part strictly between zero and one.

This refutes the explicit spectral necessary clause. It does not claim to refute mere positivity of an ordinary character trace or to build the LKB/Floer/volume models. Any basis of the same Burau representation is covered by the formal conjugacy argument.

## Reproduce

From lean/ with elan installed:

```sh
lake exe cache get
bash verify.sh
```

Lean 4.33.0 and Mathlib db584cd6d46c92f209a44c0f1c829460d327499d are pinned. New Main build, twenty-three transitive axiom audits and full official leanchecker --fresh Main replay are required. LaTeX/PDF, source-bound receipts, logs and hashes accompany the submission. No sorry, native_decide or extra axiom. Worker and supervising AI agents reviewed the formal chain/report/PDF. Organizer acceptance is pending.
