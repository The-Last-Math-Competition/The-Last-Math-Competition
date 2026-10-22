# Disproof of 00000000642: ordinary LKB determinant is not Markov invariant

Over the actual generic field Q(q,t), the standard fraction-field Krammer matrix model has determinant 1 on the two-strand identity and determinant t*q^3 on its positive three-strand Markov stabilization. These are unequal rational functions, in every choice of bases.

Lean constructs the real Artin B2/B3 presentations and their standard matrix representations, checks all invertibility and braid relations, constructs the strand inclusion and positive stabilization, and proves determinant invariance fails on this genuine elementary move. The field is Frac(MvPolynomial (Fin 2) Q); numerical representation specialization is not used.

The standard matrices and their generic conjugacy to the homological LKB representation are documented in [Bigelow, Section 4.2, p.13](https://arxiv.org/abs/math/0204057). Bigelow's sign convention is used. The topological homology identification is explained as a primary-source definition bridge; it is not reconstructed in Lean. The elementary Markov stabilization is the usual inclusion(b)*sigma_n, as in [Bigelow–Ramos–Yi, printed p.1250114-4](https://web.math.ucsb.edu/~bigelow/publications/15.pdf).

This refutes the explicit unnormalized determinant necessary condition. The source gives no normalization, and this submission makes no independent Jones-value or kernel claim. It does not assert anything about every possible additional correction.

## Reproduce

From lean/ with elan installed:

```sh
lake exe cache get
bash verify.sh
```

Lean 4.33.0 / Mathlib db584cd6d46c92f209a44c0f1c829460d327499d are pinned. A new root build, nineteen transitive axiom audits and full official leanchecker --fresh Main replay are required. Complete LaTeX/PDF and source-bound receipts accompany the proof. No sorry, native_decide or extra axiom. Worker and separate supervising AI agents review the source/report/PDF; organizer acceptance is pending.
