# Disproof of 00000004858: the infinite cyclic obstruction

The literal unqualified construction of a free rank-two nonabelian subgroup in every torsion-free hyperbolic group fails for the actual infinite cyclic group. This submission does not refute a non-elementary version or a conditional task with an existing free subgroup supplied.

Lean defines the actual shortest length of signed integer words by an infimum, proves the universal lower bound and an attaining word, identifies the resulting distance with the standard integer metric, and verifies Gromov's four-point condition with constant zero. The genuine Cayley adjacency and finite generating set are also checked. Torsion freeness is proved. Actual reduced free-group words then exclude every injective homomorphism from FreeGroup (Fin 2) to Multiplicative Z and every isomorphism to any actual subgroup of that group.

The standard group definition and rank-one free example are documented in [Drutu and Kapovich, author manuscript, Definition 11.120 / Example 11.121, printed p.407](https://www.math.ucdavis.edu/~kapovich/EPR/ggt.pdf). The exact metric four-point condition is [Nica and Spakula, arXiv1408.0250v2, Definition 2.1, printed p.2](https://arxiv.org/abs/1408.0250v2); their later non-elementary group convention is explicitly distinguished from the unrestricted competition statement.

## Reproduce

From lean/ with elan installed:

```sh
lake exe cache get
bash verify.sh
```

Lean 4.33.0 / Mathlib db584cd6d46c92f209a44c0f1c829460d327499d are pinned. A new root build, every theorem's transitive axiom audit, and full official leanchecker --fresh Main replay are required. Full LaTeX/PDF and source-bound logs and receipts accompany this proof. No sorry, native_decide or extra axiom. Worker and separate supervising AI agents reviewed the source/report/PDF. Organizer acceptance is pending.
