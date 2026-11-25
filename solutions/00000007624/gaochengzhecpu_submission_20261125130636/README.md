# Conjecture 00000007624 — Resolution Package

**Verdict:** **False in general** (with a sharp positive theorem for single grade-$1$ vectors in nondegenerate real Clifford algebras).

## Problem Statement

See [`SOURCE.md`](SOURCE.md) for the exact original English and Chinese statements (*The null-vector sum construction of nilpotent formulas / 幂零公式的零向量和构造*).

The conjecture proposes an equivalence chain linking three claims across quadratic spaces $\bigl(V, Q\bigr)$ and their Clifford algebras $\mathrm{Cl}\bigl(V, Q\bigr)$:
1. **Null-vector sum / sum-of-squares construction:** nonzero nilpotent formulas ($z \ne 0$, $z^2 = 0$ or $z^k = 0$) are constructed via sums of null vectors where a sum of squares evaluates to a null vector.
2. **Nilpotent–isotropic equivalence:** the existence of nonzero nilpotent/null elements is equivalent to the existence of a nonzero isotropic vector $v \in V \setminus \lbrace 0 \rbrace$ with $Q(v) = 0$.
3. **Isotropic–signature equivalence:** the existence of a nonzero isotropic vector in $\bigl(V, Q\bigr)$ is equivalent to the indefinite signature condition ($p \ge 1$ and $q \ge 1$).

## Mathematical Resolution Summary

### 1. Restricted Positive Theorems (Where the Intuition Holds)
- **Grade-$1$ Nilpotent–Isotropic Equivalence (`grade1_nilpotent_iff`, `grade1_nilpotent_negSig_iff`):** Over any integral domain $R$ and under either Clifford sign convention $\iota(v)^2 = +Q(v)\cdot 1$ or $\iota(v)^2 = -Q(v)\cdot 1$, a nonzero grade-$1$ vector $v \in V \setminus \lbrace 0 \rbrace$ satisfies $\iota(v)^k = 0$ for some $k \ge 1$ (equivalently $\iota(v)^2 = 0$) if and only if $Q(v) = 0$.
- **Sylvester Signature & Inertia Criteria (`hasIsotropic_sigList_iff`, `hasIsotropic_inertiaList_iff`):** Over $\mathbb{R}$ (and any ordered integral domain $R$ for the Sylvester canonical form $Q_{p,q}$), a nondegenerate quadratic space of signature $\bigl(p, q\bigr)$ admits a nonzero isotropic vector (equivalently, a nonzero grade-$1$ nilpotent in $\mathrm{Cl}_{p,q}$) if and only if $p \ge 1$ and $q \ge 1$. For general inertia $\bigl(p, q, r\bigr)$, a nonzero isotropic vector exists if and only if $\bigl(p \ge 1 \land q \ge 1\bigr) \lor r \ge 1$.
- **Polar Orthogonality Criterion (`null_vector_sum_nilpotent_iff`):** For two null vectors $u, w \in V$ ($Q(u) = Q(w) = 0$), $\iota(u) + \iota(w)$ is nilpotent if and only if $B_Q(u, w) = 0$ (spanning a totally isotropic subspace).

### 2. Three Decisive Counterexample Families (Refuting the Conjecture)
1. **Nonzero Nilpotents in Strictly Positive-Definite Clifford Algebras Under Both Sign Conventions & Sharp Classification:**
   - **`+Q` convention (`refutation_pos_def_plus_conv`):** In $2$-dimensional positive-definite Euclidean space $\bigl(\mathbb{R}^2, x_1^2 + x_2^2\bigr)$ of signature $\bigl(2, 0\bigr)$, there are **zero** nonzero isotropic vectors, yet $\mathrm{Cl}_{2,0}(\mathbb{R}) \cong \mathrm{M}_2(\mathbb{R})$ contains the nonzero multivector nilpotent
     $$x = e_1 + e_1 e_2 \ne 0, \qquad x^2 = 1 + e_2 - e_2 - 1 = 0.$$
   - **`-Q` convention (`refutation_pos_def_minus_conv`):** In $4$-dimensional positive-definite Euclidean space under $\iota(v)^2 = -Q(v)\cdot 1$, there are **zero** nonzero isotropic vectors, yet in $\mathrm{Cl}_{0,4}(\mathbb{R}) \cong \mathrm{M}_2(\mathbb{H})$ ($e_i^2 = -1$), $\bigl(e_1 e_2 e_3\bigr)^2 = +1$ anticommutes with $e_4$, so
     $$y = e_4 + e_1 e_2 e_3 e_4 = \bigl(1 + e_1 e_2 e_3\bigr)e_4 \ne 0, \qquad y^2 = -1 + e_1 e_2 e_3 - e_1 e_2 e_3 + 1 = 0.$$
   - **Complete Classification (`cl_has_nilpotent_iff`):** Over any ordered integral domain $R$, $\mathrm{Cl}_{p,q}(R)$ possesses a nonzero nilpotent element if and only if
     $$\bigl(p, q\bigr) \notin \bigl\lbrace (0, 0),\, (1, 0),\, (0, 1),\, (0, 2),\, (0, 3) \bigr\rbrace.$$
2. **Failure of the Null-Vector Sum Construction (`refutation_null_vector_sum`):**
   - In $\mathrm{Cl}_{1,1}(R)$ ($Q(x_1, x_2) = x_1^2 - x_2^2$), $u = e_1 + e_2$ and $w = e_1 - e_2$ are nonzero null vectors with $\iota(u)^2 = 0$, $\iota(w)^2 = 0$, and $\iota(u)^2 + \iota(w)^2 = 0$, yet $\iota(u) + \iota(w) = 2 e_1$ satisfies $\bigl(\iota(u) + \iota(w)\bigr)^2 = 4 \cdot 1 \ne 0$ — an invertible unit in $\mathrm{Cl}_{1,1}(\mathbb{Q})$ and $\mathrm{Cl}_{1,1}(\mathbb{R})$, never nilpotent of any index $k \ge 1$.
3. **Breakdown of the Signature Condition Across Degenerate Forms and Fields:**
   - **Degenerate semidefinite forms (`refutation_degenerate_semidefinite`):** $Q_{p,0,r}$ with $r \ge 1$ (e.g., $Q(x_1, x_2) = x_1^2 + 0 \cdot x_2^2$) has $q = 0$ (no negative squares), yet admits nonzero isotropic vectors in its radical.
   - **Complex / Gaussian integers & finite fields (`refutation_complex_sum_of_squares`, `refutation_finite_fields_sum_of_squares`):** Pure unsigned sums of squares admit nonzero isotropic vectors: $1^2 + i^2 = 0$ over $\mathbb{Z}[i] \subset \mathbb{C}$; $1^2 + 2^2 \equiv 0 \pmod 5$ over $\mathbb{F}_5$; and $x_1^2 + x_2^2 + x_3^2 \equiv 0 \pmod p$ over every odd prime field $\mathbb{F}_p$ by Chevalley–Warning.
   - **Rational Hasse–Minkowski obstructions (`refutation_hasse_minkowski_indefinite`):** Over $\mathbb{Q}$, real signature is well-defined, yet indefinite forms $x_1^2 - 2 x_2^2$ (signature $\bigl(1, 1\bigr)$) and $x_1^2 + x_2^2 - 3 x_3^2$ (signature $\bigl(2, 1\bigr)$) have **no** nonzero rational isotropic vectors.

## Package Layout & Reproduction

- [`SOURCE.md`](SOURCE.md) — Exact original conjecture statement (unmodified).
- [`main.tex`](main.tex) / [`main.pdf`](main.pdf) — Complete mathematical paper with proofs and Lean cross-reference tables.
- [`verify.py`](verify.py) — Standalone Python 3.12 verification suite (zero external packages).
- [`lean/`](lean/) — Zero-dependency Core Lean 4.19.0 formalization (`moreLeanArgs = ["-DwarningAsError=true"]`, zero `sorry`, zero custom axioms):
  - [`lean/Conjecture00000007624/Algebra.lean`](lean/Conjecture00000007624/Algebra.lean) — Self-contained `AssocRing`, `CommRing`, `IntegralDomain`, `OrderedDomain`, nilpotent index reduction, and concrete `Int`, `GaussInt`, `F3`, `F5` instances.
  - [`lean/Conjecture00000007624/QuadraticForm.lean`](lean/Conjecture00000007624/QuadraticForm.lean) — Diagonal quadratic spaces, polarization identity, and Sylvester signature & inertia theorems.
  - [`lean/Conjecture00000007624/Clifford.lean`](lean/Conjecture00000007624/Clifford.lean) — Recursive $\mathbb{Z}/2\mathbb{Z}$-graded Clifford algebra $\mathrm{Cl}(R, g)$, associativity, $\iota(v)^2 = Q_g(v)\cdot 1$, and grade-$1$ nilpotent–isotropic equivalence.
  - [`lean/Conjecture00000007624/Counterexamples.lean`](lean/Conjecture00000007624/Counterexamples.lean) — Positive-definite nilpotents in $\mathrm{Cl}_{2,0}$ and $\mathrm{Cl}_{0,4}$, complete $5$-exception classification, null-vector sum refutation, degenerate/field counterexamples, Hasse–Minkowski proofs, and concrete `Int` non-vacuity theorems.
- [`verification/`](verification/) — Build and audit logs (`lake-build.log`, `lean-axioms.log`, `lean-version.log`, `pdf-build.log`, `python-verify.log`, `SELF_REVIEW.md`).
