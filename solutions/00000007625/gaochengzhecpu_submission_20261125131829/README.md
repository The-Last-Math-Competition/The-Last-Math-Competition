# Conjecture 00000007625 — Minimal-Ideal-Count Idempotent Decomposition

## Verdict: **FALSE** (Disproved)

### Problem Statement (`SOURCE.md`)

> **English.** Definition: Idempotents as projection structure. Conjecture: The count law of idempotent decompositions is the minimal-ideal count; the realization of minimality is the matrix factor; and the minimal realization of matrix factors is the center decomposition. (minimal-ideal-count idempotent decomposition)
>
> **中文。** 定义：幂等元为投影结构。猜想：幂等分解的个数律为极小理想数；且极小的实现为矩阵因子；且矩阵因子的极小实现为中心分解。（幂等分解极小理想数）

---

## Mathematical Summary

Conjecture `00000007625` links three structural assertions for idempotent projections $e^2 = e$ in a unital associative ring or Clifford algebra $R$:

1. **Clause I (Count Law):** The count law of idempotent decompositions equals the minimal-ideal count.
2. **Clause II (Matrix-Factor Realization):** Minimality is realized by matrix factors.
3. **Clause III (Center Decomposition):** The minimal realization of matrix factors is the center decomposition.

We establish **both** the exact Wedderburn–Artin positive regime in which a restricted central-block version holds **and** complete counterexamples refuting all three clauses as stated across noncommutative matrix / split Clifford algebras, division Clifford algebras, and degenerate / non-semisimple algebras.

### 1. Positive Non-Vacuity Theorem (Central Blocks & Split Commutative Algebras)

Let $R$ be a unital ring admitting a decomposition $1 = c_1 + \dots + c_t$ into pairwise orthogonal simple central blocks $c_j \in Z(R)$ (such as any semisimple Artinian ring $R \cong \bigoplus_{j=1}^t M_{n_j}(D_j)$). Then:

- Each block $B(c_j) = R c_j$ is a minimal nonzero **two-sided** ideal, and the minimal nonzero two-sided ideals of $R$ have exact cardinality $m_{\mathrm{two}}(R) = t$.
- The central-primitive idempotents of $R$ are precisely $\{c_1, \dots, c_t\}$, the unordered center decomposition of $1$ is unique, and every central-primitive orthogonal decomposition of $1$ has exact summand length $t = m_{\mathrm{two}}(R)$.
- In split commutative semisimple algebras $R = K^t$ ($t \ge 1$, e.g. $\mathrm{Cl}_{1,0}(\mathbb{F}_3) \cong \mathbb{F}_3 \times \mathbb{F}_3$), every idempotent is central, minimal left ideals coincide with minimal two-sided ideals, and the primitive decomposition length satisfies $r(K^t) = m_{\mathrm{two}}(K^t) = m_{\mathrm{left}}(K^t) = t$ (though even on $K^t$, the number of distinct unordered primitive decompositions is $N_{\mathrm{unord}} = 1 \neq t$ for $t \ge 2$, and ordered is $N_{\mathrm{ord}} = t! \neq t$ for $t \ge 3$).

### 2. Master Six-Way Separation on $\mathrm{Cl}_{1,1}(\mathbb{F}_3) \cong M_2(\mathbb{F}_3)$ and Infinite Family on $M_2(\mathbb{Q})$

Over **every** integral domain $D$, nontrivial idempotents of $M_2(D)$ are characterized characteristic-freely by $\mathrm{tr}(e) = 1$ and $\det(e) = 0$; any two nonzero orthogonal idempotents sum to $I_2$; every nontrivial idempotent is primitive; and every primitive orthogonal decomposition $I_2 = e_1 + \dots + e_r$ has exact length $r = 2$. Over any field $K$, $M_2(K)$ is a simple ring ($m_{\mathrm{two}} = 1$) with $Z\bigl(M_2(K)\bigr) = K \cdot I_2$ ($t = 1 \neq 2 = r$).

On the split Clifford algebra $R = \mathrm{Cl}_{1,1}(\mathbb{F}_3) \cong M_2(\mathbb{F}_3)$, all candidate invariants separate strictly:

$$m_{\mathrm{two}}(R) = 1 \;\lt\; r(R) = 2 \;\lt\; m_{\mathrm{left}}(R) = 4 \;\lt\; N_{\mathrm{unord}}(R) = 6 \;\lt\; N_{\mathrm{ord}}(R) = 12 \;\lt\; |E(R)| = 14.$$

Including non-primitive orthogonal decompositions gives $N_{\mathrm{unord}}^{\mathrm{all}}(R) = 7$ and $N_{\mathrm{ord}}^{\mathrm{all}}(R) = 13$, while $|E(R) \setminus \{0\}| = 13$ and $m_{\mathrm{left}}(R) + m_{\mathrm{right}}(R) = 8$. Since

$$\{2, 6, 7, 12, 13, 14\} \cap \{1, 4, 8\} = \emptyset,$$

**Clause I fails under every interpretation** of both the idempotent decomposition count law and the minimal-ideal count. Over $\mathbb{Z}$ and characteristic-zero fields such as $\mathbb{Q}$ ($\mathrm{Cl}_{1,1}(\mathbb{Q}) \cong M_2(\mathbb{Q})$), the family

$$e_t = \begin{pmatrix} 1 & t \\ 0 & 0 \end{pmatrix}, \qquad f_t = I_2 - e_t = \begin{pmatrix} 0 & -t \\ 0 & 1 \end{pmatrix} \qquad \bigl(t \in \mathbb{Z}\bigr)$$

yields infinitely many pairwise distinct unordered primitive decompositions while $m_{\mathrm{two}}\bigl(M_2(\mathbb{Q})\bigr) = 1$ and $r = 2$.

### 3. Division-Algebra & Non-Semisimple Obstructions (Clauses II & III)

- **Non-split Clifford division algebras:** $\mathrm{Cl}_{0,1}(\mathbb{F}_3) = \mathbb{F}_3[i]/(i^2+1) \cong \mathbb{F}_9$ and the quaternion algebras $\mathrm{Cl}_{0,2}(\mathbb{Z}) = \mathbb{H}(\mathbb{Z})$ and $\mathrm{Cl}_{0,2}(K) = \mathbb{H}(K)$ (over any formally real field $K$ such as $\mathbb{Q}$ or $\mathbb{R}$) have $m_{\mathrm{two}} = 1$ and $|E| = 2$, yet are **not ring-isomorphic to $M_n(\mathbb{F}_3)$, $M_n(\mathbb{Z})$, or $M_n(K)$ for any $n \ge 1$** ($n = 1$ fails by cardinality or noncommutativity $\mathbf{i}\mathbf{j} \neq \mathbf{j}\mathbf{i}$; $n \ge 2$ fails because $M_n$ contains nonzero nilpotents $E_{12}^2 = 0$ whereas fields and quaternions have no nonzero zero divisors).
- **Degenerate Clifford / exterior algebra $\Lambda(\mathbb{F}_3^1) = \mathbb{F}_3[\varepsilon]/(\varepsilon^2)$:** Its unique minimal nonzero ideal $I = \mathbb{F}_3 \varepsilon$ satisfies $I^2 = 0$ (zero nonzero idempotents) and the algebra is not isomorphic to $M_n(\mathbb{F}_3)$ for any $n \ge 1$.
- **Commutative local algebra $R = \mathbb{F}_3[x,y]/(x^2, xy, y^2)$:** Even in a commutative algebra where every idempotent is central and left ideals equal two-sided ideals, $E(R) = \{0, 1\}$ gives $r = N_{\mathrm{unord}} = N_{\mathrm{ord}} = 1$, yet $m_{\mathrm{two}}(R) = m_{\mathrm{left}}(R) = 4 \neq 1$ (all four minimal ideals square-zero).

---

## Package Structure

- `SOURCE.md` — Unmodified competition problem statement.
- `main.tex` / `main.pdf` — Self-contained mathematical paper with complete proofs and invariant tables.
- `lean/` — Zero-dependency Core Lean `4.19.0` formalization (`-DwarningAsError=true`, zero `sorry`, zero `native_decide`, zero custom axioms):
  - `Conjecture00000007625/Basic.lean` — Bundled ring hierarchy, `finSum`, idempotent decompositions, ideals, `MatNRing`, and `ExactCard` with Pigeonhole uniqueness (`exactCard_unique`).
  - `Conjecture00000007625/Positive.lean` — Abstract central block uniqueness theorem (`central_block_minimal_ideals_exactCard`, `central_block_decomp_uniqueness`), $\mathbb{F}_3^{m+1}$ (`f3Pow_positive_theorem`), and $\mathrm{Cl}_{1,0}(\mathbb{F}_3) \cong \mathbb{F}_3^2$ (`cl10_f3_iso_f3Pow2`).
  - `Conjecture00000007625/MatrixCounterexample.lean` — Characteristic-free $M_2(D)$ idempotent theory, $M_2(K)$ simplicity, $\mathrm{Cl}_{1,1}(\mathbb{F}_3) \cong M_2(\mathbb{F}_3)$, master six-way separation (`mat2_f3_master_refutation`), and infinite $M_2(\mathbb{Z})$ decompositions (`mat2_int_infinite_unord_prim_decomps`).
  - `Conjecture00000007625/Obstructions.lean` — Cayley–Dickson `Gauss` and `Quat` constructions, $\mathrm{Cl}_{0,1}(\mathbb{F}_3) \not\cong M_n(\mathbb{F}_3)$, $\mathbb{H}(\mathbb{Z}) \not\cong M_n(\mathbb{Z})$, $\mathbb{H}(K) \not\cong M_n(K)$, $\mathbb{F}_3[\varepsilon]/(\varepsilon^2)$, and commutative $\mathbb{F}_3[x,y]/(x^2,xy,y^2)$.
  - `Conjecture00000007625.lean` — Top-level resolution theorem `conjecture_00000007625_resolution`.
- `verify.py` — Deterministic Python 3.12 exhaustive computational verification suite.
- `verification/` — Build and audit logs (`lake-build.log`, `lean-axioms.log`, `lean-version.log`, `pdf-build.log`, `python-verify.log`, `SELF_REVIEW.md`).
