# Conjecture 00000007626 — Connected-Family Spectra of Idempotents and Matrix-Block Counts

## Problem Statement

- **English:** Definition: The connected-family structure of idempotent formulas. Conjecture: The connected-family spectrum of idempotents is finite; the bound of finiteness is the matrix-block count; and the bound of the matrix-block count is the isomorphism-class counting. (matrix-block-finite idempotent families)
- **中文：** 定义：幂等公式的连通族结构。猜想：幂等元的连通族谱有限；且有限的界为矩阵块数；且矩阵块数的界为同构类计数。（幂等连通族矩阵块有限）

*(Verbatim statement preserved in `SOURCE.md`.)*

---

## Verdict: **DISPROVED (False)**

Let $A$ be a finite-dimensional associative unital algebra over a field $K$ with Jacobson radical $J(A)$ and Artin–Wedderburn semisimple quotient

$$A / J(A) \;\cong\; \bigoplus_{i=1}^{b} M_{n_i}(D_i),$$

where $b = b(A) \ge 1$ is the **matrix-block count** and $n_i \ge 1$ are the matrix block sizes over division $K$-algebras $D_i$. Across all standard connected-family structures on the idempotent locus $E(A) = \{e \in A \mid e^2 = e\}$ — topological path-connectedness over $\mathbb{R}$ or $\mathbb{C}$, smooth families, algebraic $\mathbb{A}^1$-polynomial homotopies in $A[t]$, unit-conjugacy orbits, and isomorphism classes of cyclic projective left ideals $Ae$ — the connected-family spectrum $\pi_0(E(A))$ has exact cardinality

$$\bigl|\pi_0(E(A))\bigr| \;=\; \prod_{i=1}^{b} (n_i + 1).$$

Consequently, **Conjecture `00000007626` is false**:

1. **Clause II ($|\pi_0(E(A))| \le b(A)$) fails across all idempotent regimes:**
   - **All idempotents $E(A)$:** Since $n_i \ge 1$, $\prod_{i=1}^b (n_i + 1) \ge 2^b \gt b$ for **every** nonzero finite-dimensional algebra ($b \ge 1$). Already on the single-block split Clifford algebra $\mathrm{Cl}_{1,1}(K) \cong M_2(K)$ ($b = 1$), $\pi_0(E(M_2(K)))$ has **$3 \gt 1$** connected components ($\{0\}$, the rank-$1$ family, and $\{I_2\}$) over every field $K$ of arbitrary characteristic.
   - **Proper (nontrivial) idempotents $E^\circ(A) = E(A) \setminus \{0, 1\}$:** The inequality $\prod_{i=1}^b (n_i + 1) - 2 \le b$ holds **if and only if** the block-size profile belongs to $\{(1), (2), (1, 1)\}$. It fails for every single-block matrix algebra $M_n(K)$ with $n \ge 3$ (e.g., $\mathrm{Cl}_{2,2}(\mathbb{R}) \cong M_4(\mathbb{R})$ has $b = 1$ and **$3 \gt 1$** proper components), for $\mathrm{Cl}_{2,1}(\mathbb{R}) \cong M_2(\mathbb{R}) \oplus M_2(\mathbb{R})$ ($b = 2$, **$7 \gt 2$**), for $K^3$ ($b = 3$, **$6 \gt 3$**), and diverges exponentially as $2^m - 1 \to \infty$ along $\mathrm{Cl}_{m,m}(K) \cong M_{2^m}(K)$ while $b = 1$ remains constant — proving that **no function $F(b)$ of the matrix-block count alone** bounds $|\pi_0(E(A))|$ or $|\pi_0(E^\circ(A))|$.
   - **Central and non-semisimple regimes:** Central idempotents satisfy $|E(Z(A))| = 2^b \gt b$ for all $b \ge 1$ (and $2^b - 2 \gt b$ for all $b \ge 3$). The non-semisimple upper-triangular algebra $T_2(K)$ ($b = 2$) has $4 \gt 2$ connected components.
2. **Clause III ($b(A) \le c_{\mathrm{iso}}(A)$) also fails:**
   - Under **algebra-isomorphism class counting** $c_{\mathrm{alg}}(A)$ of the simple matrix blocks, the **reverse** inequality $c_{\mathrm{alg}}(A) \le b(A)$ holds universally, with strict failure $b(A) \gt c_{\mathrm{alg}}(A) = 1$ whenever isomorphic blocks repeat — yielding simultaneous double strict reverse inequalities:
     - $\mathrm{Cl}_{1,0}(K) \cong K \oplus K$: $|\pi_0(E)| = 4 \gt b = 2 \gt c_{\mathrm{alg}} = 1$.
     - $\mathrm{Cl}_{2,1}(K) \cong M_2(K) \oplus M_2(K)$: $|\pi_0(E^\circ)| = 7 \gt b = 2 \gt c_{\mathrm{alg}} = 1$.
     - $K^3$ (proper central idempotents): $|\pi_0(E^\circ(Z))| = 6 \gt b = 3 \gt c_{\mathrm{alg}} = 1$.
   - Under **module-isomorphism readings** ($c_{\mathrm{simp}}(A) = b(A)$ or $c_{\mathrm{proj}}(A) = \prod_{i=1}^b (n_i + 1)$), the joint conjecture still collapses at Clause II.
3. **Conceptual Origin, Primitive Salvage & Clause I Boundary:**
   - Restricting specifically to **primitive** idempotents $\mathrm{Prim}(E(A))$ yields $|\pi_0(\mathrm{Prim}(E(A)))| = b(A) = c_{\mathrm{simp}}(A)$, pinpointing the conflation of primitive spinor idempotents with general idempotents as the origin of the conjecture.
   - Without finite-dimensionality, even Clause I fails: in $\mathbb{Z}^{\mathbb{N}}$, every polynomial idempotent family is constant and the Kronecker-delta idempotents form infinitely many disconnected components.

---

## Package Structure

- `SOURCE.md` — Original bilingual problem statement (unmodified).
- `main.tex`, `main.pdf` — Self-contained mathematical paper presenting the complete classification, proofs, Bott-periodic Clifford comparison table, and Lean 4 correspondence.
- `verify.py` — Standalone Python 3 verification script (standard library only) cross-checking exhaustive $M_2(\mathbb{F}_p)$ homotopy graphs, Leibniz–trace polynomial invariance on $M_n(\mathbb{Q}[t])$, all $45$ real Clifford signatures $0 \le p + q \le 8$, sporadic profiles, and non-semisimple nilpotent lifting.
- `lean/` — Self-contained Core Lean `v4.19.0` formalization (`lean-toolchain`, `lakefile.toml`, `lake-manifest.json`, `Main.lean`) with zero external dependencies and `-DwarningAsError=true`.
- `verification/` — Build and verification logs (`lake-build.log`, `lean-axioms.log`, `lean-version.log`, `pdf-build.log`, `python-verify.log`) and `SELF_REVIEW.md`.

---

## Reproducing Verification

1. **Lean 4 Formalization (`leanprover/lean4:v4.19.0`):**
   ```bash
   cd lean
   lake build
   ```
2. **Independent Python Verification:**
   ```bash
   python3 verify.py
   ```
3. **LaTeX Paper Compilation:**
   ```bash
   pdflatex -interaction=nonstopmode -halt-on-error main.tex
   pdflatex -interaction=nonstopmode -halt-on-error main.tex
   ```
