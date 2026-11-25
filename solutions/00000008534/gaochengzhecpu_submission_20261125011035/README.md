# Conjecture 00000008534 — Whitney Log-Concavity of Geometric Lattices

**Verdict:** **FALSE** (disproved unconditionally across all natural mathematical conventions; formally verified in Core Lean 4.19.0 and Python).

---

## 1. Conjecture Statement

From `SOURCE.md`:

> **English.** Definition: The Whitney numbers of a lattice are its rank distribution. Conjecture: The Whitney numbers of a geometric lattice form a log-concave sequence; log-concavity is strict when the lattice is unimodular; otherwise the first flat occurs at the doubly-flat element stratum. (Whitney log-concavity)
>
> **中文。** 定义：格的 Whitney 数指其秩分布。猜想：几何格的 Whitney 数构成对数凹序列；严格对数凹当格为单模；否则第一处平坦出现在双平坦元素层。（Whitney 对数凹）

---

## 2. Core Counterexample and Convention Coverage

Let $L = M_4 \cong L(U_{2,4})$ be the $6$-element geometric lattice of flats of the $4$-point uniform line $U_{2,4}$ on ground set $E = \{0, 1, 2, 3\}$:

- Rank $0$: $\hat{0} = \emptyset$ ($1$ element).
- Rank $1$: $\{0\}, \{1\}, \{2\}, \{3\}$ ($4$ atoms).
- Rank $2$: $\hat{1} = \{0, 1, 2, 3\}$ ($1$ element).

### Non-unimodularity of $M_4$

A geometric lattice is **unimodular** (or **regular**) if it is representable over $\mathbb{Q}$ by a totally unimodular integer matrix $A \in \mathbb{Z}^{m \times n}$ (every square submatrix has determinant in $\{-1, 0, 1\}$). Reducing any totally unimodular representation modulo $2$ preserves all non-vanishing minors, yielding an $\mathbb{F}_2$-representation. However, $M_4 \cong L(U_{2,4})$ is not binary: any $\mathbb{F}_2$-representation projects (via the modulo-$2$ Cramer-Plücker identity) onto two rows on which all $\binom{4}{2} = 6$ column pairs have odd $2 \times 2$ determinant, requiring $4$ distinct nonzero vectors in $\mathbb{F}_2^2 \setminus \{\bigl(0,0\bigr)\}$, which has cardinality $3 \lt 4$. Hence $M_4$ is **not unimodular**.

### Absence of any flat in $M_4$

The conjecture asserts that whenever $L$ is not unimodular ("otherwise"), its Whitney sequence exhibits a first flat at the "doubly-flat element stratum." Yet $M_4$ has **no flat at any index** under any standard convention:

1. **Whitney numbers of the second kind (rank distribution, as defined in `SOURCE.md`):**
   $$\bigl(W_0(M_4), W_1(M_4), W_2(M_4)\bigr) = (1, 4, 1).$$
   - **Log-concavity flat** ($W_k^2 = W_{k-1} W_{k+1}$ for $1 \le k \le r - 1$): At the unique interior rank $k = 1$, $W_1^2 = 16 \gt 1 = W_0 W_2$, so log-concavity is **strict** and zero flats exist.
   - **Value-plateau flat** ($W_k = W_{k+1}$ for $0 \le k \le r - 1$): $W_0 = 1 \neq 4 = W_1$ and $W_1 = 4 \neq 1 = W_2$, so zero plateaus exist.

2. **Unsigned Whitney numbers of the first kind** $|w_k(L)| = \bigl|\sum_{\mathrm{rk}(x)=k} \mu_L(\hat{0}, x)\bigr|$:
   $$\bigl(|w_0(M_4)|, |w_1(M_4)|, |w_2(M_4)|\bigr) = (1, 4, 3).$$
   - **Log-concavity flat**: At $k = 1$, $|w_1|^2 = 16 \gt 3 = |w_0| |w_2|$, so log-concavity is **strict** and zero flats exist.
   - **Value-plateau flat**: $1 \neq 4 \neq 3$, so zero plateaus exist.

Because the set of flats of $M_4$ is empty, "the first flat occurs at the doubly-flat element stratum" is false for **every** possible definition of that stratum $S(L) \subseteq \mathbb{N}$.

### Additional witnesses and boundary cases

- **Simultaneous failure on unimodular lattices under the plateau convention:** The rank-$3$ Boolean lattice $B_3 \cong L(U_{3,3})$ is unimodular (represented by $I_3$), yet $W(B_3) = |w(B_3)| = (1, 3, 3, 1)$ has a value plateau at $k = 1$ ($3 = 3$), refuting even the unimodular branch if "strict / flat" refers to adjacent equality $a_k = a_{k+1}$.
- **Higher-rank non-modular non-unimodular counterexample:** $L(U_{3,5})$ (rank $3$, $17$ elements) is neither modular nor unimodular, yet both $W = (1, 5, 10, 1)$ ($25 \gt 10$, $100 \gt 5$) and $|w| = (1, 5, 10, 6)$ ($25 \gt 10$, $100 \gt 30$) are strictly log-concave and plateau-free.
- **Unimodularity vs. modularity separation:** $L(U_{3,4}) \cong L(M(C_4))$ (rank $3$, $12$ elements) is unimodular ($3 \times 4$ totally unimodular matrix $[I_3 \mid \mathbf{1}]$) yet **not** a modular lattice, with strictly log-concave and plateau-free $W = (1, 4, 6, 1)$ and $|w| = (1, 4, 6, 3)$.
- **Positive non-vacuity witnesses:** $B_2 \cong L(U_{2,2})$, $M_3 \cong L(U_{2,3})$, and $L(U_{3,4})$ are unimodular geometric lattices of rank $r \ge 2$ satisfying non-vacuous strict log-concavity for both $W_k$ and $|w_k|$.

---

## 3. Package Layout and Verification

- `SOURCE.md` — Original unaltered problem statement.
- `main.tex`, `main.pdf` — Self-contained mathematical paper with complete proofs and convention tables.
- `lean/` — Dependency-free Core Lean 4 (`leanprover/lean4:v4.19.0`) formalization:
  - `Main.lean` — First-principles definitions of `GeometricLattice`, rank uniqueness (`rk_unique`), Möbius inversion (`muBot_interval_sum_zero`), `whitneySecond`, `whitneyFirstUnsigned`, `det`, `IsTotallyUnimodular`, `IsUnimodular`, `IsBinary`, `unimodular_implies_binary`, `not_isBinary_M4`, `not_isUnimodular_M4`, `positive_witnesses_unimodular`, `disproof_conjecture_secondKind_lcFlat`, `disproof_conjecture_firstKind_lcFlat`, `disproof_conjecture_plateau_both_branches`, and `boundary_and_modularity_checks`. Built with `-DwarningAsError=true`; depends only on `[propext, Quot.sound]`.
- `verify.py` — Independent Python 3 verification script checking lattice axioms, Möbius/Whitney numbers, exhaustive $\mathbb{F}_2$ and $\{-1,0,1\}$ matrix representations, and all convention cases.
- `verification/` — Build and verification logs (`lake-build.log`, `lean-axioms.log`, `lean-version.log`, `pdf-build.log`, `python-verify.log`) and `SELF_REVIEW.md`.

To reproduce:

```bash
cd lean && lake build
python3 verify.py
pdflatex -interaction=nonstopmode -halt-on-error main.tex
```
