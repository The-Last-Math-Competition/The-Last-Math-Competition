# Conjecture 00000007161 — Nonnegative Inverse Eigenvalue Problem: Cyclic Lists and Rotation Lattice

**Status:** **DISPROVED** (refuted across all natural readings of *cyclic lists* and *rotation lattice*, with formal verification in Core Lean 4.19.0 and exact rational/integer verification in Python 3.12).

---

## 1. Original Statement (`SOURCE.md`)

> **English.** Definition: The inverse eigenvalue problem with the characterization of realizable spectra. Conjecture: The realizable spectra of nonnegative matrices are the cyclic lists, and the completeness of the lists is the rotation lattice. (rotation-lattice nonnegative realizable spectra)
>
> **中文。** 定义：逆特征值问题：可实现谱的刻画。猜想：非负可实现谱：非负矩阵的可实现谱为循环列表且表的完全性为轮换格。（非负可实现轮换格循环谱列表完全刻画）

---

## 2. Mathematical Summary and Refutation Across All Readings

An $n$-tuple $\Lambda = (\lambda_1, \dots, \lambda_n) \in \mathbb{C}^n$ is **nonnegative realizable** (in the Nonnegative Inverse Eigenvalue Problem, NIEP) if there exists an entrywise nonnegative real matrix $A \in M_n(\mathbb{R}_{\ge 0})$ with characteristic polynomial

$$\chi_A(t) = \det(t I_n - A) = \prod_{k=1}^n (t - \lambda_k).$$

Weighted cyclic permutation matrices $C_n(r) = r P_n \in M_n(\mathbb{R}_{\ge 0})$ ($r \ge 0$) indeed realize the scaled $n$-th root-of-unity cyclic lists $\Lambda_{\mathrm{cyc}}(n, r) = \bigl(r, r\zeta_n, \dots, r\zeta_n^{n-1}\bigr)$ ($\zeta_n = e^{2\pi i/n}$), showing non-vacuity. However, both clauses of Conjecture `00000007161` fail under every standard interpretation:

### Reading I: Cyclic Root-of-Unity Lists and Disjoint Unions

Every scaled root-of-unity piece $\Lambda_{\mathrm{cyc}}(k, r) = \{r e^{2\pi i s / k} : 0 \le s \lt k\}$ ($k \ge 1, r \ge 0$) contains its positive real generator $r$ ($s = 0$), while every element $z$ in the piece satisfies $|z| = r$. Hence any multiset $\Lambda$ covered by cyclic root-of-unity lists satisfies the **modulus-presence invariant**:

$$\lambda \in \Lambda \implies |\lambda| \in \Lambda.$$

1. **Minimal symmetric, zero-diagonal (trace-zero), irreducible $\{0,1\}$-matrix counterexample ($n = 3$):**
   The adjacency matrix of $K_3$,

   $$A_3 = J_3 - I_3 = \begin{pmatrix} 0 & 1 & 1 \\ 1 & 0 & 1 \\ 1 & 1 & 0 \end{pmatrix} \in M_3(\mathbb{R}_{\ge 0}),$$

   is entrywise nonnegative, symmetric, trace-zero, and irreducible, with $\chi_{A_3}(t) = (t - 2)(t + 1)^2$ and exact spectrum $\Lambda(A_3) = \bigl(2, -1, -1\bigr)$. Since $-1 \in \Lambda(A_3)$ whereas $|-1| = 1 \notin \Lambda(A_3)$, $\Lambda(A_3)$ is **neither** a cyclic root-of-unity list **nor** covered by any union of cyclic root-of-unity lists.

2. **Infinite families in every dimension $n \ge 3$:**
   - **Hollow all-ones family:** $A_n = J_n - I_n \in M_n(\{0,1\})$ is nonnegative, symmetric, zero-diagonal, and irreducible with spectrum $\bigl(n - 1, -1, \dots, -1\bigr)$, violating $|-1| = 1 \in \Lambda(A_n)$ for every $n \ge 3$.
   - **Suleimanova companion family:** For any integers $\mu_2, \dots, \mu_n \gt 0$ and $\lambda_1 \ge \sum_{k=2}^n \mu_k$, $\bigl(t - \lambda_1\bigr)\prod_{k=2}^n (t + \mu_k) = t^n - \sum_{j=0}^{n-1} c_j t^j$ has all $c_j \ge 0$ (and $c_{n-1} = 0$ when $\lambda_1 = \sum_{k=2}^n \mu_k$), so its Frobenius companion matrix is nonnegative and realizes $\bigl(\lambda_1, -\mu_2, \dots, -\mu_n\bigr)$ (including $n$ pairwise distinct integers $\bigl(\binom{n}{2}, -1, -2, \dots, -(n-1)\bigr)$).

### Reading II: Nonnegative Circulant Matrices (`循环矩阵`)

For any real $3 \times 3$ circulant matrix $C(c_0, c_1, c_2)$ (even allowing negative entries), Gauss's sum-of-three-squares factorization yields

$$2\det\bigl(t I_3 - C(c_0, c_1, c_2)\bigr) = \bigl(t - (c_0 + c_1 + c_2)\bigr)\Bigl((t - c_0 + c_1)^2 + (t - c_0 + c_2)^2 + (c_1 - c_2)^2\Bigr).$$

Hence every real root belongs to $\{c_0 + c_1 + c_2, c_0 - c_1\}$, so **no real $3 \times 3$ circulant matrix can realize three pairwise distinct real eigenvalues**. Yet both:
- the zero-diagonal primitive nonnegative matrix $M_3 = \begin{pmatrix} 0 & 1 & 0 \\ 0 & 0 & 1 \\ 6 & 7 & 0 \end{pmatrix}$ with spectrum $\bigl(3, -1, -2\bigr)$, and
- the symmetric primitive nonnegative matrix $S_3 = \begin{pmatrix} 0 & 2 & 1 \\ 2 & 0 & 1 \\ 1 & 1 & 1 \end{pmatrix}$ with spectrum $\bigl(3, 0, -2\bigr)$

realize three pairwise distinct integer eigenvalues, refuting the circulant characterization simultaneously with Reading I.

### Reading III: Complex Phase Rotations and Circular-Shift Lattices (`轮换格`)

1. **Complex phase rotation destroys realizability:** Every $A \in M_n(\mathbb{R}_{\ge 0})$ satisfies $A^k \ge 0$ entrywise and hence $s_k(\Lambda) = \mathrm{tr}(A^k) \ge 0$ for all $k \ge 0$. Rotating the realizable cyclic list $\bigl(r, -r\bigr)$ ($r \ge 1$, realized for $r = 1$ by $P_2 = \bigl(\begin{smallmatrix} 0 & 1 \\ 1 & 0 \end{smallmatrix}\bigr)$) by $\pi/2$ yields $\bigl(ri, -ri\bigr)$ with real characteristic polynomial $t^2 + r^2$, whose second Newton power sum is

   $$s_2(ri, -ri) = (ri)^2 + (-ri)^2 = -2r^2 \lt 0,$$

   violating $\mathrm{tr}(A^2) \ge 0$ (and Perron–Frobenius). More generally, for any $n \ge 2$ and $r \gt 0$, $e^{i\theta}\Lambda_{\mathrm{cyc}}(n, r)$ is nonnegative realizable if and only if $e^{in\theta} = 1$ (which leaves the multiset unchanged).

2. **Circular coordinate shifts and lattice meet failure:** Circular shifts $\sigma(\lambda_1, \dots, \lambda_n) = (\lambda_2, \dots, \lambda_n, \lambda_1)$ preserve $\prod_{k=1}^n (t - \lambda_k)$ identically and generate no new unordered spectra. Under componentwise lattice meet $\wedge$ on $\mathbb{R}^n$, the circular shifts $\bigl(1, -1\bigr)$ and $\bigl(-1, 1\bigr)$ of $\Lambda(P_2)$ have meet $\bigl(-1, -1\bigr)$ with trace $-2 \lt 0$ (and the circular shifts of $\bigl(2, -1, -1\bigr)$ have meet $\bigl(-1, -1, -1\bigr)$ with trace $-3 \lt 0$), neither of which is nonnegative realizable.

---

## 3. Package Structure and Reproducibility

| Path | Description |
| :--- | :--- |
| `SOURCE.md` | Original verbatim problem statement (English and Chinese) |
| `main.tex` / `main.pdf` | Self-contained mathematical manuscript with complete proofs |
| `lean/` | Core Lean 4.19.0 formalization (`Main.lean`, zero external dependencies) |
| `verify.py` | Pure Python 3.12 exact rational/integer verification suite |
| `verification/` | Build logs (`lake-build.log`, `lean-axioms.log`, `lean-version.log`, `pdf-build.log`, `python-verify.log`) and `SELF_REVIEW.md` |

### Commands to Reproduce

```bash
# 1. Build Core Lean 4.19.0 formalization (with -DwarningAsError=true)
cd lean && lake build

# 2. Run exact Python 3.12 verification suite
python3 verify.py

# 3. Compile manuscript PDF
pdflatex -interaction=nonstopmode main.tex && pdflatex -interaction=nonstopmode main.tex
```
