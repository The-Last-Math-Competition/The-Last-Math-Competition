# Conjecture 00000007628 — Minimal Ideals, Spinor Dimensions, and Ideal Automorphism Groups in Clifford Algebras

**Status:** **Disproved (Refuted across all general readings; positive split-signature regime characterized)**

## 1. Conjecture Statement

From `SOURCE.md`:

> **English.** Definition: Minimal ideals with the ideal dimension law of Clifford algebras. Conjecture: The conversion constant is the ideal dimension law and the minimal-ideal dimension is exactly the spinor dimension; the law is exact with test by semisimple decomposition; and the automorphism group of the ideal is the symplectic group. (ideal-dimension conversion)
>
> **中文。** 定义：极小理想：Clifford 代数的理想维数律。猜想：换算常数为理想的维数律且极小理想维数恰为旋量维数；律精确且精确的检验为半单分解；理想的自同构群为辛群。（理想维数换算常数结构）

Let $K$ be a field and $\bigl(V, Q\bigr)$ an $n$-dimensional quadratic space over $K$, with Clifford algebra $\mathrm{Cl}\bigl(V, Q\bigr)$ of dimension $2^n$ and reference spinor dimension $d_{\mathrm{spin}}\bigl(n\bigr) = 2^{\lfloor n/2 \rfloor}$. The conjecture asserts three linked claims for minimal ideals $I \subseteq \mathrm{Cl}\bigl(V, Q\bigr)$:
1. **Minimal-ideal dimension & conversion law:** $\dim_K I = d_{\mathrm{spin}}$, with conversion constant $\dim_K \mathrm{Cl}\bigl(V, Q\bigr) / \dim_K I$.
2. **Semisimple exactness test:** The conversion law is exact and witnessed by a semisimple decomposition of $\mathrm{Cl}\bigl(V, Q\bigr)$ into minimal ideals.
3. **Symplectic automorphism group:** The automorphism group of the minimal ideal $I$ is the symplectic group.

---

## 2. Summary of Mathematical Resolution

### A. Positive Non-Vacuity Theorem (Origin of the Heuristic)

On the nondegenerate split Clifford algebra $\mathrm{Cl}_{1,1}\bigl(K\bigr) \cong M_2\bigl(K\bigr)$ for $\mathrm{char}\bigl(K\bigr) \neq 2$ (quadratic form $Q\bigl(x_1, x_2\bigr) = x_1^2 - x_2^2$):
- The orthogonal primitive idempotents $E_{11} = \frac{1}{2}\bigl(I_2 + \gamma_1\bigr)$ and $E_{22} = \frac{1}{2}\bigl(I_2 - \gamma_1\bigr)$ yield the exact Wedderburn–Artin semisimple decomposition $\mathrm{Cl}_{1,1}\bigl(K\bigr) = S_1 \oplus S_2$ into minimal nonzero **left** ideals $S_i = M_2\bigl(K\bigr)E_{ii}$ of exact spinor dimension $\dim_K S_i = 2 = 2^{2/2}$, with conversion constant $4 / 2 = 2$.
- Under $\mathrm{Cl}_{1,1}\bigl(K\bigr) \cong M_2\bigl(K\bigr)$, Clifford conjugation $\overline{X} = \gamma_2^{-1} X^\top \gamma_2$ induces a canonical nondegenerate alternating spinor pairing $\omega\bigl(u, v\bigr) = u_1 v_2 - u_2 v_1$ on $S_1 \cong K^2$ satisfying $\omega\bigl(X u, v\bigr) = \omega\bigl(u, \overline{X} v\bigr)$ for all $X \in \mathrm{Cl}_{1,1}\bigl(K\bigr)$, and its form-preserving linear automorphism group is literally the symplectic group:

$$\mathrm{Aut}_K\bigl(S_1, \omega\bigr) = \bigl\{ g \in M_2\bigl(K\bigr) : \det g = 1 \bigr\} = \mathrm{Sp}_2\bigl(K\bigr).$$

### B. Complete Multi-Reading Refutation

As a general mathematical statement about Clifford algebras and their minimal ideals, Conjecture `00000007628` is **false** in every clause:

| Clause / Reading | Sharp Counterexample | Exact Failure |
| :--- | :--- | :--- |
| **Minimal two-sided ideal** $J$ | $\mathrm{Cl}_{1,1}\bigl(K\bigr) \cong M_2\bigl(K\bigr)$ (or $\mathrm{Cl}_{m,m}\bigl(K\bigr) \cong M_{2^m}\bigl(K\bigr)$) | Central simple algebra: unique minimal nonzero two-sided ideal has $\dim_K J = 4^m \gt 2^m$ ($4 \neq 2$ at $m = 1$). |
| **Degenerate quadratic form** $Q \equiv 0$ | Exterior algebra $\mathrm{Cl}\bigl(K^n, 0\bigr) = \Lambda\bigl(K^n\bigr)$, $n \ge 2$ | $\mathrm{rad}\bigl(\Lambda\bigr) = \Lambda^+ \neq 0$ (not semisimple; no left-ideal complement to $\Lambda^n$); unique minimal left ideal $\Lambda^n\bigl(K^n\bigr)$ has $\dim_K = 1 \neq 2^{\lfloor n/2 \rfloor}$. |
| **Nondegenerate division Clifford algebra** | $\mathrm{Cl}_{0,2}\bigl(\mathbb{Q}\bigr) \cong \mathbb{H}_{\mathbb{Q}}$ (or $\mathrm{Cl}_{0,2}\bigl(\mathbb{R}\bigr) \cong \mathbb{H}$) | Semisimple division ring ($\overline{q}\,q = \mathrm{normSq}\bigl(q\bigr) \gt 0$ for $q \neq 0$): unique minimal nonzero left ideal has $\dim = 4 \neq 2 = 2^{2/2}$. |
| **(R3a) Left $\mathrm{Cl}$-module automorphisms** $\mathrm{Aut}_{\mathrm{Cl}}\bigl(S\bigr)$ | $\mathrm{Cl}_{1,1}\bigl(K\bigr)$, $S_1 \cong K^2$ | By Schur's lemma, $\mathrm{Aut}_{\mathrm{Cl}}\bigl(S_1\bigr) \cong K^\times$ is **abelian** ($\lvert\mathbb{F}_3^\times\rvert = 2$), whereas $\mathrm{Sp}_{2r}\bigl(F\bigr)$ is **non-abelian** ($\lvert\mathrm{Sp}_2\bigl(\mathbb{F}_3\bigr)\rvert = 24$) over every field $F$. |
| **(R3b) $K$-linear automorphisms** $\mathrm{GL}_K\bigl(S\bigr)$ | $\mathrm{Cl}_{1,0}\bigl(K\bigr) \cong K \oplus K$; $\mathrm{Cl}_{1,1}\bigl(\mathbb{F}_3\bigr)$ | Odd spinor $\dim = 1$ on $\mathrm{Cl}_{1,0}\bigl(K\bigr)$ admits **no** nonzero alternating form; $\lvert\mathrm{GL}_2\bigl(\mathbb{F}_3\bigr)\rvert = 48 \neq 24$; $\dim \mathrm{GL}_N = N^2 \gt N\bigl(N+1\bigr)/2$. |
| **(R3c) Left-ideal algebra automorphisms** $\mathrm{Aut}_{K\text{-alg}}\bigl(S\bigr)$ | $\mathrm{Cl}_{1,1}\bigl(K\bigr)$, $S_1 \cong K^2$ | $\mathrm{Aut}_{K\text{-alg}}\bigl(S_1\bigr) \cong \mathrm{Aff}_1\bigl(K\bigr) = K \rtimes K^\times$ is **2-step solvable** ($\lvert\mathrm{Aff}_1\bigl(\mathbb{F}_3\bigr)\rvert = 6$), whereas $\bigl[\mathrm{Sp}_2\bigl(F\bigr), \mathrm{Sp}_2\bigl(F\bigr)\bigr]$ is non-abelian for all $\mathrm{char}\bigl(F\bigr) \neq 2$. |
| **(R3d) Two-sided ideal algebra automorphisms** $\mathrm{Aut}_{K\text{-alg}}\bigl(J\bigr)$ | $\mathrm{Cl}_{1,1}\bigl(K\bigr) \cong M_2\bigl(K\bigr)$ | Trivial center $Z\bigl(\mathrm{Aut}_{K\text{-alg}}\bigl(M_2\bigl(K\bigr)\bigr)\bigr) = \{\mathrm{id}\}$ vs. nontrivial center $\{\pm I_{2r}\} \subseteq Z\bigl(\mathrm{Sp}_{2r}\bigl(F\bigr)\bigr)$ for all $\mathrm{char}\bigl(F\bigr) \neq 2$; $\dim \mathrm{PGL}_4 = 15 \neq 10 = \dim \mathrm{Sp}_4$. |
| **(R3e) Spinor bilinear pairing isometries** $\mathrm{Aut}_K\bigl(S, \beta\bigr)$ | $\mathrm{Cl}_{2,0}\bigl(K\bigr)$; $\mathrm{Cl}_{4,4}\bigl(K\bigr)$ ($n = 8$) | On $\mathrm{Cl}_{2,0}\bigl(K\bigr)$, reversion induces symmetric $\mathrm{O}_2\bigl(K\bigr)$ ($\lvert\mathrm{O}_2\bigl(\mathbb{F}_3\bigr)\rvert = 8 \neq 24$); at $n = 8$ ($\mathrm{Cl}_{4,4}\bigl(K\bigr) \cong M_{16}\bigl(K\bigr)$), **both** reversion and Clifford conjugation fix $136 = \frac{16 \cdot 17}{2} \neq 120$ blades, yielding $\mathrm{O}_{16}$ rather than $\mathrm{Sp}_{16}$. |

---

## 3. Package Structure & Verification Commands

- `SOURCE.md` — Original bilingual problem statement (unmodified).
- `main.tex`, `main.pdf` — Publication-grade paper presenting the positive split-signature theorem and the complete multi-reading refutation.
- `lean/` — Self-contained **Core Lean 4.19.0** formalization (`leanprover/lean4:v4.19.0`, `moreLeanArgs = ["-DwarningAsError=true"]`, zero external dependencies, zero `sorry`/`admit`/`native_decide`, zero custom axioms):
  - `Conjecture00000007628/Field.lean` — `CommField K`, exact finite field `F3`, group isomorphism obstructions, and pigeonhole finite non-bijection.
  - `Conjecture00000007628/Mat2.lean` — $\mathrm{Cl}_{1,1}\bigl(K\bigr)$ and $\mathrm{Cl}_{2,0}\bigl(K\bigr)$, positive split theorem, two-sided simplicity of $M_2\bigl(K\bigr)$, and symmetric reversion spinor form on $\mathrm{Cl}_{2,0}\bigl(K\bigr)$.
  - `Conjecture00000007628/ExteriorAndQuat.lean` — Degenerate exterior algebra $\Lambda\bigl(K^2\bigr) = \mathrm{Cl}\bigl(K^2, 0\bigr)$, division quaternions $\mathrm{Cl}_{0,2}\bigl(\mathbb{Z}\bigr)$, and odd-dimensional symplectic impossibility on $\mathrm{Cl}_{1,0}\bigl(K\bigr)$.
  - `Conjecture00000007628/Automorphisms.lean` — Polymorphic non-isomorphism theorems for $\mathrm{Aut}_{\mathrm{Cl}}\bigl(S_1\bigr)$, $\mathrm{GL}_2\bigl(K\bigr)$, $\mathrm{Aff}_1\bigl(K\bigr)$, and $\mathrm{Aut}_{K\text{-alg}}\bigl(M_2\bigl(K\bigr)\bigr)$ against $\mathrm{Sp}_2\bigl(F\bigr)$, exact $\mathbb{F}_3$ order spectrum $\{2, 6, 8, 24, 48\}$, and $n = 8$ mod-$8$ blade-fix proof.
  - `Conjecture00000007628/Main.lean` — Master synthesis theorems `conjecture_00000007628_positive_split_case`, `conjecture_00000007628_complete_refutation`, and `conjecture_00000007628_refuted_over_F3`.
- `verify.py` — Standalone Python 3.12 exact arithmetic verification script (`fractions.Fraction` and modular $\mathbb{F}_p$ arithmetic).
- `verification/` — Complete build, axiom-audit, version, PDF, and Python verification logs, plus `SELF_REVIEW.md`.

### Reproducing Verification

```bash
cd lean && lake build
python3 verify.py
pdflatex -interaction=nonstopmode -halt-on-error main.tex
```
