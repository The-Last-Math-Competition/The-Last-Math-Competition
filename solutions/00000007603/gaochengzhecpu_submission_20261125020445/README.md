# Conjecture 00000007603 — Norm-Type Geometric-Product Conversion

**Verdict:** **FALSE** (refuted in general across all standard Clifford-algebra norm conventions, with sharp classification of the positive domain and exact Bott-periodicity conversion constants).

---

## 1. Problem Statement

From `SOURCE.md`:

> **English.** Definition: The geometric product as the norm-type product structure. Conjecture: The conversion constant is the norm law of the product, the norm always equaling the bound of the quadratic-form product; the spectrum is explicit and is the isometry group; and the tight example of equality is vector pairs. (norm-type geometric-product conversion)
>
> **中文。** 定义：几何积：范数型积结构。猜想：换算常数为积的范数律且范数恒等于二次型积的界；谱显式且谱为等距群；等式的紧例为向量对。（范数型积换算常数结构）

---

## 2. Mathematical Summary

Let $\mathrm{Cl}_{p,q} = \mathrm{Cl}\bigl(\mathbb{R}^{p,q}, Q\bigr)$ denote the Clifford algebra of the quadratic form $Q(v) = \sum_{i=1}^p v_i^2 - \sum_{j=p+1}^{p+q} v_j^2$ under the geometric product $v^2 = Q(v) \cdot 1$, equipped with grade involution $\widehat{X}$, reversal $\widetilde{X}$, and Clifford conjugation $\overline{X} = \widetilde{\widehat{X}}$. We test every standard quadratic norm convention on $\mathrm{Cl}_{p,q}$:
- Euclidean $L^2$-blade squared norm $\|X\|_2^2 := \sum_A x_A^2$;
- Scalar reversal quadratic form $N_{\mathrm{rev}}(X) := \langle \widetilde{X} X \rangle_0$ (which equals $\|X\|_2^2$ on $\mathrm{Cl}_{n,0}$);
- Scalar Clifford-conjugation quadratic form $N_{\mathrm{conj}}(X) := \langle \overline{X} X \rangle_0$ (which equals $\|X\|_2^2$ on $\mathrm{Cl}_{0,n}$);
- Algebraic spinor norms $\widetilde{X} X$ and $\overline{X} X$ in $\mathrm{Cl}_{p,q}$.

### Positive Non-Vacuity Domain
1. **Grade-$1$ Vector Pairs and Versors:** For all grade-$1$ vectors $u, v \in V \subset \mathrm{Cl}(V, Q)$, $\widetilde{(u v)}(u v) = Q(u) Q(v) \cdot 1$ and $N_{\mathrm{rev}}(u v) = Q(u) Q(v)$. On Euclidean $\mathrm{Cl}_{n,0}$ for all $n \ge 0$, Lagrange's identity gives $\|u v\|_2^2 = \bigl(u \cdot v\bigr)^2 + \|u \wedge v\|_2^2 = Q(u) Q(v)$, and every versor $W = v_1 \cdots v_k$ satisfies $\|W Y\|_2^2 = \|W\|_2^2 \|Y\|_2^2$ for all $Y \in \mathrm{Cl}_{n,0}$.
2. **Hurwitz Low-Dimensional Algebras:** On $\mathrm{Cl}_{0,0} \cong \mathbb{R}$, $\mathrm{Cl}_{0,1} \cong \mathbb{C}$, and $\mathrm{Cl}_{0,2} \cong \mathbb{H}$, exact multiplicativity $\|X Y\|_2^2 = \|X\|_2^2 \|Y\|_2^2$ holds for all multivectors $X, Y$ (and $N_{\mathrm{conj}}(X Y) = N_{\mathrm{conj}}(X) N_{\mathrm{conj}}(Y)$ holds whenever $p + q \le 2$).

### Complete Refutations of All Three Clauses
1. **Euclidean $\mathrm{Cl}_{n,0}$ for all $n \ge 1$:** Taking $X_\pm = 1 \pm e_1$ gives $\|X_\pm\|_2^2 = N_{\mathrm{rev}}(X_\pm) = 2$ (product bound $4$), yet $X_+^2 = 2 + 2 e_1$ has $\|X_+^2\|_2^2 = N_{\mathrm{rev}}(X_+^2) = 8 \gt 4$, while $X_+ X_- = 0$ has $\|X_+ X_-\|_2^2 = 0 \lt 4$. Thus both exact equality and submultiplicativity with constant $1$ fail, and grade-$1$ vector pairs (ratio $1 \lt 2$) are strictly suboptimal for the conversion bound.
2. **Spin-Euclidean $\mathrm{Cl}_{0,n}$ for all $n \ge 3$:** Taking $X_\pm = 1 \pm e_1 e_2 e_3$ gives $\|X_\pm\|_2^2 = N_{\mathrm{conj}}(X_\pm) = 2$, $\|X_+^2\|_2^2 = N_{\mathrm{conj}}(X_+^2) = 8 \gt 4$, and $X_+ X_- = 0$. Moreover, $W = 1 + e_1 \in \mathrm{Cl}_{0,n}$ ($n \ge 1$) gives $N_{\mathrm{rev}}(W) = 0$ with $N_{\mathrm{rev}}(W^2) = -4 \ne 0$, and $Z = 1 + e_1 e_2 e_3 \in \mathrm{Cl}_{3,0}$ gives $N_{\mathrm{conj}}(Z) = 0$ with $N_{\mathrm{conj}}(Z^2) = -4 \ne 0$.
3. **Even Subalgebra $\mathrm{Cl}_{n,0}^+$ Simultaneous Triple-Norm Refutation ($n \ge 4$):** For $X_\pm = 1 \pm e_1 e_2 e_3 e_4 \in \mathrm{Cl}_{n,0}^+$, all three norms $N \in \{\|\cdot\|_2^2, N_{\mathrm{rev}}, N_{\mathrm{conj}}\}$ simultaneously satisfy $N(X_\pm) = 2$, $N(X_+^2) = 8 \gt 4$, and $N(X_+ X_-) = 0 \lt 4$.
4. **Indefinite Vector Pairs ($\mathrm{Cl}_{1,1}$):** Isotropic grade-$1$ vectors $u = e_1 + e_2$ and $v = e_1 - e_2$ satisfy $Q(u) = Q(v) = 0$, yet $u v = 2 - 2 e_1 e_2 \ne 0$ with $\|u v\|_2^2 = 8 \gt 4 = \|u\|_2^2 \|v\|_2^2$, $\|u^2\|_2^2 = 0$, and $N_{\mathrm{rev}}(u v) = 0$.
5. **Spectrum vs. Isometry Group $\mathrm{O}(V, Q)$:**
   - The scalar conversion-ratio spectrum is $\{1\}$ for $\bigl(p, q\bigr) \in \{\bigl(0,0\bigr), \bigl(0,1\bigr), \bigl(0,2\bigr)\}$ and $[0, C(p, q)]$ otherwise, never a group isomorphic to $\mathrm{O}(p, q)$.
   - Under the twisted adjoint action $\rho(U)(x) = \widehat{U} x U^{-1}$, $+1 \ne -1$ always lie in $\ker \rho$, making $\mathrm{Pin}(p, q) \to \mathrm{O}(p, q)$ a $2$-to-$1$ double cover rather than a bijection.
   - Already in $\mathrm{Cl}_{0,1} \cong \mathbb{C}$, the unit-norm group $\mathrm{U}(1) \cong S^1$ is infinite and $|\mathrm{Pin}(0, 1)| = 4 \ne 2 = |\mathrm{O}(1)|$.
   - In $\mathrm{Cl}_{3,0}$, the rational unit $U = \frac{3}{5} + \frac{4}{5} e_1 e_2 e_3$ satisfies $\widetilde{U} U = 1$ and $\|U\|_2^2 = 1$, acts trivially under $U v \widetilde{U} = v$, and sends $e_1$ under twisted conjugation to $\widehat{U} e_1 \widetilde{U} = -\frac{7}{25} e_1 - \frac{24}{25} e_2 e_3 \notin \mathbb{R}^3$.

### Sharp Salvage Theorem (Bott Periodicity)
For every signature $\bigl(p, q\bigr)$ with Artin–Wedderburn structure $\bigoplus_{r=1}^b M_m(\mathbb{D})$ ($\mathbb{D} \in \{\mathbb{R}, \mathbb{C}, \mathbb{H}\}$), the exact Euclidean conversion constant is

$$
C(p, q) = \sup_{X, Y \ne 0} \frac{\|X Y\|_2^2}{\|X\|_2^2 \|Y\|_2^2} = b \, m = 2^{(p + q + \delta(p - q \bmod 8)) / 2},
$$

attained by primitive idempotents $P^2 = P$, with $C(p, q) = 1$ if and only if $\bigl(p, q\bigr) \in \{\bigl(0, 0\bigr), \bigl(0, 1\bigr), \bigl(0, 2\bigr)\}$.

---

## 3. Repository Contents and Reproduction

- `SOURCE.md` — Original bilingual conjecture statement (unmodified).
- `main.tex`, `main.pdf` — Complete mathematical paper with proofs, counterexample summary tables, and Lean correspondence table.
- `verify.py` — Pure-Python (standard library only) exact rational and numerical verification suite.
- `lean/` — Zero-dependency Core Lean 4.19.0 formalization (`leanprover/lean4:v4.19.0`, `-DwarningAsError=true`):
  - `CliffordNormConjecture/Algebra.lean` — Recursive Clifford algebra $\mathrm{Cl}_R(\sigma)$, involutions, norms, and `OrderedCommRing Int` instance.
  - `CliffordNormConjecture/Positive.lean` — Contraction law, norm coincidences, grade-$1$ vector/versor multiplicativity, Hurwitz laws ($n \le 2$), and parallelogram doubling bound.
  - `CliffordNormConjecture/Counterexamples.lean` — Universal dimension-lifted refutations across $\mathrm{Cl}_{n,0}$, $\mathrm{Cl}_{0,n}$, $\mathrm{Cl}_{n,0}^+$, $\mathrm{Cl}_{1,1}$, and unit-group vs. isometry-group obstructions.
  - `CliffordNormConjecture.lean` — Master positive and refutation theorems (`conjecture_00000007603_positive_domain`, `conjecture_00000007603_refuted`, `conjecture_00000007603_int_nonvacuous`).
- `verification/` — Recorded build, axiom, toolchain, PDF, and Python verification logs, plus `SELF_REVIEW.md`.

### Verification Commands

```bash
# 1. Core Lean 4.19.0 formalization & axiom check
cd lean && lake build && lake env lean PrintAxioms.lean

# 2. Independent Python verification suite
python3 verify.py

# 3. LaTeX paper compilation
pdflatex -interaction=nonstopmode -halt-on-error main.tex
pdflatex -interaction=nonstopmode -halt-on-error main.tex
```
