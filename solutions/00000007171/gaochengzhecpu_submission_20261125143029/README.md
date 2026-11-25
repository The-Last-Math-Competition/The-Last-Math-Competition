# Conjecture 00000007171 — Disproof, Positive Scope, and Formal Verification

## Verdict: **DISPROVED (FALSE)**

### Official Statement (`SOURCE.md`)

- **English:** *Definition: Constrained spectral extrema with fixed trace. Conjecture: The configuration of the maximal spectrum is the concentrated type, and the realization of the type is rank-one perturbation. (rank-one concentrated trace-fixed extrema)*
- **中文:** *定义：谱的约束极值：迹的固定。猜想：迹固定的极值：极大谱的构型为集中型且型的实现为秩一扰动。（迹固定秩一扰动集中极大构型谱）*

---

## Mathematical Summary

Conjecture `00000007171` studies constrained spectral extremal problems over symmetric / Hermitian $n \times n$ matrices $A$ subject to a fixed-trace constraint $\mathrm{tr}(A) = \sum_{i=1}^n \lambda_i = c$ ($n \ge 2$), asserting that (i) the maximal eigenvalue configuration has the **concentrated type** and (ii) its matrix realization is obtained via a **rank-one perturbation**.

While this statement reflects a valid classical phenomenon in one specific regime, the unqualified conjecture is **false** across all standard formulations of constrained fixed-trace spectral optimization:

1. **Positive Salvage & Non-Vacuity Theorem (Schur-Convex Extrema on One-Sided Trace Simplices):**
   - On the one-sided lower-bounded trace simplex $\Delta_{n,c}(a) = \{\lambda \in \mathbb{F}^n : \lambda_i \ge a,\; \sum_{i=1}^n \lambda_i = c\}$ ($n \ge 2$, $c \gt n a$), the concentrated configuration
     $$\lambda^{\mathrm{conc}} = \bigl(c - (n - 1)a,\, a,\, \dots,\, a\bigr)$$
     majorizes every $\lambda \in \Delta_{n,c}(a)$ ($\lambda \prec \lambda^{\mathrm{conc}}$), maximizes every separable convex spectral functional $\sum_{i=1}^n \phi(\lambda_i)$, and is the **unique** global maximizer (up to coordinate permutation) of $\|A\|_F^2 = \sum_{i=1}^n \lambda_i^2$ via the exact identity
     $$\sum_{i=1}^n (\lambda_i^{\mathrm{conc}})^2 - \sum_{i=1}^n \lambda_i^2 = \sum_{i \neq j} (\lambda_i - a)(\lambda_j - a) \ge 0.$$
   - For any unit vector $u \in \mathbb{F}^n$ ($\|u\|_2 = 1$), the **trace-changing** rank-one perturbation $A(u) = a I_n + (c - n a) u u^\top$ satisfies $\mathrm{rank}(A(u) - a I_n) = 1$, $\mathrm{tr}(A(u)) = c$, $A(u) \succeq a I_n$, and orthogonally realizes $\lambda^{\mathrm{conc}}$ over any linearly ordered field $\mathbb{F}$ via a square-root-free Householder reflection.

2. **Refutation R1 — Schur-Concave Fixed-Trace Spectral Maxima Are Uniform and Full-Rank:**
   - On the positive semidefinite fixed-trace simplex $\{A \succeq 0 : \mathrm{tr}(A) = c\}$ ($n \ge 2$, $c \gt 0$), canonical spectral maximization objectives including $\det(A) = \prod_{i=1}^n \lambda_i$, $e_2(A) = \sum_{i \lt j} \lambda_i \lambda_j$, and von Neumann entropy $S(A) = -\mathrm{tr}(A \log A)$ achieve their **unique** global maximum at the **uniform** full-rank scalar matrix $A^* = \frac{c}{n} I_n$ with spectrum $\lambda^{\mathrm{unif}} = (c/n, \dots, c/n)$ ($\det A^* = (c/n)^n \gt 0$, $e_2(A^*) = \frac{n-1}{2n} c^2 \gt 0$).
   - By contrast, every concentrated rank-one PSD matrix $c u u^\top$ achieves the **global minimum** $\det = 0$ and $e_2 = 0$.

3. **Refutation R2 — Box-Constrained Schur-Convex & Majorization Extrema Fail Both Clauses (Complete Classification):**
   - On the two-sided spectral polytope $\mathcal{B}_{n,c}(a,b) = \{a \le \lambda_i \le b : \sum_{i=1}^n \lambda_i = c\}$ ($a \lt b$, $n a \lt c \lt n b$), the unique nonincreasing majorization-greatest spectrum is the saturated profile $\lambda^{\mathrm{box}} = (b, \dots, b, a + r, a, \dots, a)$ ($q = \lfloor (c - n a)/(b - a) \rfloor$ copies of $b$).
   - **Exact Classification Theorem:** A symmetric matrix $A$ realizing $\lambda^{\mathrm{box}}$ can be written as $\alpha I_n + R$ with $\mathrm{rank}(R) \le 1$ (for *any* scalar $\alpha$) **if and only if** $c \le (n - 1)a + b$ or $c \ge a + (n - 1)b$ (and is floor-concentrated iff $c \le (n - 1)a + b$).
   - Whenever $\lparen n - 1)a + b \lt c \lt a + (n - 1)b$ — already at the **sharp minimal dimension $n = 3$** on $\mathcal{B}_{3,3}(0,2)$ with $\lambda^* = (2, 1, 0)$, and on the Ky Fan $2$-frame polytope $\mathcal{B}_{4,2}(0,1)$ with $\lambda^* = (1, 1, 0, 0)$ — $\lambda^{\mathrm{box}}$ fails even weak single-spike concentration and satisfies $\mathrm{rank}(A - \alpha I_n) \ge 2$ for **every** scalar $\alpha$.

4. **Refutation R3 — Fixed-Trace Rank-One Perturbation Rigidity:**
   - Every symmetric matrix $R$ with $\mathrm{rank}(R) \le 1$ satisfies $\|R\|_F^2 = (\mathrm{tr}\, R)^2$. Hence $\mathrm{tr}(R) = 0 \implies R = 0$: **no nonzero trace-preserving symmetric rank-one perturbation exists** within $\{A \in \mathrm{Sym}_n(\mathbb{F}) : \mathrm{tr}(A) = c\}$. Any deformation between distinct fixed-trace symmetric matrices requires $\mathrm{rank}(A - A_0) \ge 2$ (attained sharply by Robin–Muirhead rank-$2$ transfers $\delta(e_1 e_1^\top - e_2 e_2^\top)$), while non-symmetric traceless rank-one perturbations $R = u v^\top$ satisfy $R^2 = 0$ and cannot alter scalar spectra.

---

## Package Structure

```text
.
├── .gitignore
├── SOURCE.md                       # Untouched copy of official conjecture 00000007171
├── README.md                       # Package overview and reproduction instructions
├── main.tex                        # LaTeX mathematical manuscript
├── main.pdf                        # Compiled PDF report
├── verify.py                       # Exact rational + floating-point verification suite (Python 3)
├── lean/
│   ├── lean-toolchain              # leanprover/lean4:v4.19.0
│   ├── lakefile.toml               # Core Lean 4 configuration (-DwarningAsError=true)
│   ├── lake-manifest.json          # Zero external dependencies
│   └── Main.lean                   # Self-contained formalization and #print axioms audit
└── verification/
    ├── lean-version.log
    ├── lake-build.log
    ├── lean-axioms.log
    ├── pdf-build.log
    ├── python-verify.log
    └── SELF_REVIEW.md
```

---

## Reproduction Commands

1. **Core Lean 4 (`v4.19.0`) Build & Axiom Audit:**
   ```bash
   cd lean
   lake build
   lake env lean -DwarningAsError=true Main.lean
   ```

2. **Python Independent Verification:**
   ```bash
   python verify.py
   ```

3. **LaTeX PDF Compilation:**
   ```bash
   pdflatex -interaction=nonstopmode -halt-on-error main.tex
   pdflatex -interaction=nonstopmode -halt-on-error main.tex
   ```
