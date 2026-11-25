# Conjecture 00000007163 — Resolution Package

## Verdict: **FALSE** (Disproved)

Conjecture `00000007163` asserts within Perron–Frobenius theory that (1) a strict gap between the spectral radius and the next eigenvalue requires almost-irreducible primitivity, and (2) the bound of the spectral gap is the positivity modulus.

We prove that **both clauses are false** across every standard matrix class (nonnegative $A \ge 0$, primitive, strictly positive $A \gt 0$, symmetric, and row-stochastic), both standard spectral-gap definitions — the modulus gap $\gamma_{\mathrm{mod}}(A) := \rho(A) - \max_{\lambda \neq \rho(A)} |\lambda|$ and the real gap $\gamma_{\mathrm{re}}(A) := \rho(A) - \max_{\lambda \neq \rho(A)} \mathrm{Re}(\lambda)$ — both inequality directions (upper bound, lower bound, and sharp infimum), and all three canonical positivity moduli in Perron–Frobenius theory. Alongside explicit integer-eigenvalue counterexamples and infinite parametric families, we establish the sharp positive boundary theorems that explain where and why each claim fails.

---

## Mathematical Summary

### 1. Refutation of Clause 1 (Almost-Irreducible Primitivity Is Not Necessary)

By Frobenius normal form (`main.pdf`, Theorem 2.2), a nonnegative matrix $A \ge 0$ with $\rho(A) \gt 0$ satisfies $\gamma_{\mathrm{mod}}(A) \gt 0$ if and only if $A$ has a **unique** Frobenius block $B_{r_0}$ attaining $\rho(B_{r_0}) = \rho(A)$, $B_{r_0}$ is primitive, and every other block satisfies $\rho(B_r) \lt \rho(A)$ — **not** $\rho(B_r) = 0$ as almost-irreducible primitivity demands:

- **Completely reducible diagonal counterexample:** $A_{\mathrm{diag}} = \mathrm{diag}(3, 1)$ has two disconnected positive components (failing irreducibility, primitivity, single-essential-class almost-irreducibility, and block-supported primitivity), yet $\sigma(A_{\mathrm{diag}}) = \{3, 1\}$ and $\gamma_{\mathrm{mod}}(A_{\mathrm{diag}}) = \gamma_{\mathrm{re}}(A_{\mathrm{diag}}) = 2 \gt 0$.
- **Reducible matrix with an imprimitive periodic block:** $A_{\mathrm{per}} = \mathrm{diag}(3, P_2)$ ($3 \times 3$, where $P_2$ is the period-$2$ swap) fails all four irreducibility/primitivity predicates and contains an oscillating period-$2$ component, yet $\sigma(A_{\mathrm{per}}) = \{3, 1, -1\}$ gives $\gamma_{\mathrm{mod}}(A_{\mathrm{per}}) = \gamma_{\mathrm{re}}(A_{\mathrm{per}}) = 2 \gt 0$.
- **Irreducible imprimitive counterexample for the real gap:** $A_{\mathrm{cyc}} = \begin{pmatrix} 0 & 2 \\ 2 & 0 \end{pmatrix}$ is irreducible of period $2$ (not primitive), with $\sigma(A_{\mathrm{cyc}}) = \{2, -2\}$ and $\gamma_{\mathrm{re}}(A_{\mathrm{cyc}}) = 4 \gt 0$.

### 2. Refutation of Clause 2 and Sharp Boundary Theorems Across Positivity Moduli

Let $n \ge 2$ and consider the three standard positivity moduli:
1. **Entrywise positivity floor:** $m(A) := \min_{1 \le i,j \le n} a_{ij}$;
2. **Markov–Doeblin column-minimum sum:** $\delta(A) := \sum_{j=1}^n \min_{1 \le i \le n} a_{ij} \ge n \, m(A)$;
3. **Scale-invariant moduli:** entry ratio $\mu_{\mathrm{ratio}}(A) := m(A) / M(A)$ and Birkhoff–Hopf contraction gap $\kappa_{\mathrm{BH}}(A) := 2 / (\sqrt{K(A)} + 1)$.

- **Vanishing floor on primitive nonnegative matrices:** $A_{\mathrm{prim}} = \begin{pmatrix} 2 & 3 \\ 1 & 0 \end{pmatrix}$ satisfies $A_{\mathrm{prim}}^2 = \begin{pmatrix} 7 & 6 \\ 2 & 3 \end{pmatrix} \gt 0$ (primitive), with $\sigma(A_{\mathrm{prim}}) = \{3, -1\}$ and $\gamma_{\mathrm{mod}}(A_{\mathrm{prim}}) = 2$, whereas $m(A_{\mathrm{prim}}) = 0$ and $\delta(A_{\mathrm{prim}}) = 1 \lt 2$.
- **Failure as an upper bound:** For all $K \ge 1$, symmetric positive $A_{\mathrm{sym,rk1}}(K) = \begin{pmatrix} K^2 & K \\ K & 1 \end{pmatrix}$ has $m = 1$ and $\gamma = K^2 + 1 \to +\infty$, while $A_K = \begin{pmatrix} K & K \\ 1 & 1 \end{pmatrix}$ has $m = 1$, $\delta = 2$, and $\gamma = K + 1 \to +\infty$. Even on symmetric doubly stochastic positive matrices ($\rho(P) = 1$), $P_{\mathrm{stoch}} = \frac{1}{10}(3 J_4 - 2 R_4)$ has $\sigma(P_{\mathrm{stoch}}) = \{1, \frac{1}{5}, \frac{1}{5}, -\frac{1}{5}\}$ and $m(P_{\mathrm{stoch}}) = \frac{1}{10} \lt \delta(P_{\mathrm{stoch}}) = \frac{2}{5} \lt \gamma(P_{\mathrm{stoch}}) = \frac{4}{5}$.
- **Failure of $m(A)$ as the sharp lower bound on $A \gt 0$:** Using Perron diagonal similarity and Deutsch–Zenger convex-combination contraction, we prove universally for **every** $n \ge 2$ and **every** $A \in \mathbb{R}^{n \times n}_{\gt 0}$ that $\gamma_{\mathrm{mod}}(A) \gt m(A)$ (strict inequality), and for $n = 2$ we prove the sharp bound $\gamma_{\mathrm{mod}}(A) \ge 2 m(A)$, so $\inf_{m(A) = m} \gamma_{\mathrm{mod}}(A) = 2m \neq m$.
- **Failure of $\delta(A)$ and $n \, m(A)$ as lower bounds on general $A \gt 0$:** While $\gamma_{\mathrm{mod}}(A) \ge \delta(A) \ge n \, m(A)$ holds for constant-row-sum matrices, it fails on symmetric positive matrices for every $n \ge 3$: $A_{\mathrm{low},3} = \begin{pmatrix} 7 & 2 & 2 \\ 2 & 7 & 2 \\ 2 & 2 & 2 \end{pmatrix}$ has $\sigma = \{10, 5, 1\}$, $m = 2$, $\delta = 6$, and $\gamma = 5 \lt 6$; $A_{\mathrm{low},4} = J_4 + 3(E_{11} + E_{22})$ has $\sigma = \{6, 3, 1, 0\}$, $m = 1$, $\delta = 4$, and $\gamma = 3 \lt 4$; and $\gamma(J_n + a(E_{11} + E_{22})) / \delta \to 2/n \to 0$.
- **Failure of scale-invariant moduli $\mu_{\mathrm{ratio}}$ and $\kappa_{\mathrm{BH}}$:** Scaling $A \mapsto c A$ ($c \gt 0$) leaves $\mu_{\mathrm{ratio}}$ and $\kappa_{\mathrm{BH}}$ invariant while scaling $\gamma(cA) = c\gamma(A)$. Even for the relative gap $\gamma_{\mathrm{mod}}(A)/\rho(A)$, the integer-spectrum family $A_{\mathrm{rat}}(p) = \begin{pmatrix} p^2 + 2p - 3 & 2p \\ 2p & 2p + 1 \end{pmatrix}$ ($p \ge 2$, $\sigma = \{(p+1)^2, 2p - 3\}$) satisfies $\gamma_{\mathrm{mod}}/\rho = \frac{p^2 + 4}{(p + 1)^2} \to 1$ while $\mu_{\mathrm{ratio}} \to 0$ and $\kappa_{\mathrm{BH}} \to 0$.

---

## Package Contents

- `SOURCE.md` — Original conjecture statement (unmodified).
- `main.tex` / `main.pdf` — Self-contained mathematical paper proving all counterexamples, asymptotic families, and positive boundary theorems.
- `verify.py` — Standalone Python 3 verification script (standard library only) cross-checking Faddeev–Leverrier characteristic polynomials against Laplace cofactor determinants over `fractions.Fraction`, graph/Wielandt primitivity predicates, and $2{,}000$ random matrix stress tests.
- `lean/` — Core Lean 4.19.0 formalization (`leanprover/lean4:v4.19.0`, zero external dependencies, `-DwarningAsError=true`, zero `sorry`, zero `native_decide`):
  - `Conjecture00000007163/PFMatrix.lean` — Gaussian integers `GaussInt` ($\mathbb{Z}[i]$), weighted convex-combination norm bounds, `IMat n`, `matPow`, recursive Laplace cofactor determinant `det`, `charPolyEval`, and Perron–Frobenius predicates/moduli.
  - `Conjecture00000007163/PositiveBounds.lean` — Deutsch–Zenger contraction (`pairwise_weight_contraction`), Markov–Doeblin constant-row-sum bound (`constantRowSum_gap_ge_doeblin`), universal strict floor separation (`strictlyPositive_gap_gt_posModulus`), and sharp $2 \times 2$ bound (`twoByTwo_gap_ge_two_posModulus`).
  - `Conjecture00000007163/Counterexamples.lean` — Explicit counterexamples and infinite parametric families (`diag31`, `periodicBlock3`, `cycle2`, `primZeroMod`, `unbounded_gap_fixed_modulus_families`, `doeblinFail3`, `doeblinFail4`, `stochasticScaled4`, `ratioGapFamily_arbitrage`).
  - `Conjecture00000007163.lean` — Top-level positive boundary exports and master disproof theorem `conjecture_00000007163_disproved`.
- `verification/` — Build and audit logs (`lake-build.log`, `lean-axioms.log`, `lean-version.log`, `pdf-build.log`, `python-verify.log`, `SELF_REVIEW.md`).
