# Conjecture 00000007602 — Resolution Package

## Problem Statement

**English.** Definition: The outer product as the fully antisymmetric part structure. Conjecture: The dimension-vanishing threshold of the outer product is exact and given by binomial zeros; and the realization of the threshold is full antisymmetrization. (binomial-zero outer-product vanishing threshold)

**中文。** 定义：外积为全反对称部分结构。猜想：外积的维数消没阈精确且阈值由二项式零点给出；且阈的实现为满反称。（外积消没阈二项式零点）

---

## Resolution Summary (Verdict: Conditionally True in Characteristic $0$ on $1$-Vectors; False Unconditionally)

Conjecture `00000007602` exhibits a sharp structural dichotomy depending on the base field characteristic, the algebraic interpretation of binomial zeros, and the grade of the multiplied factors:

1. **Conditional Positive Theorem (Grade-$1$ Vectors over Characteristic $0$ / Invertible $k!$):**
   Let $V \cong K^n$ be an $n$-dimensional vector space over a field $K$ in which $k! \cdot 1_K \in K^\times$ (in particular, any field of characteristic $0$ such as $\mathbb{Q}$ or $\mathbb{R}$ for all $k \in \mathbb{N}$), and interpret binomial zeros as the roots of the rational polynomial $\binom{x}{k} = \frac{x(x-1)\cdots(x-k+1)}{k!}$. Then the normalized full antisymmetrizer
   $$\Pi_k = \frac{1}{k!}\,\mathrm{Alt}_k : T^k(V) \to T^k(V), \qquad \mathrm{Alt}_k(T) = \sum_{\sigma \in S_k} \mathrm{sgn}(\sigma)\,\bigl(\sigma \cdot T\bigr)$$
   is an idempotent linear projection ($\Pi_k \circ \Pi_k = \Pi_k$) onto the $S_k$-sign-equivariant ("fully antisymmetric part") subspace $A^k_{\mathrm{sgn}}(V) \cong \Lambda^k(V)$ of exact dimension $\dim_K \Lambda^k(V) = \dim_K A^k_{\mathrm{sgn}}(V) = \binom{n}{k}$. Its vanishing threshold is exact and realized by $\Pi_k$:
   $$\Pi_k = 0 \iff A^k_{\mathrm{sgn}}(V) = \{0\} \iff \binom{n}{k} = 0 \iff k \gt n.$$

2. **Refutation of the Unqualified Conjecture (Three Independent Obstructions):**
   - **Obstruction 1 — Characteristic $2$ ($K = \mathbb{F}_2$), Loss of Any Finite Vanishing Threshold for $A^k_{\mathrm{sgn}}(V)$:**
     In $\mathbb{F}_2$, $+1 = -1$, so $\mathrm{sgn}(\sigma) \cdot 1_{\mathbb{F}_2} = 1_{\mathbb{F}_2}$ for all $\sigma \in S_k$. Thus the literal "fully antisymmetric part" $A^k_{\mathrm{sgn}}(\mathbb{F}_2^n)$ collapses to the $S_k$-invariant (symmetric) tensor space $\bigl((\mathbb{F}_2^n)^{\otimes k}\bigr)^{S_k}$ of dimension $\binom{n + k - 1}{k} \ge 1$. For **every** $n \ge 1$ and **every** $k \gt n$ (where $\binom{n}{k} = 0$), the diagonal tensor $e_0^{\otimes k} \in A^k_{\mathrm{sgn}}(\mathbb{F}_2^n)$ is non-zero; for instance, at $n = 2, k = 3$, $\binom{2}{3} = 0$ yet $\dim_{\mathbb{F}_2} A^3_{\mathrm{sgn}}(\mathbb{F}_2^2) = 4 \neq 0$, and at $n = 2, k = 2$, $\dim_{\mathbb{F}_2} A^2_{\mathrm{sgn}}(\mathbb{F}_2^2) = 3 \neq \binom{2}{2} = 1$.
   - **Obstruction 2 — Positive Characteristic $0 \lt p \le k \le n$, Breakdown of Full Antisymmetrization and Modular Binomial Zeros:**
     Whenever $\mathrm{char}(K) = p \le k$, $k! = 0$ in $K$: normalized antisymmetrization $\frac{1}{k!}\mathrm{Alt}_k$ does not exist, and unnormalized $\mathrm{Alt}_k$ satisfies $\mathrm{Alt}_k \circ \mathrm{Alt}_k = k!\,\mathrm{Alt}_k = 0$ (nilpotent, annihilating every already-alternating tensor such as $\omega_{01} = \mathrm{Alt}_2(e_0 \otimes e_1) \neq 0$ at $p = n = k = 2$). Moreover, for alternating tensors $\omega \in A^r_{\mathrm{sgn}}(K^n)$ and $\eta \in A^s_{\mathrm{sgn}}(K^n)$, shuffle factorization gives $\mathrm{Alt}_{r+s}(\omega \otimes \eta) = r!\,s!\,(\omega \wedge_{\mathrm{sh}} \eta)$, which vanishes prematurely below/at the threshold whenever $r \ge p$ and $r + s \le n$ (minimal witness: $p = 2, n = 3, r = 2, s = 1$, where $\binom{3}{3} = 1$ and $\mathrm{Alt}_3(e_0 \otimes e_1 \otimes e_2) \neq 0$, yet $\mathrm{Alt}_3(\omega_{01} \otimes e_2) = 0$). Likewise, modular Lucas zeros in $K$ decouple from exterior dimension: at $p = 2, n = 2, k = 1$, $\binom{2}{1} \cdot 1_{\mathbb{F}_2} = 0$ while $\dim_{\mathbb{F}_2} \Lambda^1(\mathbb{F}_2^2) = 2 \neq 0$.
   - **Obstruction 3 — Characteristic $0$ ($K = \mathbb{Q}$), Higher-Grade Multivectors in $\Lambda(\mathbb{Q}^n)$ and $\mathrm{Cl}_{n,0}(\mathbb{Q})$:**
     For homogeneous multivectors $A$ of grade $r$ and $B$ of grade $s$, the true outer product $A \wedge B = \langle A B \rangle_{r+s}$ obeys Koszul graded-commutativity $A \wedge B = (-1)^{rs} B \wedge A$ rather than factor antisymmetry:
     - *Premature vanishing at $k = n = 4$:* for $A = e_0 \wedge e_1$ and $B = e_2 \wedge e_3$ in $\Lambda(\mathbb{Q}^4)$ / $\mathrm{Cl}_{4,0}(\mathbb{Q})$, $\binom{4}{4} = 1$ and $A \wedge B = \langle A B \rangle_4 = e_0 \wedge e_1 \wedge e_2 \wedge e_3 \neq 0$, yet $\frac{1}{2}(A \wedge B - B \wedge A) = \frac{1}{2}(A B - B A) = 0$.
     - *Non-vanishing above the threshold at $k = 4 \gt n = 3$:* for $A = e_0 e_1$ and $B = e_1 e_2$ in $\mathrm{Cl}_{3,0}(\mathbb{Q})$, $\binom{3}{4} = 0$ and $A \wedge B = \langle A B \rangle_4 = 0$, yet $\frac{1}{2}(A B - B A) = e_0 e_2 \neq 0$.

---

## Package Structure

| Path | Description |
| :--- | :--- |
| `SOURCE.md` | Original problem statement (untouched) |
| `main.tex` / `main.pdf` | Publication-grade mathematical paper and compiled PDF |
| `verify.py` | Standalone Python 3.12 exact verification script (`fractions.Fraction` and $\mathbb{F}_p$) |
| `lean/lakefile.toml` | Lake package configuration (`-DwarningAsError=true`, zero external dependencies) |
| `lean/lean-toolchain` | Pinned toolchain `leanprover/lean4:v4.19.0` |
| `lean/Conjecture00000007602.lean` | Root Lean module bundling the complete resolution theorem |
| `lean/Conjecture00000007602/BinomialThreshold.lean` | Binomial zeros, falling factorials, monotone basis count, and pigeonhole principle |
| `lean/Conjecture00000007602/Antisymmetrization.lean` | $S_k$, inversion parity, $T^k(R^n)$, $\mathrm{Alt}_k$, coordinate duality, and positive theorem |
| `lean/Conjecture00000007602/Refutations.lean` | Exact $\mathbb{Q}$ and $\mathbb{F}_2$ rings, $\Lambda(R^n)$ / $\mathrm{Cl}_{n,0}(R)$, and all counterexample families |
| `verification/` | Build, axiom-audit, PDF compilation, and Python verification logs + `SELF_REVIEW.md` |

---

## Reproduction Commands

From the package root:

```bash
# 1. Exact computational verification (Python 3.12 standard library only)
python3 verify.py

# 2. Formal proof verification in Core Lean 4.19.0
cd lean && lake build

# 3. Compile LaTeX paper
pdflatex -interaction=nonstopmode -halt-on-error main.tex
pdflatex -interaction=nonstopmode -halt-on-error main.tex
```
