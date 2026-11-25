# Conjecture 00000004763 — Disproof and Formal Verification

**Verdict:** **FALSE** (refuted in all four constituent claims, with machine-checked formal proofs in Core Lean 4.19.0 and exact rational verification in Python).

---

## 1. Problem Summary

Conjecture `00000004763` (`SOURCE.md`, given identically in English and Chinese) considers the conversion between Speicher's free cumulants $\kappa_n$ (governed by noncrossing partitions $\mathrm{NC}_n$) and classical cumulants $c_n$ (governed by all set partitions $\Pi_n$):

$$
m_n = \sum_{\pi \in \Pi_n} \prod_{B \in \pi} c_{\lvert B \rvert} = \sum_{\pi \in \mathrm{NC}_n} \prod_{B \in \pi} \kappa_{\lvert B \rvert} \qquad \bigl(n \ge 1\bigr).
$$

It conjectures four properties of the free-classical cumulant conversion:
1. **Low-order rational combination:** The conversion is always a low-order rational combination.
2. **Weighted crossing-pair counts:** The conversion coefficients are determined by weighted counts of crossing pairs.
3. **Initial nontrivial coefficients:** The first two nontrivial conversion coefficients are $1$ and $-1$.
4. **Finite inverse bandwidth:** The associated conversion matrix is invertible over the field of rational functions, and its inverse has finite bandwidth (finite bandwidth of the Stirling-type triangle).

---

## 2. Mathematical Resolution

### Why Low Orders ($n \le 4$) Were Misleading
For $n \in \{1, 2, 3\}$, no two disjoint blocks of $\{1, \dots, n\}$ can cross, so $\Pi_n = \mathrm{NC}_n$ and $\kappa_n = c_n$. At $n = 4$, $\Pi_4 \setminus \mathrm{NC}_4$ consists of the unique crossing pairing $\{\{1,3\},\{2,4\}\}$, yielding

$$
\kappa_4 = c_4 + c_2^2, \qquad c_4 = \kappa_4 - \kappa_2^2.
$$

Beyond $n = 4$, the exact conversion formulas are governed by the crossing graph $G(\pi)$ on the blocks of $\pi \in \Pi_n$:

$$
\kappa_n(c) = \sum_{\pi \in \Pi_n^{\mathrm{conn}}} \prod_{B \in \pi} c_{\lvert B \rvert}, \qquad c_n(\kappa) = \sum_{\pi \in \Pi_n^{\mathrm{conn}}} (-1)^{\lvert \pi \rvert - 1} T_{G(\pi)}(1, 0) \prod_{B \in \pi} \kappa_{\lvert B \rvert},
$$

where $\Pi_n^{\mathrm{conn}}$ consists of partitions with connected crossing graph and $T_{G(\pi)}(1, 0)$ is the Tutte activity (number of acyclic orientations with a prescribed unique source). Every one of the four conjectured claims fails:

1. **Refutation of Claim 1 (Unbounded Algebraic Degree and Index Depth):**
   - Along the Gaussian ray $c^{(t)} = (0, t, 0, 0, \dots)$, $\kappa_{2d}\bigl(c^{(t)}\bigr) = a_d t^d$, where $a_d$ satisfies Stein's recurrence $a_1 = 1$, $a_d = (d - 1)\sum_{j=1}^{d-1} a_j a_{d-j} \ge (d - 1)! \ge 1$ ($1, 1, 4, 27, 248, \dots$).
   - Along the Wigner semicircle ray $\kappa^{(t)} = (0, t, 0, 0, \dots)$, $c_{2d}\bigl(\kappa^{(t)}\bigr) = b_d t^d$, where $b_d$ satisfies $2d = \sum_{j=1}^d \frac{b_j}{(2j-1)!}\frac{d!}{(d-j)!}\frac{(d+1)!}{(d+1-j)!}$ and is nonzero for infinitely many $d$ ($1, -1, 5, -56, 1092, \dots$).
   - Consequently, for every degree bound $D$, neither direction can be represented uniformly by polynomials or even rational functions $P(t)/Q(t)$ with $\deg P \le D$ and $\deg Q \le D$. Moreover, for $n \ge 5$, $[c_{n-2}c_2]\kappa_n(c) = \frac{n(n-3)}{2} \gt 0$, so the index depth $n - 2$ is also unbounded.

2. **Refutation of Claim 2 (Crossing-Pair Counts Do Not Determine Weights):**
   - At $n = 8$, among perfect matchings of $\{1, \dots, 8\}$ (all of block-size signature $[2, 2, 2, 2]$):
     - With $\mathrm{cr}(\pi) = 3$ crossing pairs, $\pi_{\mathrm{disc}} = \{\{1,8\},\{2,5\},\{3,6\},\{4,7\}\}$ ($K_1 \sqcup K_3$, disconnected) has weights $\bigl(0, 0\bigr)$, whereas $\pi_{\mathrm{tree}} = \{\{1,7\},\{2,6\},\{3,5\},\{4,8\}\}$ ($K_{1,3}$, connected tree) has weights $\bigl(+1, -1\bigr)$.
     - Even restricting to *connected* partitions with $\mathrm{cr}(\pi) = 4$, $\pi_{\mathrm{paw}} = \{\{1,7\},\{2,5\},\{3,6\},\{4,8\}\}$ has $T_{\mathrm{paw}}(1,0) = 2$ (weight $-2$ in $c_8(\kappa)$), whereas $\pi_{C_4} = \{\{1,6\},\{2,5\},\{3,8\},\{4,7\}\}$ has $T_{C_4}(1,0) = 3$ (weight $-3$ in $c_8(\kappa)$).

3. **Refutation of Claim 3 (First Two Nontrivial Coefficients Are Not $1$ and $-1$):**
   - In $c \mapsto \kappa(c)$, all coefficients are strictly positive integers, starting with $+1$ ($\kappa_4 = c_4 + c_2^2$) and $+5$ ($\kappa_5 = c_5 + 5 c_3 c_2$); $-1$ never occurs.
   - In $\kappa \mapsto c(\kappa)$, the first two nontrivial coefficients are $-1$ ($c_4 = \kappa_4 - \kappa_2^2$) and $-5$ ($c_5 = \kappa_5 - 5 \kappa_3 \kappa_2$), or $\bigl(-1, -9, +5\bigr)$ on centered even cumulants. The numbers $+1$ and $-1$ belong to opposite directions at $n = 4$, not to a single conversion.

4. **Refutation of Claim 4 (Unbounded Inverse Bandwidth of All Conversion Triangles):**
   - **Stirling and Narayana triangles:** $\bigl(S^{-1}\bigr)_{n,1} = (-1)^{n-1}(n-1)! \ne 0$ ($\mathrm{bw}_n = n - 1$), and $N^{-1}$ likewise has unbounded lower bandwidth.
   - **Block-count conversion triangles $T_{\mathrm{cl}\to\mathrm{fr}} = N^{-1}S$ and $T_{\mathrm{fr}\to\mathrm{cl}} = S^{-1}N$:** We prove the closed-form identity
     $$
 \bigl(S^{-1}N\bigr)_{n,2} = (-1)^{n-1}(n - 2)!\bigl(H_{n-2} - 1\bigr) \ne 0 \qquad \bigl(n \ge 4\bigr),
 $$
     giving $\mathrm{bw}_n\bigl((N^{-1}S)^{-1}\bigr) = n - 2 \to \infty$, while $2^{n-1} - 1 = S(n,2) = \sum_{k=2}^n N(n,k)(N^{-1}S)_{k,2}$ proves that $\bigl(S^{-1}N\bigr)^{-1} = N^{-1}S$ also has unbounded lower bandwidth.
   - **Bell/Kreweras triangles $B(c), B^{\mathrm{NC}}(\kappa)$, Jacobian $J = \partial\kappa/\partial c$, and moment-recurrence matrices $T_{\mathrm{rec}}(m) = L_{\mathrm{fr}}(m)^{-1}L_{\mathrm{cl}}(m)$ over $\mathbb{Q}(c_1, c_2, \dots) = \mathbb{Q}(m_1, m_2, \dots)$:** Specializing $B(c)$ and $B^{\mathrm{NC}}(c)$ at $c_j = 1$ reduces them to $S$ and $N$, while $[m_{n-2}]\bigl(T_{\mathrm{rec}}(m)^{\pm 1}\bigr)_{n,2} = \pm(n - 3) \ne 0$ for all $n \ge 4$, yielding unbounded bandwidth $n - 2$ in every case.

---

## 3. Package Layout and Verification Commands

| Path | Description |
| :--- | :--- |
| `SOURCE.md` | Original untouched problem statement (English and Chinese) |
| `main.tex` / `main.pdf` | Full mathematical exposition and disproof paper |
| `verify.py` | Standalone exact rational Python verification suite ($n \le 15$) |
| `lean/Conjecture00000004763/Basic.lean` | Core moment-cumulant systems and mutual inversion proofs |
| `lean/Conjecture00000004763/LowOrderAndCrossing.lean` | Symbolic identities ($n \le 6$), nonlinearity, Claims 2 and 3 |
| `lean/Conjecture00000004763/UnboundedDegree.lean` | Gaussian/Wigner rays, Catalan identity, Claim 1 disproof |
| `lean/Conjecture00000004763/InverseBandwidth.lean` | Unitriangular matrices, Stirling/Narayana/recurrence bandwidths (Claim 4) |
| `lean/Conjecture00000004763.lean` | Root module exporting `conjecture_00000004763_positive_foundations` and `conjecture_00000004763_disproof` |
| `verification/` | Build logs (`lake-build.log`, `lean-axioms.log`, `lean-version.log`, `pdf-build.log`, `python-verify.log`) and `SELF_REVIEW.md` |

To reproduce all checks from scratch:
- **Python verification:** run `python verify.py` from the package root.
- **Lean 4.19.0 formal verification:** run `lake build` inside `lean/` (configured with `leanprover/lean4:v4.19.0` and `-DwarningAsError=true`, zero external dependencies).
- **PDF build:** run `pdflatex main.tex` twice from the package root.
