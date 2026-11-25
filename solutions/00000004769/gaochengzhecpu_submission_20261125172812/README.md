# Conjecture 00000004769 — Resolution Package

## Verdict: **FALSE** (Disproved)

Conjecture `00000004769` defines annular noncrossing partitions as noncrossing structures on the torus and claims that at thickness two, the $q$-analogue of their count is an explicit product of cyclotomic polynomials indexed by the annular thickness and specializing to the classical values.

We prove that this conjecture is **false** across every standard interpretation, while characterizing the exact positive sub-phenomena (individual through-block strata, connected annular permutations, and restricted pair matchings) that explain why individual pieces factor into cyclotomic polynomials whereas full annular noncrossing partitions do not.

---

## Mathematical Summary

### 1. Topological Misidentification in the Definition
- **Annulus vs. Closed Torus:** Genuine annular noncrossing partitions $\mathrm{NC}_A(p, r)$ (Mingo–Nica, 2004) are genus-$0$ noncrossing structures on the compact **annulus** $A = S^1 \times [0, 1]$ ($g = 0$, $b = 2$ boundary components) relative to the two-cycle boundary permutation $\gamma_{p,r} = (1 \dots p)(p+1 \dots p+r)$, NOT on the closed **torus** $T^2 = S^1 \times S^1$ ($g = 1$, $b = 0$). Although $\chi(A) = \chi(T^2) = 0$, the surfaces are non-homeomorphic and their partition counts diverge: already on $5$ marked points $\lvert\mathrm{NC}_A(4, 1)\rvert = 49 \ne 52 = \lvert\mathrm{NC}_{g \le 1}(5)\rvert$, and on $6$ marked points $\lvert\mathrm{NC}_A(4, 2)\rvert = 189 \ne 203 = \lvert\mathrm{NC}_{g \le 1}(6)\rvert$.

### 2. Thickness-Two Enumeration and the Positive Stratum Dichotomy
At thickness two ($r = 2$, $p \ge 1$), decomposing $\mathrm{NC}_A(p, 2) = \mathrm{NC}_A^{(0)}(p, 2) \sqcup \mathrm{NC}_A^{(1)}(p, 2) \sqcup \mathrm{NC}_A^{(2)}(p, 2)$ by the number $k \in \{0, 1, 2\}$ of through-blocks yields

$$
\lvert\mathrm{NC}_A(p, 2)\rvert = \frac{7p^2 + 9p + 14}{2(p + 1)(p + 2)}\binom{2p}{p} = 5,\, 15,\, 52,\, 189,\, 702,\, 2640,\, 10010,\, 38181,\, \dots \quad (p \ge 1).
$$

- **Positive diagnostic regimes:** Each individual through-block stratum $Q^{(0)}_{p,2}(q) = \Phi_4(q) C_p(q)$, $Q^{(1)}_{p,2}(q) = \Phi_3(q) \left[\begin{smallmatrix} 2p-1 \\ p-1 \end{smallmatrix}\right]_q$, and $Q^{(2)}_{p,2}(q) = \Phi_4(q)\frac{[p]_q [p-1]_q}{[p+1]_q [p+2]_q}\left[\begin{smallmatrix} 2p \\ p \end{smallmatrix}\right]_q$, as well as the connected **permutation** $q$-count $S^{\mathrm{conn}}_{p,2}(q) = \frac{[p]_q}{[p+2]_q}\left[\begin{smallmatrix} 2p \\ p \end{smallmatrix}\right]_q \left[\begin{smallmatrix} 4 \\ 2 \end{smallmatrix}\right]_q$ and the restricted **pair-matching** $q$-count $\left[\begin{smallmatrix} 2m+1 \\ m \end{smallmatrix}\right]_q$ for $\mathrm{NC}_{A,2}(2m, 2)$, *is* an explicit product of cyclotomic polynomials in $\mathbb{Z}[q]$.

### 3. Complete Disproof for Annular Noncrossing Partitions $\mathrm{NC}_A(p, 2)$
- **Parameter-indexing contradiction:** Fixing thickness $r = 2$ cannot index the unbounded sequence $\lvert\mathrm{NC}_A(p, 2)\rvert$; moreover, any product of cyclotomic polynomials with orders $1 \le d_j \le 2$ evaluates at $q = 1$ to $0$ or $2^s$, never matching $5, 15, 52, \dots$.
- **Universal failure of poset rank and co-rank $q$-analogues:** For every $p \ge 1$, neither $R_{p,2}(q) = \sum_{\pi \in \mathrm{NC}_A(p,2)} q^{\lvert\pi\rvert - 1}$ nor $\tilde{R}_{p,2}(q) = \sum_{\pi \in \mathrm{NC}_A(p,2)} q^{p + 2 - \lvert\pi\rvert}$ is a product of cyclotomic polynomials:
  - At $p = 1$, $R_{1,2}(q) = 1 + 3q + q^2$ has degree $2 \lt 4$ (and real roots $\frac{-3 \pm \sqrt{5}}{2}$ off $\lvert z\rvert = 1$), whereas $R_{1,2}(1) = 5$ requires $\Phi_{5^k}$ of degree $\ge 4$.
  - For all $p \ge 2$, $[q^1]R_{p,2} = 2p^2 - 2p + 3$ whereas $[q^p]R_{p,2} = \binom{p+2}{2}$, with strict gap $\frac{(p-1)(3p-4)}{2} \gt 0$; hence $R_{p,2}(q)$ and $\tilde{R}_{p,2}(q)$ are strictly non-palindromic, whereas every cyclotomic product with $F(1) \ge 1$ is palindromic.
- **Failure of $q$-strata sums, monomial shifts, and rational $q$-substitutions:** Both unshifted and $q^2$-weighted Mingo–Nica $q$-sums have constant term $\ge 2$, every monomial-shifted combination $q^a Q^{(0)}_{p,2}(q) + q^b Q^{(1)}_{p,2}(q) + q^c Q^{(2)}_{p,2}(q)$ ($a,b,c \in \mathbb{N}$) fails cyclotomic factorization for $p \in \{1, 2, 3\}$, and $\frac{[7p^2+9p+14]_q}{[2]_q[p+1]_q[p+2]_q}\left[\begin{smallmatrix} 2p \\ p \end{smallmatrix}\right]_q \notin \mathbb{Z}[q]$ already at $p = 2$.
- **Prime-divisor degree and cyclotomic-order obstructions:** Because $7p^2 + 9p + 14$ is an irreducible quadratic ($\Delta = -311$), large prime divisors force any cyclotomic product $F(q) = \prod_j \Phi_{d_j}(q)$ with $F(1) = \lvert\mathrm{NC}_A(p, 2)\rvert$ to satisfy $\deg F \ge 14$ and $\max_j d_j \ge 13$ at $p = 3$ ($\lvert\mathrm{NC}_A(3,2)\rvert = 52 = 2^2 \cdot 13$, exceeding $\binom{5}{2} = 10$ and $p^2 + 2 = 11$), $\deg F \ge 112$ and $\max_j d_j \ge 89$ at $p = 8$ ($\lvert\mathrm{NC}_A(8,2)\rvert = 38181 = 3 \cdot 11 \cdot 13 \cdot 89$, exceeding $p^2 + 2 = 66$), and $\deg F \ge 359$ and $\max_j d_j \ge 331$ at $p = 9$ ($\lvert\mathrm{NC}_A(9,2)\rvert = 146302 = 2 \cdot 13 \cdot 17 \cdot 331$, exceeding $p^2 + 2 = 83$).

---

## Package Contents

- `SOURCE.md` — Original conjecture statement (unmodified).
- `main.tex` / `main.pdf` — Complete mathematical paper proving the positive stratum dichotomy and full disproof.
- `verify.py` — Standalone Python 3 verification script (standard library only) cross-checking ribbon-graph enumerations, Mingo–Nica closed forms, cyclotomic factorizations, monomial shifts, and prime-divisor bounds.
- `lean/` — Core Lean 4.19.0 formalization (`leanprover/lean4:v4.19.0`, zero external dependencies, `-DwarningAsError=true`, zero `sorry`, zero `native_decide`):
  - `Conjecture00000004769/Polynomial.lean` — First-principles integer polynomial ring $\mathbb{Z}[q]$, evaluation, palindromicity, and exact monic Euclidean division.
  - `Conjecture00000004769/Cyclotomic.lean` — Constructive cyclotomic polynomials $\Phi_n(q)$ for all $n \ge 1$, integer Pseudo-Bezout proof of $q^n - 1 = \prod_{d \mid n} \Phi_d(q)$, palindromicity for $d \ge 2$, exact value $\Phi_d(1)$, and universal prime-power degree/order lower bounds.
  - `Conjecture00000004769/Annular.lean` — Surface invariants, executable Mingo–Nica ribbon-graph enumeration, universal all-$p$ rank non-palindromicity, and universal shift disproof at $p = 1$.
  - `Conjecture00000004769.lean` — Positive non-vacuity theorem (`positive_strata_and_pair_cyclotomic`) and master disproof theorem (`conjecture_00000004769_disproved`).
- `verification/` — Build and verification logs (`lake-build.log`, `lean-axioms.log`, `lean-version.log`, `pdf-build.log`, `python-verify.log`, `SELF_REVIEW.md`).
