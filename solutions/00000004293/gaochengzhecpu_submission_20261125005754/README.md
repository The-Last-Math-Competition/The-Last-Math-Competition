# Conjecture 00000004293 — Disproof and Complete Period Analysis

## Problem Statement

See `SOURCE.md` for the exact bilingual statement:

> **English.** Definition: The subgroup lattice is the lattice of all subgroups under inclusion. Conjecture: The maximal chain count of the subgroup lattice of a p-group is a quasi-polynomial in p, its period modulo p equals the logarithm of the order of the group and cannot be shortened further. (quasi-polynomial period of subgroup maximal chains)

For a finite $p$-group $G$ of order $|G| = p^k$ with $k = \log_p |G| \in \mathbb{Z}_{\ge 0}$, let $\mathcal{L}(G) = \mathrm{Sub}(G)$ denote the lattice of all subgroups under inclusion and let $c(G)$ denote the number of maximal chains $\{1\} = H_0 \lt H_1 \lt \dots \lt H_k = G$ in $\mathcal{L}(G)$.

## Verdict: **FALSE** (Disproved for All $k = \log_p |G| \ge 2$)

The conjecture is **disproved** for every log-order $k = \log_p |G| \ge 2$ across **every** natural mathematical reading of the statement, while $k = 1$ (where $G \cong \mathbb{Z}/p\mathbb{Z}$ and $\log_p |G| = 1$) serves as the unique degenerate case where the minimal period equals $1$.

### Summary of Counterexamples and Theorems Across All Readings

1. **Cyclic $p$-groups $C_k(p) = \mathbb{Z}/p^k\mathbb{Z}$ ($k \ge 2$):**
   The subgroup lattice $\mathcal{L}\bigl(\mathbb{Z}/p^k\mathbb{Z}\bigr)$ is a single saturated chain of $k + 1$ subgroups $p^k\mathbb{Z}/p^k\mathbb{Z} \lt \dots \lt \mathbb{Z}/p^k\mathbb{Z}$, so
   $$c\bigl(\mathbb{Z}/p^k\mathbb{Z}\bigr) = 1$$
   for every prime $p$. This is a constant polynomial in $p$ whose minimal quasi-polynomial period (and PORC period) is $1 \mid k$ with $1 \lt k$, refuting both strict minimality ($1 \lt k$) and proper-divisor irreducibility ($1 \mid k$, $1 \lt k$).

2. **Elementary Abelian $p$-groups $E_k(p) = \bigl(\mathbb{Z}/p\mathbb{Z}\bigr)^k$ ($k \ge 2$):**
   Maximal chains in $\mathcal{L}\bigl(E_k(p)\bigr) \cong \mathrm{Sub}\bigl(\mathbb{F}_p^k\bigr)$ are complete linear flags, giving the non-constant monic integer polynomial of degree $\binom{k}{2}$:
   $$c\bigl(E_k(p)\bigr) = [k]_p! = \prod_{j=1}^k \frac{p^j - 1}{p - 1} = \prod_{j=1}^k \bigl(1 + p + \dots + p^{j-1}\bigr) \in \mathbb{Z}[p].$$
   Its minimal quasi-polynomial period is again $1 \lt k$, and $[k]_p! \equiv 1 \pmod p$ for all primes $p$.

3. **All Finite Abelian $p$-groups and Small-Order Non-Abelian Census ($k = 2, 3$):**
   For every partition $\lambda \vdash k$, Pontryagin duality and Young-lattice recursion give $c\bigl(G_\lambda(p)\bigr) = P_\lambda(p) \in \mathbb{Z}[p]$ (minimal quasi-period $1$). At $k = 3$ and odd primes $p \ge 3$, the Heisenberg group satisfies $c\bigl(\mathrm{UT}_3(\mathbb{F}_p)\bigr) = (p + 1)^2$ and the metacyclic group satisfies $c\bigl(M(p^3)\bigr) = 2p + 1$ (both exact polynomials of PORC period $1 \lt 3$).

4. **Universal Modulo-$p$ Maximal Chain Congruence (Literal Residue Reading):**
   By Burnside's basis theorem, every nontrivial finite $p$-group $H$ has $|\mathcal{M}(H)| = 1 + p + \dots + p^{d-1} \equiv 1 \pmod p$ maximal subgroups ($d \ge 1$). Induction on $|G| = p^k$ via $c(G) = \sum_{M \in \mathcal{M}(G)} c(M)$ proves that for **every** finite $p$-group $G$ (abelian or non-abelian),
   $$c(G) \equiv 1 \pmod p.$$
   Hence even for an arbitrary non-uniform assignment $p \mapsto G(p)$ of groups of order $p^k$ ($k \ge 2$), the sequence $p \mapsto c\bigl(G(p)\bigr) \bmod p$ is identically $1$ of minimal period $1 \lt k$, refuting both universal and existential readings of modulo-$p$ residue period $k$.

5. **Non-Abelian Semidirect Family $G_d(p)$ of Fixed Order $p^5$ ($k = 5$) with Arbitrary Prime Quasi-Periods:**
   For $d \in \mathbb{Z}$, let $G_d(p) = \bigl(\mathbb{Z}/p^2\mathbb{Z}\bigr)^2 \rtimes_{\varphi_d} \bigl(\mathbb{Z}/p\mathbb{Z}\bigr)$ where $\varphi_d(u, v) = (u + p d v, v + p u) \bmod p^2$. For every integer $d$ and every odd prime $p \ge 3$,
   $$c\bigl(G_d(p)\bigr) = 3p^4 + 10p^3 + 9p^2 + 4p + 1 + \left(\frac{d}{p}\right) p^2(2p + 1),$$
   where $\left(\frac{d}{p}\right)$ is the Legendre symbol.
   - Taking $d = -1$ gives minimal quasi-polynomial period $4 \ne 5$ (in fact, $N$ is a quasi-period if and only if $4 \mid N$, so $5 = \log_p |G_{-1}(p)|$ is not even a valid quasi-period).
   - Taking $d_\ell = (-1)^{(\ell-1)/2}\ell$ for any odd prime $\ell$ gives minimal PORC period $\ell$ at fixed log-order $k = 5$ (so the minimal period can satisfy $\ell = 3 \lt 5$ or $\ell \in \{7, 11, 13, \dots\} \gt 5$).

## Package Contents

- `SOURCE.md` — Unmodified original problem statement.
- `main.tex` / `main.pdf` — Complete mathematical paper proving all theorems, counterexamples, and closed-form formulas.
- `lean/` — Self-contained Core Lean 4.19.0 formalization (`lean-toolchain`, `lakefile.toml`, `lake-manifest.json`, `Main.lean`) compiled with `-DwarningAsError=true`, zero external dependencies, zero `sorry`, zero `native_decide`, and zero custom axioms:
  - `cyclic_hasExactMaximalChains` — Complete classification of subgroups of $\mathbb{Z}/p^k\mathbb{Z}$ and proof that $c\bigl(\mathbb{Z}/p^k\mathbb{Z}\bigr) = 1$ for all primes $p$ and all $k \ge 0$.
  - `ea2_hasExactMaximalChains` — Complete classification of all $p + 3$ subgroups of $\bigl(\mathbb{Z}/p\mathbb{Z}\bigr)^2$ and proof that $c\bigl((\mathbb{Z}/p\mathbb{Z})^2\bigr) = p + 1$ for all primes $p$.
  - `treeMaximalChains_mod_p` & `universal_mod_p_period_impossibility` — Universal modulo-$p$ congruence $c(T) \bmod p = 1$ and impossibility of minimal modulo-$p$ period $k \ge 2$.
  - `nonvacuous_witness_k_eq_1`, `cyclic_refutes_conjecture_all_k_ge_2`, `elem_abelian_refutes_conjecture` — Positive non-vacuity at $k = 1$ and full refutations for all $k \ge 2$.
  - `gMinus1_quasiPoly_iff_four_dvd` & `nonabelian_order_p5_period_4_ne_5` — Exact period characterization $4 \mid N$ for $G_{-1}(p)$ ($k = 5$).
- `verify.py` — Standalone Python 3 verification suite cross-checking exhaustive subgroup lattices, Frattini-hyperplane dynamic programming, abelian Young-lattice polynomials, order-$p^3$ non-abelian groups, and $G_d(p)$ at orders $3^5 = 243$ and $5^5 = 3125$.
- `verification/` — Complete build and verification logs (`lake-build.log`, `lean-axioms.log`, `lean-version.log`, `pdf-build.log`, `python-verify.log`, and `SELF_REVIEW.md`).

## Reproducing Verification

1. **Lean 4.19.0 build:** Run `lake build` inside `lean/`.
2. **Python suite:** Run `python3 verify.py` from the package root.
3. **LaTeX build:** Run `pdflatex -interaction=nonstopmode -halt-on-error main.tex` twice from the package root.
