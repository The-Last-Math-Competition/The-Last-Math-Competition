# Self-Review Audit — Conjecture 00000004763

## 1. Conjecture Statement & Faithfulness Audit
- **Source integrity:** `SOURCE.md` (971 bytes, untouched) presents both English and Chinese versions of Conjecture `00000004763` on the conversion between free cumulants $\kappa_n$ and classical cumulants $c_n$.
- **Complete coverage of all four constituent subclaims and interpretations:**
  1. *Subclaim 1 ("always a low-order rational combination"):* Refuted in both directions (`classicalToFree` and `freeToClassical`). Along the Gaussian ray $c = (0, t, 0, \dots)$ and Wigner semicircle ray $\kappa = (0, t, 0, \dots)$, we prove exact degree-$d$ homogeneity at order $n = 2d$ with infinitely many nonzero coefficients $a_d$ and $b_d$, ruling out not only bounded-degree polynomials but also bounded-degree rational combinations $P(t)/Q(t)$ with $\deg P, \deg Q \le D$. We also show unbounded index depth $n - 2$ via $[c_{n-2}c_2]\kappa_n(c) = n(n-3)/2 > 0$.
  2. *Subclaim 2 ("coefficients given by weighted crossing pair counts"):* Refuted at $n = 8$ on set partitions of $\{1, \dots, 8\}$ of identical block-size signature $[2, 2, 2, 2]$ and identical crossing-pair counts: at $\mathrm{cr} = 3$ ($K_1 \sqcup K_3$ vs. $K_{1,3}$, connectivity obstruction) and even among *connected* crossing partitions at $\mathrm{cr} = 4$ (paw graph vs. $C_4$, Tutte activity $T_G(1,0) = 2 \ne 3$).
  3. *Subclaim 3 ("first two nontrivial conversion coefficients are 1 and -1"):* Refuted across all single-direction conventions: $c \mapsto \kappa$ has $(+1, +5)$ with all coefficients strictly positive; $\kappa \mapsto c$ has $(-1, -5)$ (or $(-1, -9, +5)$ on centered symmetric cumulants); block-count transitions have $(+1, -5)$ and $(-1, +5)$. We explicitly prove the positive order-4 identities $\kappa_4 = c_4 + c_2^2$ and $c_4 = \kappa_4 - \kappa_2^2$ showing how $+1$ and $-1$ arise from *opposite* conversion directions.
  4. *Subclaim 4 ("invertible over the field of rational functions, with finite bandwidth of the inverse (finite bandwidth of the Stirling-type triangle)"):* Refuted across every canonical candidate matrix family: Stirling $S, S^{-1}$; Narayana $N, N^{-1}$; block-count transitions $T_{\mathrm{cl}\to\mathrm{fr}} = N^{-1}S$ and $T_{\mathrm{fr}\to\mathrm{cl}} = S^{-1}N$ (including the exact closed-form harmonic identity $(S^{-1}N)_{n,2} = (-1)^{n-1}(n-2)!(H_{n-2}-1) \ne 0$ for all $n \ge 4$ and exponential-vs-polynomial disproof for $N^{-1}S$); partial Bell and Kreweras triangles $B(c), B^{\mathrm{NC}}(\kappa)$ over $\mathbb{Q}(c_1, c_2, \dots)$; Jacobian $J = \partial\kappa/\partial c$; and canonical moment-recurrence matrices $T_{\mathrm{rec}}(m) = L_{\mathrm{fr}}(m)^{-1}L_{\mathrm{cl}}(m)$ and $T_{\mathrm{rec}}(m)^{-1}$ over $\mathbb{Q}(m_1, m_2, \dots)$.

## 2. Anti-Vacuity & Non-Tautology Audit (Lean 4.19.0)
- **Genuine definitions from first principles:** `clMoment`, `clCumulant`, `frMoment`, `frCumulant`, `classicalToFree`, and `freeToClassical` are defined directly from the exponential-generating and Speicher R-transform recurrences in `Basic.lean`, and proved mutually inverse for all $n \ge 1$ (`freeToClassical_classicalToFree`, `classicalToFree_freeToClassical`).
- **Positive foundations & non-vacuity witnesses (`conjecture_00000004763_positive_foundations`):**
  - Symbolic universal proofs for all sequences `c, κ : Nat → Int` at orders $1 \le n \le 5$ and centered $n = 6$.
  - Explicit proof that `matId` (bandwidth $0$) and `bidiagDiff` (bandwidth $1$) satisfy `HasFiniteLowerBandwidth`, confirming the bandwidth predicate is non-vacuous.
  - Explicit proof (`L_cl_implements_clMoment`, `L_fr_implements_frMoment`) that the canonical recurrence matrices `L_cl(m)` and `L_fr(m)` genuinely implement the classical and free moment-cumulant systems.
- **Strict toolchain compliance:**
  - Toolchain: `leanprover/lean4:v4.19.0` with `moreLeanArgs = ["-DwarningAsError=true"]` and zero external dependencies.
  - Zero `sorry`, zero `admit`, zero `native_decide`, zero custom `axiom`.
  - `#print axioms` on `conjecture_00000004763_positive_foundations` and `conjecture_00000004763_disproof` uses only standard Lean kernel axioms (`propext`, `Classical.choice`, `Quot.sound` — or subset thereof).

## 3. Paper, Computational Script, and Hygiene Audit
- **`main.pdf` visual inspection:** All pages inspected visually; 0 LaTeX errors, 0 warnings, 0 overfull `\hbox`es, 0 underfull `\hbox`es, clean typography and table placement.
- **`verify.py`:** Uses exact `fractions.Fraction` arithmetic and Python standard library only; cross-checks partition lattices ($n \le 8$), Tutte activities ($n \le 7$), Stein/Wigner sequences ($d \le 12$), and all matrix bandwidths ($n \le 15$).
- **`README.md` GitHub math compliance:** Checked for zero `\operatorname`, `\bowtie`, `\coloneqq`, `\DeclareMathOperator`, `\newcommand`, raw `<`/`>` inside math, `$(` openers, and local paths.
- **Artifact hygiene:** `.lake/` and LaTeX auxiliary files (`.aux`, `.out`, `.toc`, root `.log`) removed after generating clean UTF-8 logs in `verification/`.
