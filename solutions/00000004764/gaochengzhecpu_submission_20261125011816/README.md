# Conjecture 00000004764 — Disproof and Formal Verification

## Verdict: **FALSE**

Conjecture `00000004764` (*power-of-two conversion of Boolean-free convolution*) is **false** under every canonical mathematical reading — even if signed integer powers $2^e$ ($e \in \mathbb{Z}$) or rational powers $2^{p/q}$ ($p/q \in \mathbb{Q}$) are permitted.

---

## Original Statement (`SOURCE.md`)

> **English.** Definition: Boolean convolution is the simplified convolution without a composition condition. Conjecture: The conversion of Boolean to free convolution is an explicit power of two, the exponent is controlled by the partition structure of the moment order, and it is exact at the generating function level. (power-of-two conversion of Boolean-free convolution)
>
> **中文。** 定义：布尔卷积指无复合条件的简化卷积。猜想：布尔与自由卷积的换算为二的显式幂,幂次由矩阶的分拆结构控制且在母函数层精确。（布尔-自由二幂换算）

---

## Mathematical Summary

### 1. The Non-Composition Definition at the Generating-Function Level

Let $M(z) = 1 + \sum_{n=1}^{\infty} m_n z^n$ be a normalized moment generating series.

- **Voiculescu--Speicher free convolution ($\boxplus$, with composition):** Writing $C(w) = 1 + \sum_{n=1}^{\infty} \kappa_n w^n = 1 + w R(w)$, free cumulants are governed by the functional composition $w = z M(z)$:

$$M(z) = C\bigl(z M(z)\bigr) \iff M(z) - 1 = z M(z) \, R\bigl(z M(z)\bigr).$$

- **Speicher--Woroudi Boolean convolution ($\uplus$, simplified without composition):** Writing $B(z) = \sum_{n=1}^{\infty} \beta_n z^n = z \tilde{B}(z)$, dropping the internal composition $z \mapsto z M(z)$ yields the rational reciprocal equation:

$$M(z) - 1 = z M(z) \, \tilde{B}(z) \iff \bigl(1 - B(z)\bigr) M(z) = 1 \iff B(z) = 1 - \frac{1}{M(z)}.$$

### 2. Why the Conjecture Appears Plausible at Small Orders (Fermat-Prime Mirage)

Because $4 + 1 = 5$ and $6 - 1 = 5$ are Fermat primes ($2^2 + 1 = 5$), small-order expansions exhibit a deceptive power-of-two pattern:

- **Partition-type moment ratios ($n \in \{1, 2, 4\}$):** For any integer partition $\lambda = (1^{r_1} \cdots n^{r_n}) \vdash n$ into $k = \ell(\lambda)$ blocks, Kreweras' theorem gives

$$R_{\mathrm{BP}}(\lambda) := \frac{N_{\mathrm{NC}}(\lambda)}{N_{\mathrm{Int}}(\lambda)} = \frac{n!}{k! \, (n - k + 1)!} = \frac{1}{n+1}\binom{n+1}{k},$$

which lies in $\{1, 2\} = \{2^0, 2^1\}$ for every partition at $n \in \{1, 2, 4\}$ (and centered $n \le 4$).
- **Centered two-measure convolutions ($n \le 4$):** When $m_1(\mu) = m_1(\nu) = 0$, $m_n(\mu \uplus \nu) = m_n(\mu \boxplus \nu)$ for $n \in \{2, 3\}$, and at $n = 4$, $a_4 + c_4 + 2 a_2 c_2$ converts to $a_4 + c_4 + 4 a_2 c_2$ (ratios $2^0$ and $2^1$).
- **Symmetric cumulant conversions ($2k \le 6$):** When odd cumulants vanish, $\beta_2 = \kappa_2$, $\beta_4 = \kappa_4 + \kappa_2^2$, and $\beta_6 = \kappa_6 + 4 \kappa_4 \kappa_2 + 2 \kappa_2^3$ have exclusively power-of-two monomial coefficients $\{1, 4, 2\}$.

### 3. Complete Refutation Across All Four Canonical Readings

1. **Reading I — Bercovici--Pata / Partition-Type Moment Conversion ($\mu \mapsto \mathbb{B}_1(\mu)$):**
   - $R_{\mathrm{BP}}(2, 1) = \frac{3}{2}$ ($n = 3$), $R_{\mathrm{BP}}(3, 2) = \frac{5}{2}$ ($n = 5$, centered), and $R_{\mathrm{BP}}(4, 2) = 3$, $R_{\mathrm{BP}}(2, 2, 2) = 5$ ($n = 6$, symmetric).
   - For the symmetric Bernoulli law $\mu_{\mathrm{Bern}} = \frac{1}{2}(\delta_{-1} + \delta_1)$, $M_{\mu_{\mathrm{Bern}}}(z) = \frac{1}{1 - z^2}$ is rational with $m_{2k} = 1$, whereas $\mathbb{B}_1(\mu_{\mathrm{Bern}}) = \mu_{\mathrm{sc}}$ (the standard Wigner semicircle law) has $M_{\mu_{\mathrm{sc}}}(z) = \frac{1 - \sqrt{1 - 4z^2}}{2z^2} = \sum_{k=0}^{\infty} C_k z^{2k}$ with algebraic branch points and $m_6(\mu_{\mathrm{sc}}) / m_6(\mu_{\mathrm{Bern}}) = C_3 = 5 \notin \{2^r : r \in \mathbb{Q}\}$.

2. **Reading II — Same-Measure Cumulant Conversion ($\beta_n(\mu) \leftrightarrow \kappa_n(\mu)$):**
   By Lagrange--Bürmann inversion, for all $n \ge 2$,

$$\beta_n = \frac{1}{n-1}[w^n] C(w)^{n-1}, \qquad \kappa_n = -\frac{1}{n-1}[z^n]\bigl(1 - B(z)\bigr)^{n-1}.$$

   - **Scalar zero-divisor failure ($n = 4$):** $\kappa_4(\mu_{\mathrm{sc}}) = 0$ whereas $\beta_4(\mu_{\mathrm{sc}}) = 1$.
   - **Sign failure ($n = 4$):** $\kappa_4(\mu_{\mathrm{Bern}}) = -1 \lt 0$ whereas $\beta_2(\mu_{\mathrm{Bern}})^2 = 1 \gt 0$.
   - **Centered monomial failure ($n = 5$):** $\beta_5 = \kappa_5 + 3 \kappa_2 \kappa_3$ (coefficient $3$).
   - **Symmetric collapse ($n = 8$):** $\beta_8 = \kappa_8 + 6 \kappa_6 \kappa_2 + 3 \kappa_4^2 + 15 \kappa_4 \kappa_2^2 + 5 \kappa_2^4$, and $\beta_8(\mu_{\mathrm{sc}}) = C_3 = 5 \notin \{2^r : r \in \mathbb{Q}\}$.

3. **Reading III — Direct Two-Measure Convolution ($\mu \uplus \nu$ vs. $\mu \boxplus \nu$):**
   - For centered symmetric measures at $n = 6$, mixed moment terms convert by factor $3$ ($2(a_2 c_4 + a_4 c_2) \mapsto 6(a_2 c_4 + a_4 c_2)$ and $a_2 c_2(a_2 + c_2) \mapsto 3 a_2 c_2(a_2 + c_2)$).
   - For $\mu_{\mathrm{Bern}}$, $M_{\mu_{\mathrm{Bern}} \uplus \mu_{\mathrm{Bern}}}(z) = \frac{1}{1 - 2z^2}$ ($m_{2k} = 2^k$), whereas $\mu_{\mathrm{Bern}} \boxplus \mu_{\mathrm{Bern}}$ is the arcsine law with $M_{\mu_{\mathrm{Bern}} \boxplus \mu_{\mathrm{Bern}}}(z) = \frac{1}{\sqrt{1 - 4z^2}}$ ($m_{2k} = \binom{2k}{k}$), failing at $n = 4$ ($\frac{6}{4} = \frac{3}{2}$) and $n = 6$ ($\frac{20}{8} = \frac{5}{2}$).

4. **Reading IV — Partition-Lattice Cardinalities ($|\mathrm{Int}(n)|$ vs. $|\mathrm{NC}(n)|$):**
   - $|\mathrm{Int}(n)| = 2^{n-1}$ holds universally, whereas $|\mathrm{NC}(n)| = C_n$, failing at $n = 3$: $|\mathrm{NC}(3)| / |\mathrm{Int}(3)| = \frac{5}{4} \notin \{2^r : r \in \mathbb{Q}\}$, and $|\mathrm{NC}_{\mathrm{irr}}(4)| = 5 \notin \{2^r : r \in \mathbb{Q}\}$.

---

## Package Structure & Reproduction

- `SOURCE.md` — Unmodified competition problem statement.
- `main.tex` / `main.pdf` — Complete mathematical paper proving the positive generating-function identities and refuting all four canonical readings.
- `verify.py` — Standalone Python 3.12 symbolic verification script (standard library only).
- `lean/` — Self-contained Core Lean 4.19.0 formalization (`BooleanFreeConv`, zero external dependencies, `-DwarningAsError=true`, zero `sorry` / `admit` / `native_decide` / custom axioms):
  - `BooleanFreeConv/Basic.lean` — Signed integer & rational power-of-two predicates, $3$-adic and $5$-adic non-dyadic obstructions, and Kreweras ratios.
  - `BooleanFreeConv/Series.lean` — Formal power series, composition $C\bigl(z M(z)\bigr)$, non-composition equivalence `boolGenEq_iff_no_comp`, moment--cumulant bijections, and Bercovici--Pata homomorphism `bercoviciPataBF_hom`.
  - `BooleanFreeConv/Partitions.lean` — Set partitions via restricted growth strings, universal theorem `intPartitions_card_pow2` ($|\mathrm{Int}(n)| = 2^{n-1}$), and noncrossing lattice counts.
  - `BooleanFreeConv/MainTheorems.lean` — Universal centered polynomial identities, Bernoulli/Wigner/arcsine witnesses, and master theorem `conjecture_00000004764_false`.
- `verification/` — Complete build, axiom-audit, and verification logs (`lake-build.log`, `lean-axioms.log`, `lean-version.log`, `pdf-build.log`, `python-verify.log`, `SELF_REVIEW.md`).

### Commands to Reproduce

```bash
python3 verify.py
cd lean && lake build
pdflatex -interaction=nonstopmode -halt-on-error main.tex
```
