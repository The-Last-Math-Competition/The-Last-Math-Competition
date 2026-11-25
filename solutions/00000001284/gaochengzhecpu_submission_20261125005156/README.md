# Conjecture 00000001284 — Nim-Multiplication and Square Density in the Nim-Square Sequence

## Overview and Verdict

**Verdict: REFUTED (False as stated under every natural mathematical interpretation).**

Conjecture `00000001284` (`SOURCE.md`) defines nim-multiplication as the realization of finite-field multiplication on the nim-value system $\mathbb{N} = \{0, 1, 2, \dots\}$ and conjectures that:
1. The density of square values in the nim-square sequence is zero; and
2. The decay of the zero density is a logarithmic power with exponent $-1/2$, i.e., $\Theta\bigl((\log N)^{-1/2}\bigr)$.

We analyze both natural mathematical interpretations of *"square values in the nim-square sequence"* (matching both the English and Chinese formulations in `SOURCE.md`) and prove unconditionally that the conjecture fails in both settings:

- **Interpretation A — Nim-square values $\mathcal{Q}_{\mathrm{nim}} = \{x \otimes x : x \in \mathbb{N}\}$:**
  Under Conway's nim-addition $\oplus$ (bitwise XOR) and nim-multiplication $\otimes$ (the inductive Artin–Schreier quadratic field tower $F_k = [0, 2^{2^k}) \cong \mathbb{F}_{2^{2^k}}$), the structure $\bigl(\mathbb{N}, \oplus, \otimes, 0, 1\bigr)$ is a field of characteristic $2$ closing every $F_k$. The Frobenius endomorphism $s(x) = x \otimes x$ is a global bijection $\mathbb{N} \to \mathbb{N}$ preserving **every** dyadic interval $[0, 2^d)$. Consequently, **every** natural number $n \in \mathbb{N}$ is a nim-square, so the density of nim-square values in $\mathbb{N}$ (and in $s(x)$) is identically **$1 \neq 0$** (and strictly exceeds $1/2$ for all $N \ge 1$ even when witnesses are restricted to $x \lt N$).

- **Interpretation B — Ordinary integer squares $\mathcal{Q}_{\mathrm{ord}} = \{m^2 : m \in \mathbb{N}\}$ in $s(x) = x \otimes x$:**
  Let $C(N) = \bigl|\{0 \le x \lt N : \exists m \in \mathbb{N},\; x \otimes x = m^2\}\bigr|$ and $D(N) = C(N)/N$. Because $x \mapsto x \otimes x$ maps $[0, 2^d)$ bijectively onto $[0, 2^d)$ for every $d \ge 0$, we obtain
  $$C(2^d) = \bigl\lceil 2^{d/2} \bigr\rceil \quad (\forall d \ge 0), \qquad C(4^m) = 2^m, \qquad D(4^m) = (4^m)^{-1/2},$$
  and in particular $C(N) = \sqrt{N}$, $D(N) = N^{-1/2}$ at every Fermat $2$-power $N = 2^{2^k}$ ($k \ge 1$). Across **all** integers $N \ge 1$ (including all intermediate $N$), we prove the uniform two-sided polynomial bounds
  $$\frac{1}{\sqrt{2}}\, N^{-1/2} \lt D(N) \lt 2\sqrt{2}\, N^{-1/2} \qquad (\forall N \ge 1).$$
  Therefore, while $\lim_{N \to \infty} D(N) = 0$ **confirms** the zero-density clause under Interpretation B, the true decay rate is **polynomial** of exact order $\Theta\bigl(N^{-1/2}\bigr)$ — **refuting** the conjectured logarithmic decay $\bigl(\log N\bigr)^{-1/2}$, since
  $$\lim_{N \to \infty} \frac{D(N)}{\bigl(\log N\bigr)^{-1/2}} = 0.$$

---

## Key Mathematical Ingredients

1. **Quadratic Field Tower Realization on $\mathbb{N}$:**
   Setting $M_k = 2^{2^k}$ and $P_k = 2^{2^k - 1} = M_k / 2$, each $F_{k+1} = [0, M_{k+1})$ is constructed over $F_k = [0, M_k)$ via $F_{k+1} = F_k[\alpha_k] / \bigl(\alpha_k^2 \oplus \alpha_k \oplus P_k\bigr)$ with $\alpha_k = M_k$. We prove the sharp Artin–Schreier bound
   $$\bigl(x \otimes x\bigr) \oplus x \lt P_k \qquad (\forall x \lt M_k),$$
   which guarantees $T^2 \oplus T \oplus P_k$ has no root in $F_k$ and yields explicit quadratic-norm inverses $\mathrm{nimInv}_k$, Conway's Fermat $2$-power laws ($M_k \otimes x = M_k \cdot x$ for $x \lt M_k$ and $M_k \otimes M_k = M_k + P_k$), ring-theoretic uniqueness, and Conway's impartial-game $\mathrm{mex}$ exclusion property.

2. **Constructive Inverse Frobenius and All-Dyadic Preservation:**
   Cross terms vanish in characteristic $2$, giving the explicit recursive nim-square-root formula
   $$\mathrm{nimSqrt}_{k+1}\bigl(M_k y_1 + y_0\bigr) = M_k\,\mathrm{nimSqrt}_k(y_1) + \mathrm{nimSqrt}_k\bigl(y_0 \oplus (P_k \otimes y_1)\bigr)$$
   and the equivalence $x \otimes x \lt 2^d \iff x \lt 2^d$ for **every** $d \ge 0$ (not merely $d = 2^k$).

3. **Exact Dyadic Counts and Uniform All-$N$ Sandwiching:**
   Sandwiching any $N \ge 1$ inside $2^d \le N \lt 2^{d+1}$ via $d = \lfloor \log_2 N \rfloor$ transfers $C(2^d) = \lceil 2^{d/2} \rceil$ and $C(2^{d+1}) = \lceil 2^{(d+1)/2} \rceil$ to all intermediate integers $N$, yielding $\frac{1}{2} N \lt C(N)^2 \lt 8 N$ for every $N \ge 1$ and $K \cdot C(N)^2 \cdot \lfloor \log_2 N \rfloor \lt N^2$ for all $N \ge 2^{\max(4, 8K)}$.

---

## Package Structure

- `SOURCE.md` — Original bilingual problem statement (unmodified).
- `main.tex` / `main.pdf` — Complete mathematical paper with proofs, explicit $16 \times 16$ nim-multiplication table on $F_2 = [0, 16)$, numerical comparison up to $N = 2^{20}$, and Lean theorem mapping.
- `lean/` — Self-contained Core Lean `v4.19.0` formalization (zero external dependencies, compiled with `-DwarningAsError=true`):
  - `lean-toolchain` — `leanprover/lean4:v4.19.0`
  - `lakefile.toml` & `lake-manifest.json` — Lake build configuration
  - `Main.lean` — Complete formal proofs of the field tower, Fermat $2$-power characterization and uniqueness, Frobenius dyadic bijectivity, Interpretation A, Interpretation B, and explicit non-vacuity checks (zero `sorry`, `admit`, `native_decide`, or custom axioms)
- `verify.py` — Standalone Python 3 verification checking recursive `mex` vs. field-tower equivalence on $64 \times 64$ pairs, field axioms, Frobenius bijectivity, and both interpretations across all $1 \le N \le 1{,}048{,}576$.
- `verification/` — Recorded verification logs (`lake-build.log`, `lean-axioms.log`, `lean-version.log`, `pdf-build.log`, `python-verify.log`) and `SELF_REVIEW.md`.

---

## Reproducing Verification

1. **Core Lean 4 Formalization (`lean/`):**
   ```bash
   cd lean && lake build
   ```
2. **Independent Python Verification:**
   ```bash
   python3 verify.py
   ```
3. **LaTeX Manuscript Compilation:**
   ```bash
   pdflatex -interaction=nonstopmode -halt-on-error main.tex
   pdflatex -interaction=nonstopmode -halt-on-error main.tex
   ```
