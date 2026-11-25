# Conjecture 00000007620 — Resolution Package

- **Conjecture ID:** `00000007620`
- **Verdict:** **TRUE** (affirmatively resolved with explicit opposite-signature conformal models, complete $8$-fold Bott classification, exact rational verification, and Core Lean 4.19.0 formalization)

## Problem Statement

> **English.** Definition: Group spectra and Clifford spectra are two layers. Conjecture: There exist two conformal models with the same isometry-group spectrum but different Clifford spectra, and the separation is realized by an explicit signature pair with the same group but different embedding. (same group-different signature separation)
>
> **中文。** 定义：群谱与 Clifford 谱指两层。猜想：存在两共形模型的等距群谱相同而 Clifford 谱不同,分离由同群异嵌入的显式符号差对实现。（群同-谱异符号差分离）

## Summary of Mathematical Resolution

Given any nondegenerate base quadratic space $\bigl(V, q_0\bigr)$ of signature $\bigl(p, q\bigr)$ over a formally real field $F$ (such as $F = \mathbb{R}$ or $F = \mathbb{Q}$), compare:
1. **Standard Conformal Horosphere Model $\mathcal{M}_1$:** embeds $\bigl(V, q_0\bigr)$ into $W = V \oplus F^2$ equipped with $Q_1(x, u, v) = q_0(x) + u^2 - v^2$ of signature $\bigl(p + 1, q + 1\bigr)$ via
   $$\iota_1(x) = \left(x,\; \frac{q_0(x) - 1}{2},\; \frac{q_0(x) + 1}{2}\right).$$
2. **Dual Sign-Flipped Conformal Horosphere Model $\mathcal{M}_2$:** embeds $\bigl(V, -q_0\bigr)$ of signature $\bigl(q, p\bigr)$ into the **same** ambient vector space $W = V \oplus F^2$ equipped with $Q_2(x, u, v) = -q_0(x) - u^2 + v^2 = -Q_1(x, u, v)$ of signature $\bigl(q + 1, p + 1\bigr)$ via
   $$\iota_2(x) = \left(x,\; \frac{1 - q_0(x)}{2},\; -\frac{1 + q_0(x)}{2}\right).$$

- **Layer 1 (Same Group & Identical Isometry-Group Spectrum, Distinct Embeddings):**
  Because $G_{Q_2} = -G_{Q_1}$, the orthogonal groups $\mathrm{O}(W, Q_1) = \mathrm{O}(W, Q_2)$, special orthogonal groups, projective conformal groups $\mathrm{PO}(W, Q_1) = \mathrm{PO}(W, Q_2)$, Lie algebras $\mathfrak{so}(W, Q_1) = \mathfrak{so}(W, Q_2)$, null cones $\mathcal{N}(Q_1) = \mathcal{N}(Q_2)$, and points at infinity $e_\infty = (0, 1, 1)$ are **literally identical**, so all Layer-1 group spectra (eigenvalue, trace, characteristic-polynomial, Casimir, and representation spectra) coincide, while $\iota_1$ and $\iota_2$ are distinct and projectively disjoint on $V \setminus \{0\}$.
- **Layer 2 (Separated Clifford Spectra):**
  - **Minimal Odd-Dimensional Witness** — signature $\bigl(1, 0\bigr)$ vs. $\bigl(0, 1\bigr)$, ambient $\bigl(2, 1\bigr)$ vs. $\bigl(1, 2\bigr)$: $\mathrm{Cl}_{2,1}(F) \cong M_2(F) \times M_2(F)$ has split center $F \times F$, $4$ central idempotents, central pseudoscalar $\omega_1^2 = +1$, and $2$ simple spinor modules, whereas $\mathrm{Cl}_{1,2}(F) \cong M_2(F(\sqrt{-1}))$ has field center $F(\sqrt{-1})$, $2$ central idempotents, $\omega_2^2 = -1$, and $1$ simple module; thus $\mathrm{Cl}_{2,1}(F) \not\cong \mathrm{Cl}_{1,2}(F)$.
  - **Lorentzian Even-Dimensional Witness** — signature $\bigl(2, 0\bigr)$ vs. $\bigl(0, 2\bigr)$, ambient $\bigl(3, 1\bigr)$ vs. $\bigl(1, 3\bigr)$: Both centers equal $F$, yet $\mathrm{Cl}_{3,1}(F) \cong M_4(F)$ has Pierce idempotent capacity $4$ whereas $\mathrm{Cl}_{1,3}(F) \cong M_2(\mathbb{H}_F)$ has Pierce capacity $2$; thus $\mathrm{Cl}_{3,1}(F) \not\cong \mathrm{Cl}_{1,3}(F)$.
  - **Complete Real Classification:** Over $\mathbb{R}$, opposite-signature conformal pairs $\bigl(p, q\bigr)$ and $\bigl(q, p\bigr)$ separate Layer 2 if and only if $p - q \not\equiv 0, 4 \pmod{8}$.

## Package Structure

- `SOURCE.md` — Exact unmodified problem statement.
- `main.tex`, `main.pdf` — Complete mathematical exposition and proofs.
- `verify.py` — Pure Python 3.12 standard-library exact rational verification suite (`fractions.Fraction`).
- `lean/` — Self-contained Core Lean 4.19.0 formalization (`-DwarningAsError=true`, zero external dependencies, zero `sorry`, zero `native_decide`, zero custom axioms):
  - `Conjecture00000007620/Field.lean` — Associative rings, ring isomorphisms, intrinsic spectral invariants (`HasNontrivialCentralIdem`, `HasNontrivialCentralInvolution`, `HasOrthogonalIdempotents`), `FormallyRealField`, and constructive exact rationals `RatField`.
  - `Conjecture00000007620/Conformal.lean` — Quadratic/polar forms, matrices, `InFullOrthGroup`, `InOrthLieAlg`, group eigenvalue/trace spectra, sign-flip group invariance, and `ConformalModel` (`stdConformalModel`, `dualConformalModel`, projective disjointness).
  - `Conjecture00000007620/Clifford.lean` — Genuine $2^n$-dimensional universal Clifford algebra `CliffordAlg`, associativity, quadratic law `embedVec_sq`, and universal property (`CliffordAlg.lift`, `hom_unique`).
  - `Conjecture00000007620/Separation.lean` — Odd separation (`clifford_21_not_iso_12`), quaternion division algebra `QuatAlg`, $2 \times 2$ matrix Pierce rank bound, even Lorentzian separation (`clifford_31_not_iso_13`), and master theorems `conjecture_00000007620_universal`, `conjecture_00000007620`, and `conjecture_00000007620_lorentzian`.
- `verification/` — Complete build, audit, and execution verification logs.

## Reproduction Commands

```powershell
python verify.py
cd lean
lake build
pdflatex -interaction=nonstopmode main.tex
```
