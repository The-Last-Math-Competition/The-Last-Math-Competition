# Self-Review Report — Conjecture `00000007609`

## 1. Bilingual Statement & Scope Audit

- **`SOURCE.md` Integrity:** Verified byte-for-byte untouched (`660` bytes) against the original staged `SOURCE.md`.
- **English vs. Chinese Clause Alignment:**
  - *Definition:* "Reflection decomposition with the reflection-representation counting of rotations" / "反射分解：旋转的反射表示计数" — aligned on orthogonal reflection decompositions $R = r_1 \cdots r_k$ and reflection-representation counting of rotations $R \in \mathrm{SO}(V, Q)$.
  - *Claim A:* "The conversion constant is the reflection count of rotations, the minimal reflection count being angle-type" / "换算常数为旋转的反射计数且最少反射数为角度型" — decisively refuted: in Euclidean $\mathrm{SO}_n(F)$, $\ell_{\mathrm{ref}}(R) = \mathrm{rank}(I_n - R) = 2s$ is a discrete rank invariant (angle-insensitive across the infinite Cayley family in $\mathrm{SO}_2(F)$, and differing as $2 \neq 4$ on $R_1 = \mathrm{diag}(-1,-1,1,1)$ vs. $R_2 = \mathrm{diag}(J, J)$ in $\mathrm{SO}_4(\mathbb{Z})$ despite identical trace $0$, squared Frobenius chordal distance $8$, and $L^1$ angle sum $\pi$, as well as on Pythagorean eigenangles $ (\pi, 0) $ vs. $ (\frac{3\pi}{5}, \frac{4\pi}{5}) $ with identical $L^2$ geodesic distance $\sqrt{2}\,\pi$), while in split signature $\mathrm{SO}(2, 2; F)$, Scherk's unipotent null rotation $N$ ($ (I_4 - N)^2 = 0 $, $\mathrm{tr}(N) = 4$, zero angle) has $\mathrm{rank}(I_4 - N) = 2$ yet $\ell_{\mathrm{ref}}(N) = 4 = \mathrm{rank}(I_4 - N) + 2$.
  - *Claim B:* "the counting is finite with parity given by the determinant" / "计数有限且计数的奇偶由行列式":
    - *Parity sub-clause (True away from $\mathrm{char} = 2$):* Confirmed and proved universally in Core Lean 4 (`reflCount2_parity_iff`, `reflCount4_parity_iff`): $\det(r_1 \cdots r_k) = (-1)^k$.
    - *Finiteness sub-clause (False under every reading):* Every $R \in \mathrm{SO}_2(F) \setminus \{I_2\}$ admits infinitely many pairwise distinct minimal-length ($k = 2$) ordered and unordered reflection-operator factorizations $R = r_{(1, t)} \circ r'_t$ (`so2_infinite_reflection_counting`), plus valid decompositions of unbounded even lengths $2 + 2m$; meanwhile on $ (\mathbb{F}_2^4, x_0 x_1 + x_2 x_3) $, Dieudonné's reversal rotation $D \in \mathrm{SO}^+(4, \mathbb{F}_2)$ admits **zero** reflection decompositions of any length (`dieudonne_f2_counterexample`).
  - *Claim C:* "and the minimization is realized by geodesic decomposition" / "最少的实现为测地分解" — refuted both in Lorentzian $\mathrm{SO}(1, 1; F)$ (where $-I_2$ has $\ell_{\mathrm{ref}}(-I_2) = 2$ yet lies outside the square/exponential subgroup $\mathrm{SO}^+(1, 1; F)$, so zero Lie-group geodesics reach $-I_2$) and in compact Euclidean $\mathrm{SO}_4(F)$ (where reflections lie outside $\mathrm{SO}_4$, and the $B_4$-Coxeter rotation $R_{\mathrm{Cox}} = P_1 P_2$ with $R_{\mathrm{Cox}}^4 = -I_4$ has $\ell_{\mathrm{ref}}(R_{\mathrm{Cox}}) = 4$, non-commuting planar factors $P_1 P_2 \neq P_2 P_1$, and preserves **no** $2$-dimensional subspace of $\mathbb{Q}^4$).

## 2. Adversarial Formalization Audit (Core Lean `v4.19.0`)

- **No Shortcut / Proxy Definitions:**
  - `QuadForm2.polar`, `QuadForm4.polar`, and `f2Polar` use the exact textbook polar bilinear form $B_Q(u, v) = Q(u + v) - Q(u) - Q(v)$.
  - `refl2`, `refl4`, and `f2Refl` implement the exact coordinate-free orthogonal reflection $r_u(v) = v - Q(u)^{-1} B_Q(u, v) u$ ($Q(u) \neq 0$), proved at the operator level (counting distinct linear operators in $\mathcal{R}(V, Q)$, not merely rescaled vectors!).
  - `IsMinReflCount2` and `IsMinReflCount4` define the exact textbook minimum word length (`HasReflCount Q g k ∧ ∀ m < k, ¬ HasReflCount Q g m`), and `TwoDimSubspace4` / `LinIndep2` define textbook $2$-dimensional invariant subspaces.
- **Universal Field Generality + Concrete Non-Vacuity Ground Witness:**
  - All theorems hold over any `FormallyRealField F` (covering $\mathbb{R}$ and $\mathbb{Q}$) plus exact $\mathbb{F}_2^4$ (`F2Vec4`), and are constructively instantiated on `QField` in `conjecture_00000007609_ground_witness`.
- **Zero Forbidden Constructs:**
  - `lean-toolchain`: `leanprover/lean4:v4.19.0`
  - `lakefile.toml`: `moreLeanArgs = ["-DwarningAsError=true"]`, zero external dependencies.
  - Zero `sorry`, zero `admit`, zero `native_decide`, zero custom `axiom` declarations (`#print axioms` reports only standard Lean core axioms `propext`, `Classical.choice`, `Quot.sound`).

## 3. Symbolic Verification, Typesetting, and Markdown Audit

- **`verify.py`:** Standalone Python 3.12 script using exact `fractions.Fraction` and $\mathbb{F}_2$ arithmetic (zero floating-point approximations); exits with code `0`.
- **`main.tex` / `main.pdf`:** Compiled twice with `pdflatex` via `run_lean.py`; visually inspected page-by-page; zero LaTeX errors, zero unresolved references, zero overfull boxes.
- **GitHub Markdown Math Compliance (`README.md` and `pr_body.md`):** Audited via `audit_markdown.py` for zero occurrences of `\operatorname`, `\bowtie`, `\coloneqq`, `\DeclareMathOperator`, `\newcommand`, raw `<` or `>` inside math delimiters, `$(` inline-math openings, or local filesystem paths.
