# Self-Review — Conjecture 00000000592

## 1. Problem Fidelity Audit (English & Chinese Statements)

- **Original Statement (`SOURCE.md`):**
  - English: *"Definition: The graded canonical module $\omega$ of a semigroup-graded ring. Conjecture: The minimal number of generators of $\omega$ equals the type, and its set of degrees is exactly the pseudo-Frobenius numbers plus a constant (an aligned correspondence, verified up to dimension 4)."*
  - Chinese: *"定义：半群 ℤ-分级环的分次 canonical 模 ω。猜想：ω 的极小生成元数 = type,且其度数集合恰为伪 Frobenius 数 + 常数(对应对齐,验证至 dim 4)。"*
- **Scope & Interpretation Coverage:**
  1. **Classical numerical semigroup rings ($R = k[S]$, $S \subseteq \mathbb{N}$, $\dim R = 1$, Cohen–Macaulay, positively $\mathbb{Z}$-graded):**
     - The first clause ($\mu_R(\omega) = \mathrm{type}(R) = |\mathrm{PF}(S)|$) is proved **true** in general (`minimal_gen_characterization`).
     - The second clause ($\mathrm{Deg}_{\min}(\omega) = \mathrm{PF}(S) + c'$) is proved **false** at embedding dimension $e = 4$ (also genus $g = 4$, multiplicity $m = 4$, Frobenius number $F = 5$) via $S = \langle 4, 6, 7, 9 \rangle = \mathbb{N} \setminus \{1, 2, 3, 5\}$, where $\mathrm{PF}(S) = \{2, 3, 5\}$ has consecutive gaps $(1, 2)$ while $\mathrm{Deg}_{\min}(\omega_R(-c)) = \{-5 + c, -3 + c, -2 + c\}$ has consecutive gaps $(2, 1) \ne (1, 2)$.
     - Both the Goto–Watanabe canonical normalization $\omega_R = \underline{\mathrm{Hom}}_k(H^1_{\mathfrak{m}}(R), k)$ ($c = 0$), the standard canonical fractional ideal $K(S) = \omega_R(-F(S))$ ($c = F(S)$), and **every** shifted canonical module $\omega_R(-c)$ ($c \in \mathbb{Z}$) are simultaneously covered by universally quantifying over both $c \in \mathbb{Z}$ and the proposed alignment constant $c' \in \mathbb{Z}$, as well as over all base fields $k$ of arbitrary characteristic (`CommField K`).
  2. **Higher-Krull-dimension Cohen–Macaulay $\mathbb{Z}$-graded affine semigroup rings:**
     - Polynomial extensions $R_d = k[S \times \mathbb{N}^{d-1}]$ ($d \ge 1$) exhibit the same $(2, 1) \ne (1, 2)$ gap-reversal obstruction in every Krull dimension $d = 1, 2, 3, 4, 5, \dots$.
  3. **Non-Cohen–Macaulay $\mathbb{Z}$-graded affine semigroup rings:**
     - Macaulay's smooth rational quartic curve semigroup $S_{\mathrm{Mac}} = \langle (4,0), (3,1), (1,3), (0,4) \rangle \subseteq \mathbb{N}^2$ ($\dim R = 2$, $\mathrm{edim}\, R = 4$, $\mathrm{depth}\, R = 1$) shows that without Cohen–Macaulayness, even the first clause $\mu_R(\omega_R) = \mathrm{type}(R)$ fails ($\mathrm{type}(R) = |\mathrm{PF}(S_{\mathrm{Mac}})| = 1$ vs. $\mu_R(\omega_R) = 3$).
  4. **Explanation of Empirical Agreement in Small Cases:**
     - Proved (`alignment_of_type_le_two`) that whenever $\mathrm{type}(S) \le 2$, $-\mathrm{PF}(S) + c$ is automatically a constant shift of $\mathrm{PF}(S)$, covering 100% of numerical semigroups of embedding dimension $e \le 3$ (by Herzog 1970) and multiplicity $m \le 3$.
     - Exhaustively checked all 50 numerical semigroups of genus $g \le 6$ and 137 four-generator arithmetic-progression semigroups in `verify.py`, confirming zero counterexamples for $g \le 3$, $F \le 4$, and arithmetic-progression families, and identifying $S = \langle 4, 6, 7, 9 \rangle$ as the unique genus-$4$ counterexample.

## 2. Lean 4 Formalization Audit (`lean/Main.lean`)

- **Toolchain & Dependencies:** Core Lean `4.19.0` (`leanprover/lean4:v4.19.0`), zero external dependencies in `lakefile.toml` and `lake-manifest.json`, compiled with `-DwarningAsError=true`.
- **Soundness & Axiom Check:**
  - Zero `sorry`, zero `admit`, zero `native_decide`, zero custom `axiom`, zero `unsafe` / `extern` / `implemented_by` / `opaque`.
  - `#print axioms` on all 11 main theorems reports solely `[propext, Classical.choice, Quot.sound]`.
- **Non-Vacuity & Faithfulness Check:**
  - `CommField` is concretely instantiated on `Bool` ($\mathbb{F}_2$) via `instCommFieldBool`, and `conjecture_592_counterexample_exists` packages an explicit unconditional witness at $K = \mathbb{F}_2$, $c = 0$.
  - Minimal homogeneous generating sets (`IsMinimalHomogGenSet`) are defined genuinely over formal homogeneous $K[S]$-linear combinations (`GenComb` / `evalComb`) inside the graded module $\omega_S(c)$ (`OmegaHomog`), rather than merely asserting degree formulas by definition.
  - Both $S_{4679}$ and $S_{\mathrm{Mac}}$ are proved equivalent to explicit nonnegative integer combinations of their generators (`S4679_iff_generated_by_4_6_7_9` and `SMacaulay_iff_generated`).

## 3. Paper, Script, and Package Hygiene Audit

- **`SOURCE.md`:** Untouched and byte-identical to original input.
- **`main.tex` / `main.pdf`:** Compiled twice with `pdflatex -interaction=nonstopmode -halt-on-error main.tex`; visually inspected page-by-page to verify crisp typography, zero overfull boxes, and zero unresolved references.
- **`README.md`:** Audited against GitHub Markdown math rendering rules (no `\operatorname`, `\coloneqq`, `\bowtie`, `\newcommand`, raw `<`/`>` inside math, `$(` math delimiters, or local host paths).
- **Cleanliness:** Build directory `.lake/` and LaTeX temporary files (`*.aux`, `*.out`, `*.toc`, root `*.log`) removed after archiving full build logs in `verification/`.
