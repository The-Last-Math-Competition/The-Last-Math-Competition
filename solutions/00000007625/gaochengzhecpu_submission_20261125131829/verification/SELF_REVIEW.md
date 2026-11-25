# Adversarial Self-Review — Conjecture 00000007625

## 1. Faithfulness & Bilingual Statement Audit

- **Original Statement (`SOURCE.md`):**
  - English: *"Definition: Idempotents as projection structure. Conjecture: The count law of idempotent decompositions is the minimal-ideal count; the realization of minimality is the matrix factor; and the minimal realization of matrix factors is the center decomposition. (minimal-ideal-count idempotent decomposition)"*
  - Chinese: *"定义：幂等元为投影结构。猜想：幂等分解的个数律为极小理想数；且极小的实现为矩阵因子；且矩阵因子的极小实现为中心分解。（幂等分解极小理想数）"*
- **Coverage of Every Interpretation:**
  1. **Clause I ("count law of idempotent decompositions is the minimal-ideal count" / "幂等分解的个数律为极小理想数"):**
     - Tested against *all* standard count notions: primitive orthogonal decomposition length $r$, unordered primitive decomposition count $N_{\mathrm{unord}}$, ordered primitive decomposition count $N_{\mathrm{ord}}$, non-primitive orthogonal decomposition counts ($N_{\mathrm{unord}}^{\mathrm{all}}$, $N_{\mathrm{ord}}^{\mathrm{all}}$), nonzero idempotents $|E(R) \setminus \{0\}|$, and total idempotents $|E(R)|$.
     - Tested against *all* standard minimal-ideal counts: minimal nonzero two-sided ideal count $m_{\mathrm{two}}$, minimal nonzero left ideal count $m_{\mathrm{left}}$, minimal nonzero right ideal count $m_{\mathrm{right}}$, and $|\mathcal{I}_{\mathrm{left}} \cup \mathcal{I}_{\mathrm{right}}|$.
     - On the single split Clifford algebra $\mathrm{Cl}_{1,1}(\mathbb{F}_3) \cong M_2(\mathbb{F}_3)$, we obtain $\{2, 6, 7, 12, 13, 14\} \cap \{1, 4, 8\} = \emptyset$, refuting every combination simultaneously; and over $\mathbb{Z}$ / $\mathbb{Q}$, $N_{\mathrm{unord}} = \infty$ while $m_{\mathrm{two}}(M_2(\mathbb{Q})) = 1$ and $r = 2$.
  2. **Clause II ("the realization of minimality is the matrix factor" / "且极小的实现为矩阵因子"):**
     - Refuted on non-split division Clifford algebras $\mathrm{Cl}_{0,1}(\mathbb{F}_3) \cong \mathbb{F}_9$ and $\mathrm{Cl}_{0,2}(\mathbb{Z}) = \mathbb{H}(\mathbb{Z})$ / $\mathrm{Cl}_{0,2}(K) = \mathbb{H}(K)$, none of which is ring-isomorphic to $M_n$ over the base ring/field for any $n \ge 1$.
     - Refuted on minimal left ideals $M_2(K)e_i$ (which contain nonzero nilpotents $E_{21}^2 = 0$) and on degenerate Clifford / non-semisimple algebras $\Lambda(\mathbb{F}_3^1) = \mathbb{F}_3[\varepsilon]/(\varepsilon^2)$ and $\mathbb{F}_3[x,y]/(x^2,xy,y^2)$, whose minimal ideals satisfy $I^2 = 0$ and contain zero nonzero idempotents.
  3. **Clause III ("the minimal realization of matrix factors is the center decomposition" / "且矩阵因子的极小实现为中心分解"):**
     - Positive scope proved rigorously (`central_block_minimal_ideals_exactCard`, `central_block_decomp_uniqueness`, `f3Pow_positive_theorem`): for central-primitive orthogonal decompositions into simple central blocks, the unordered center decomposition is unique and its length $t$ equals $m_{\mathrm{two}}(R)$ (and equals $m_{\mathrm{left}}(R) = r(R)$ on $K^t$).
     - Refuted outside semisimplicity on $\mathbb{F}_3[\varepsilon]/(\varepsilon^2)$ (center block is not a matrix factor) and commutative $\mathbb{F}_3[x,y]/(x^2,xy,y^2)$ (where all elements and idempotents are central and $t = r = 1 \neq 4 = m_{\mathrm{two}}$).

## 2. Core Lean 4.19.0 Formalization Audit

- **Toolchain & Build:** `leanprover/lean4:v4.19.0`, `moreLeanArgs = ["-DwarningAsError=true"]`, zero external dependencies.
- **No Forbidden Constructs:** Verified zero occurrences of `sorry`, `admit`, `native_decide`, or custom `axiom`.
- **Axiom Hygiene:** `#print axioms` on `conjecture_00000007625_resolution` and all 16 component theorems uses only standard Lean foundations (`propext`, `Classical.choice`, `Quot.sound`; zero `sorryAx`, `Lean.ofReduceBool`, or `Lean.trustCompiler`).
- **Non-Vacuity:** Concrete unconditional rings (`F3PowRing (m + 1)`, `Cl10F3Ring`, `Cl11F3Ring`, `Mat2F3Ring`, `Mat2IntRing`, `Cl01F3Ring`, `QuatIntRing`, `DualF3Ring`, `LocalF3Ring`) witness every positive and negative regime directly without vacuous hypotheses. Furthermore, `ExactCard` is backed by constructive Pigeonhole uniqueness (`exactCard_unique`).

## 3. Manuscript, Computational & Hygiene Audit

- **PDF Quality:** `main.tex` compiled twice via `pdflatex` with `0` errors, `0` unresolved `??` references, and `0` overfull boxes; every page of `main.pdf` visually inspected via `read_file`.
- **Python Verification:** `verify.py` uses only Python 3.12 standard library, runs deterministically in `< 2s`, and exits `0`.
- **Package Cleanliness & Markdown Math:** `SOURCE.md` untouched (557 bytes); `.lake/` and LaTeX auxiliary files removed; `README.md` and `pr_body.md` checked for strict GitHub Markdown math compliance (no `\operatorname`, `\bowtie`, `\coloneqq`, `\DeclareMathOperator`, `\newcommand`, raw `<`/`>` in math, `$(` openers, or local paths).
