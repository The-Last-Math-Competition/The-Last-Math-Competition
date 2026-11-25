# Adversarial Self-Review (`SELF_REVIEW.md`) — Conjecture 00000004768

## 1. Source Alignment & Bilingual Equivalence Audit

### Exact Official Text (`SOURCE.md`)
- **English:**
  > Definition: The noncrossing lattice is the poset lattice of partitions under refinement. Conjecture: Its linear extension count is an explicit hook-length type product, the denominator is the product of block sizes, and the count is computable in polynomial time. (hook-length product of NC linear extensions)
- **中文:**
  > 定义：非交叉格指分拆按加细的偏序格。猜想：其线性扩展计数为钩长型显式积,分母为块大小乘积且计数多项式时间可算。（NC 线性扩展钩长积）

### Term-by-Term Bilingual Comparison
| English Term | Chinese Term | Standard Mathematical Meaning | Representation in `Main.lean` & `main.tex` |
|---|---|---|---|
| noncrossing lattice / NC | 非交叉格 / NC | Lattice $\operatorname{NC}_n$ of noncrossing partitions of $[n]$ ordered by block refinement ($\pi_1 \preceq \pi_2 \iff \forall B_1 \in \pi_1,\, \exists B_2 \in \pi_2,\, B_1 \subseteq B_2$) | `NCPartition n`, `IsNoncrossing`, `Refines`, `ncPartitionLattice` (and also `SetPartition n`, `setPartitionLattice` for $\Pi_n$; Definition 2.1 & Proposition 2.2 of `main.tex`) |
| linear extension count | 线性扩展计数 | Number $e(\operatorname{NC}_n)$ of total orderings of $\operatorname{NC}_n$ (bijections $f : \operatorname{NC}_n \to \operatorname{Fin} |\operatorname{NC}_n|$) satisfying $\pi_1 \preceq \pi_2 \implies f(\pi_1) \le f(\pi_2)$ | `IsLinearExtension`, `HasLinearExtensionCount`, `LinearExtensionBij`, `linearExtensionToBij`, `bijToLinearExtension` (Definition 2.3 of `main.tex`) |
| explicit hook-length type product | 钩长型显式积 | Product formula of Frame–Robinson–Thrall / Knuth / Proctor poset hook type $|\operatorname{NC}_n|! / \prod_{\pi \in \operatorname{NC}_n} h(\pi)$, or rational quotient $(\prod_i a_i) / D_n$ with bounded combinatorial numerator factors | `HasIntegerHookFormula`, `SatisfiesNCBlockSizeHookFormula`, `Conjecture4768_Standard`, `Conjecture4768_Generalized` (Definition 2.3 & Section 4 of `main.tex`) |
| the denominator is the product of block sizes | 分母为块大小乘积 | Denominator $D_n = \prod_{\pi \in \operatorname{NC}_n} \prod_{B \in \pi} |B|$ (also audited against $\prod |B|!$ and principal ideal/filter products) | `partitionBlockSizeProd`, `ncBlockSizeProduct`, `piBlockSizeProduct` (Equation (3) & Theorems 4.1–4.2 of `main.tex`) |
| and the count is computable in polynomial time | 且计数多项式时间可算 | Existence of a polynomial-time algorithm computing $n \mapsto e(\operatorname{NC}_n)$ | Parameterized over an arbitrary predicate `PolyTimeComputable : (Nat → Nat) → Prop` in `Conjecture4768_Standard` and `Conjecture4768_Generalized` |

**Conclusion on Bilingual Equivalence:** Both English and Chinese texts assert the exact same universal three-clause conjunction:
$$\forall n \ge 1,\quad (\text{Hook-length product for } e(\operatorname{NC}_n)) \;\land\; (\text{Denominator} = D_n) \;\land\; (\text{Poly-time computable}).$$
Refuting the product-formula conjuncts at $n = 3$ and $n = 4$ disproves the universal conjunction **unconditionally**, without assuming any unproven complexity separation such as $\mathrm{\#P} \not\subseteq \mathrm{FP}$.

---

## 2. Adversarial Boundary-Case & Convention Audit

We test every plausible way a skeptical reviewer could attempt to rescue the conjecture or question a boundary convention:

1. **Could any predicate in `Main.lean` be vacuously false (making `¬ Conjecture4768_*` hold trivially)?**
   - At $n = 1$ and $n = 2$, the literal block-size hook-length formula $|\operatorname{NC}_n|! = e(\operatorname{NC}_n) \cdot D_n$ **actually holds** ($1! = 1 \cdot 1$ and $2! = 1 \cdot 2$).
   - Theorems `nc1_positive_witness` and `nc2_positive_witness` formally prove `SatisfiesNCBlockSizeHookFormula n ∧ HasIntegerHookFormula (NCPartition n)` for $n = 1$ and $n = 2$ inside Lean, certifying 100% non-vacuity of all definitions.

2. **What if the hook-length formula applies to the interior poset $\operatorname{NC}_n \setminus \{\hat{0}, \hat{1}\}$ of size $|\operatorname{NC}_n| - 2$, or uses $(2n)!$ in the numerator?**
   - `nc4_linExt_not_dvd_factorial_lt53` proves `natFactorial m ≠ e * D` for **every** $m < 53$ and **every** $D \in \mathbb{N}$!
   - Since $|\operatorname{NC}_4| = 14 < 53$, $|\operatorname{NC}_4| - 2 = 12 < 53$, and $2n = 8 < 53$, the prime $53 \mid e(\operatorname{NC}_4) = 1{,}399{,}200$ rules out all of them simultaneously.

3. **What if "denominator is the product of block sizes" means block factorials $\prod |B|!$, or principal ideal/filter sizes $\prod |I(\pi)|$, or an unreduced fraction $(\prod_i a_i)/D_n$ whose numerator is not a single factorial?**
   - `nc4_no_bounded_product_over_denominator` proves that for **every** $D \in \mathbb{N}$ (which covers $D_4 = 331{,}776$, $D_4^{!} = 31{,}850{,}496$, $\prod |I(\pi)| = 8{,}960{,}000$, or $D = 1$) and **every** finite list of integers $1 \le a_i < 53$, $\prod_i a_i \ne e(\operatorname{NC}_4) \cdot D$, because $53$ is prime and $53 \mid e(\operatorname{NC}_4) \cdot D$.
   - Moreover, at $n = 5$ ($|\operatorname{NC}_5| = 42$), `main.tex` (Remark 4.4) documents that $e(\operatorname{NC}_5)$ is divisible by both a $10$-digit prime ($5{,}273{,}727{,}821$) and a $20$-digit prime ($71{,}064{,}201{,}736{,}056{,}904{,}919$), ruling out even polynomial-degree linear factors in $n$ or $C_n$.

4. **What if a literal reader interprets "Definition: The noncrossing lattice is the poset lattice of partitions under refinement" as the unrestricted partition lattice $\Pi_n$ instead of $\operatorname{NC}_n$?**
   - Both lattices are formalized side-by-side (`SetPartition n` with `setPartitionLattice` and `NCPartition n` with `ncPartitionLattice`).
   - At $n = 3$, $\Pi_3 = \operatorname{NC}_3$, so $5! = 120 \ne 6 \cdot 24 = 144$ already refutes the block-size formula on $\Pi_3$.
   - At $n = 4$ ($|\Pi_4| = 15$), `pi4_linExt` certifies $e(\Pi_4) = 10{,}368{,}000 = 2^{10} \cdot 3^4 \cdot 5^3$, and `disproof_conjecture4768_fullPartitionLattice` proves both $15! \ne e(\Pi_4) D(\Pi_4)$ and $\forall D,\, 13! \ne e(\Pi_4) \cdot D$ (since $125 \mid e(\Pi_4)$ while $13! \bmod 125 = 50$).

5. **Does `SetPartition n` / `NCPartition n` omit or duplicate any mathematical partition, or misdefine linear extensions?**
   - `SetPartition.ext_sameBlock` proves canonical uniqueness: two `SetPartition n` values are equal iff they induce the exact same equivalence relation on `Fin n`, and `ofEquivRel` constructs a valid `SetPartition n` from any equivalence relation.
   - `nc1_card`..`nc5_card` verify the Catalan sequence $1, 2, 5, 14, 42$, and `pi4_card` verifies $B_4 = 15$.
   - `linearExtensionToBij` and `bijToLinearExtension` establish explicit mutual translations between duplicate-free exhaustive order-compatible lists `IsLinearExtension` and order-preserving bijections `LinearExtensionBij P N`.

---

## 3. Formal Hygiene & Build Audit Checklist

- **Zero external dependencies:** `lake-manifest.json` has `"packages": []`; compiles completely offline in Core Lean `v4.19.0`.
- **Warnings as errors:** `moreLeanArgs = ["-DwarningAsError=true"]` in `lakefile.toml`, and `lake env lean -DwarningAsError=true Main.lean` exits with `0` and zero warnings.
- **Forbidden constructs check:** Zero occurrences of `sorry`, `admit`, `native_decide`, `unsafe`, `implemented_by`, `extern`, `opaque`, or user-declared `axiom` anywhere in `Main.lean`.
- **Axiom footprint:** Every `#print axioms` check depends exclusively on subsets of `{propext, Classical.choice, Quot.sound}`.
- **LaTeX hygiene:** Two-pass `pdflatex -interaction=nonstopmode -halt-on-error main.tex` produces `main.pdf` with zero errors, zero undefined references/citations, zero `hyperref` warnings, zero `Overfull \hbox`, and zero `Underfull \hbox` warnings.
- **Independent Python cross-check:** `verify.py` independently verifies all lattice axioms and cross-checks $e(\operatorname{NC}_4) = 1{,}399{,}200$ via order-ideal DP, coatom-order telescoping, and atom-order telescoping.
