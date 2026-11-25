# Self-Review and Verification Audit — Conjecture 00000007626

## 1. Statement Faithfulness Audit

- **`SOURCE.md` Integrity:** Verified byte-for-byte unchanged (`542` bytes).
- **All Three Clauses & All Standard Interpretations Formalized:**
  - **Connected-family structure (`IdemSpectrum`, `ProperIdemSpectrum`, `PrimIdemSpectrum`, `UnitConj`, `LeftIdealIso`):** Formalizes $\mathbb{A}^1$-polynomial homotopy connectedness (`PolyStep` and `PolyConn` via the genuine polynomial ring `Poly A`), unit conjugacy (`UnitConj`), and cyclic projective left-ideal module isomorphism (`LeftIdealIso`, proven equivalent to Murray–von Neumann algebraic equivalence in `leftIdealIso_iff_murrayVonNeumann`). Topological and smooth connectedness over $\mathbb{R}$ and $\mathbb{C}$ are shown in `main.tex` (Theorem 2.4) to yield the identical multi-rank spectrum $\prod_{i=1}^b (n_i + 1)$.
  - **Clause I (Finiteness):** Proven to hold for finite-dimensional algebras with exact cardinality $\prod_{i=1}^b (n_i + 1)$, and proven to fail when finite-dimensionality is omitted (`clause1_infinite_counterexample` on $\mathbb{Z}^{\mathbb{N}}$).
  - **Clause II (Matrix-block bound $|\pi_0(E(A))| \le b(A)$):** Refuted across all idempotent loci:
    1. *All idempotents $E(A)$:* `all_idempotents_exceed_block_count` ($\prod(n_i + 1) \ge 2^b > b$), `Mat2.mat2IdemSpectrumEquivFin3` ($3 > 1 = b$ on $M_2(K) \cong \mathrm{Cl}_{1,1}(K)$ over every field $K$), `Mat.singleBlockAllMap_injective` ($\ge n + 1 > 1$ on $M_n(K)$).
    2. *Proper idempotents $E^\circ(A) = E(A) \setminus \{0, 1\}$:* `proper_bound_iff_sporadic` (holds iff profile is `[1]`, `[2]`, or `[1, 1]`), `Mat.singleBlockProperMap_injective` ($\ge n - 1 \ge 2 > 1$ on $M_n(K)$ for all $n \ge 3$), `Mat.clifford22_proper_three_gt_one` ($3 > 1$ on $\mathrm{Cl}_{2,2}(K) \cong M_4(K)$), and `Mat.split_clifford_unbounded_proper_spectrum` (unbounded $2^m - 1 \to \infty$ divergence vs. $b = 1$ on $\mathrm{Cl}_{m,m}(K) \cong M_{2^m}(K)$).
    3. *Central & non-semisimple regimes:* `commBlockSpectrumEquiv` + `powRing_comm_isCentralIdem` ($2^b > b$), and `UpperTri2` ($4 > 2 = b$).
  - **Clause III (Isomorphism-class counting $b(A) \le c_{\mathrm{iso}}(A)$):** Formalizes ring-isomorphism class counting of matrix blocks (`ExactAlgIsoClassCount`), proving the universal reverse inequality $c_{\mathrm{alg}} \le b$ (`algIsoClasses_le_blockCount`), strict refutation $b > 1 = c_{\mathrm{alg}}$ (`clause3_refuted_homogeneous`), and simultaneous double strict reverse inequalities $|\pi_0| > b > c_{\mathrm{alg}}$ (`double_reverse_inequality_master`), alongside module-isomorphism analysis (`LeftIdealIso`).

## 2. Non-Vacuity & Positive Structural Witnesses

To ensure no typeclass or predicate is vacuously satisfied:
1. **Concrete Field & Ring Witnesses in Multiple Characteristics:** Constructs both `QField` ($\mathbb{Q}$, instantiating `Field QField` and `TorsionFreeRing QField` in characteristic $0$) and `F2` ($\mathbb{F}_2$, instantiating `Field F2` in characteristic $2$), plus `Int`, instantiating concrete theorems (`concreteMat2QEquiv`, `concreteMat2F2Equiv`, `concreteClifford22Q`).
2. **Small-Rank Coincidence & Primitive Idempotent Salvage:** Proves `Mat2.mat2ProperSpectrumEquivUnit` ($|\pi_0(E^\circ(M_2(K)))| = 1 = b$) and `mat2PowPrimSpectrumEquiv` ($\mathrm{Prim}(E((M_2(K))^b)) \simeq \mathrm{Fin}\,b$ of exact size $b$), explaining why the conjecture appeared plausible on low-rank and primitive spinor examples.
3. **Universal Nilpotent Homotopy Invariance:** Proves Newton's polynomial step (`newtonLiftStep_sub_self`) and explicit polynomial conjugation modulo nilpotent elements (`nilpotent_diff_polyStep`).

## 3. Formal Soundness & Hygiene Checklist

- **Toolchain:** `leanprover/lean4:v4.19.0` (Core Lean 4 only, zero external packages).
- **Compiler Flags:** `moreLeanArgs = ["-DwarningAsError=true"]` enabled and passing cleanly.
- **Forbidden Constructs Scan:** Zero occurrences of `sorry`, `admit`, `native_decide`, `axiom`, `unsafe`, `extern`, `implemented_by`, or `opaque` in `lean/Main.lean`.
- **Axiom Footprint (`lean-axioms.log`):** Every major theorem depends exclusively on subsets of `[propext, Classical.choice, Quot.sound]`.
- **Independent Python Verification (`verify.py`):** Standard library only; exits with code `0` across all $5$ verification suites (including all $45$ real Clifford signatures $0 \le p + q \le 8$).
- **PDF Quality (`main.pdf`):** Compiled twice with `pdflatex -interaction=nonstopmode -halt-on-error main.tex`, zero overfull/underfull boxes, visually inspected page by page.
- **GitHub Markdown Math Compliance (`README.md` and PR summary):** Programmatically audited for zero `\operatorname`, `\bowtie`, `\coloneqq`, `\DeclareMathOperator`, `\newcommand`, raw `<`/`>` inside math delimiters, `$(` inline math openings, or local filesystem paths.
