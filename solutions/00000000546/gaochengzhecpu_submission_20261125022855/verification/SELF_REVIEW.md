# Self-Review & Verification Audit — Conjecture 00000000546

## 1. Source Fidelity Check

- **Original Statement (`SOURCE.md`):**
  - English: *"Definition: The depth of monomial subrings. Conjecture: The depth-drop threshold of the numerical semigroup ⟨a, a+1, …, a+k⟩ equals ⌈a/k⌉ (a depth jump for symmetric gaps)."*
  - Chinese: *"定义：Monomial 子环的 depth。猜想：数值半群 ⟨a, a+1, …, a+k⟩ 的深度递降阈值为 ⌈a/k⌉(对称间隙的深度跃变)。"*
- **Integrity:** `package/SOURCE.md` is preserved byte-identically (374 bytes, SHA-256 unchanged).

## 2. Exhaustive Multi-Reading Mathematical Audit

Because `SOURCE.md` pairs the commutative-algebraic heading *"The depth of monomial subrings"* with a claimed *"depth-drop threshold ... (a depth jump for symmetric gaps)"* for $S_{a,k} = \langle a, a+1, \dots, a+k \rangle$ ($a \ge 2$, $1 \le k \le a-1$), we audited all six natural homological and combinatorial interpretations:

1. **Affine monomial subring $K[S_{a,k}] = K[t^a, \dots, t^{a+k}] \subseteq K[t]$:**
   Proved (`affine_ta_is_regSeq1`, `affine_no_regSeq2_extending_ta`) that $(t^a)$ is a regular sequence of length $1$ and $g^{\lceil (a-1)/k \rceil + 1} \in t^a K[S_{a,k}]$ for every full (even inhomogeneous) polynomial $g \in \mathfrak{m}_{S_{a,k}}$. Thus $\mathrm{depth}_{\mathfrak{m}}(K[S_{a,k}]) = 1$ identically across all $(a, k)$ — zero depth drop.
2. **Projective monomial curve coordinate ring $R_{a,k} \subseteq K[u, v]$:**
   Proved (`projectiveClosure_isRegSeq2`, `projectiveClosure_no_regSeq3`) that $(u^{a+k}, v^{a+k})$ is a regular sequence of length $2$ and $G^{\lceil (a-1)/k \rceil + 2} \in (u^{a+k}, v^{a+k}) R_{a,k}$ for every full polynomial $G \in \mathfrak{m}_{R_{a,k}}$. Thus $\mathrm{depth}_{\mathfrak{m}}(R_{a,k}) = 2$ identically across all $(a, k)$ — zero depth drop.
3. **Tangent cone $\mathrm{gr}_{\mathfrak{m}}(K[[S_{a,k}]])$:**
   Proved (`inMaxIdealPower_iff_le_div`, `tangentCone_ta_nonzerodivisor_poly`) that $\nu_{\mathfrak{m}}(t^s) = \lfloor s/a \rfloor$ for all $s \in S_{a,k}$, so $\overline{t^a}$ is a nonzerodivisor and $\mathrm{depth}(\mathrm{gr}_{\mathfrak{m}}) = 1$ identically. Furthermore, we separated its two internal filtration thresholds: the reduction-number / Hilbert-stabilization threshold is $\lceil (a-1)/k \rceil$ (`reductionNumber_threshold_iff`), whereas $\lceil a/k \rceil$ is the nilpotency index of $\overline{t^{a+k}}$ (`topGenerator_nilpotent_in_gr_iff`, i.e., first overlap of consecutive generator sumsets).
4. **Powers of the defining toric ideal $P / I_{a,k}^t$:**
   Verified analytically and by exact rational Gaussian elimination in `verify.py` that complete intersections ($k=1$ for all $a \ge 2$, $k=2$ for even $a \ge 4$) never drop depth, while $S_{5,2}$ drops to depth $0$ at $t = 2 \ne 3 = \lceil 5/2 \rceil$ and symmetric $S_{5,3}$ drops at $t = 3 \ne 2 = \lceil 5/3 \rceil$.
5. **Eliahou's combinatorial depth $q(S_{a,k}) = \lceil C(S_{a,k})/m(S_{a,k}) \rceil$, ordinary power truncations $S_{a,k}^{(m)}$, and the symmetric-gap depth jump:**
   Proved (`eliahouDepth_intervalSemigroup`, `eliahouDepth_ne_conjectured_iff`, `powerSemigroup_ordinary_iff`, `hasSymmetricGaps_iff`, `symmetricGaps_iff_eliahouDepth_jump`, `conjectured_formula_no_jump_at_symmetricGaps`, `eliahouDepth_strict_drop_at_symmetricGaps`) that $q(S_{a,k}) = \lceil (a-1)/k \rceil$, which disagrees with $\lceil a/k \rceil$ iff $a \equiv 1 \pmod{k}$, and jumps by $+1$ ($a-1 \to a$, $k \ge 2$) **if and only if** $S_{a,k}$ has symmetric gaps ($a \equiv 2 \pmod{k}$), whereas $\lceil a/k \rceil$ exhibits zero jump at every symmetric-gap semigroup for $k \ge 2$.
6. **Symmetric-gap pinched Veronese subrings $B_{a,k}^{(m)}$:**
   Proved (`pinchedVeronese_isRegSeq2_iff`) that $(u^{m(a+k)}, v^{m(a+k)})$ is $B_{a,k}^{(m)}$-regular of length $2$ iff $m \ge \lceil (a-1)/k \rceil$, refuting $\lceil a/k \rceil$ whenever $a \equiv 1 \pmod{k}$ (e.g., $(a, k, m) = (5, 2, 2)$).

## 3. Lean 4.19.0 Definition & Non-Vacuity Audit

- **Toolchain & Flags:** `leanprover/lean4:v4.19.0`, zero external dependencies, `moreLeanArgs = ["-DwarningAsError=true"]`.
- **No Shortcuts or Forbidden Constructs:** Zero `sorry`, zero `admit`, zero `native_decide`, zero custom `axiom` declarations, and clean `#print axioms` output across all exported theorems.
- **Structural Faithfulness & Non-Vacuity:**
  - `InIntervalSemigroup a k` is defined inductively from `0` and generator addition $g \in [a, a+k]$.
  - `Poly1 K` and `BivarPoly K` implement genuine Cauchy polynomial multiplication over any constructive field `[FieldCoeff K]` (not restricted to single monomials).
  - `FieldCoeff` is explicitly instantiated on `F2` ($\mathbb{F}_2$), and `nonvacuity_witness_F2_5_2`, `counterexample_S3_1`, `counterexample_S5_2_all_readings`, and `counterexample_symmetric_jump_S5_3` verify that no hypothesis set is vacuous.

## 4. Artifact & Formatting Checks

- `verify.py`: Exits with code `0` (`verification/python-verify.log`).
- `main.pdf`: Compiled cleanly via `pdflatex` with `0` errors and `0` overfull `\hbox`/`\vbox` warnings (`verification/pdf-build.log`), and visually inspected page-by-page.
- `README.md` and `pr_body.md`: Verified clean against all GitHub Markdown math rendering rules (no `\operatorname`, `\bowtie`, `\coloneqq`, `\DeclareMathOperator`, `\newcommand`, raw `<`/`>` inside math, `$(` openings, or local paths).
