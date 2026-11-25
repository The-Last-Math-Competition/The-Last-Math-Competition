# Self-Review — Conjecture 00000000593

## 1. Source Integrity & Operational Compliance
- **Untouched `SOURCE.md`:** Verified byte-identically preserved at `package/SOURCE.md` (439 bytes).
- **Workspace Isolation:** All reads, writes, builds, and scripts operated strictly inside the conjecture workspace; all commands ran in Standard Sandbox Mode (`BypassSandbox: false`).
- **Compilation Lock Discipline:** Every `lake`, `lean`, and `pdflatex` invocation used `run_lean.py` directly from its working directory.

## 2. Mathematical Completeness & Multi-Reading Audit
- **Standard Mathematical Reading (Affirmative Resolution — Unconditional Across All Fields):**
  - Over *any* field $k$ (including modular characteristic $\mathrm{char}(k) = p \mid |G|$ and finite fields), base-change flatness $\dim_k(R_m^G) = \dim_{\overline{k}}((\overline{k} \otimes_k R)_m^G)$ combined with Dade's subspace-avoidance construction produces a homogeneous system of parameters $f_1, \dots, f_n \in \overline{k}[x_1,\dots,x_n]^G$ all of exact degree $|G|$; Hilbert's Syzygy Theorem over the polynomial ring $\overline{k}[f_1,\dots,f_n]$ proves $H(R^G, t) = P(t) / (1 - t^{|G|})^n$ with $P(t) \in \mathbb{Z}[t]$, so the reduced denominator $Q(t)$ divides $(1 - t^{|G|})^n$ and divides the explicit length-$n$ strict divisibility chain $\prod_{i=1}^n (1 - t^{2^{i-1}|G|})$.
  - Independently and constructively over $k$ itself (without $\overline{k}$, Nullstellensatz, or Syzygy), Emmy Noether's orbit polynomials $\Phi_i(X) = \prod_{g \in G} (X - g \cdot x_i)$ and graded Hilbert–Serre induction yield $Q(t) \mid \prod_{d=1}^{|G|} (1 - t^d)^n$, upgraded via `strictDivChain_upgrade` to a strict divisibility chain.
  - In the non-modular regime ($\mathrm{char}(k) \nmid |G|$), our elementary matrix geometric-series identity $\det(I_n - t A) \det(\sum_{s=0}^{e-1} t^s A^s) = (1 - t^e)^n$ sharpens $|G|$ to $e = \exp(G)$ with strict numerator degree bound $\deg P_G \le n(e - 1) < n e$.
- **Modular Periodic Structure (`modular_periodic_iff`):**
  - Proved the exact three-way equivalence between $(1 - t^D)^n H(t) \in \mathbb{Z}[t]_{< n D}$, vanishing of the $n$-th modular difference $\Delta_D^n a_m = 0$, and discrete Newton quasi-polynomiality $a_{qD+c} = \sum_{j=0}^{n-1} (\Delta_D^j a)_c \binom{q}{j}$ on residue classes modulo $D$ (plus the eventual version for arbitrary $\deg P < m_0 + n D$).
- **Sharpness & Boundary Classification (All Four Alternative/Edge Readings Settled):**
  1. **Necessity of "dividing" vs. "equal to":** Proved on Klein's binary icosahedral group $\mathrm{SL}_2(5) \le \mathrm{GL}_2(\mathbb{C})$ via an integer Bézout identity $(1 + t^4 - t^{12}) P_{\mathrm{ico}} + (-t^2 + t^{10}) Q_{\mathrm{ico}} = 1$, divisibility $Q_{\mathrm{ico}} \mid (1 - t^{12})(1 - t^{60})$, and an arithmetic AM–GM impossibility proof ($d_1 d_2 = 120$ vs. $d_1 + d_2 = 18 \implies d_1 d_2 \le 81 < 120$) that $Q_{\mathrm{ico}} \ne \prod_{i=1}^r (1 - t^{d_i})$ for every positive integer tuple.
  2. **Failure of $\exp(G)$ in modular characteristic:** Proved on $(\mathbb{F}_4, +) \cong C_2 \times C_2$ acting on $\mathbb{F}_4[x, y]$ ($|G| = 4, \exp(G) = 2$), where $Q_{\mathrm{mod}}(t) = (1 - t)(1 - t^4) \nmid (1 - t^2)^2$ while $Q_{\mathrm{mod}}(t) \mid (1 - t^4)^2 \mid (1 - t^4)(1 - t^8)$.
  3. **Minimum chain length $r \ge n$:** Proved for all $n \ge 1$ that $(1 - t)^n \mid \prod_{i=1}^r (1 - t^{d_i}) \implies r \ge n$; in particular, a single factor $(1 - t^d)$ never suffices for $n \ge 2$.
  4. **Refutation of hyper-literal index-rationality $m \mapsto a_m \in \mathbb{Q}(m)$:** Proved on $k[x]^{\{\pm 1\}}$ ($a_m = 1, 0, 1, 0, \dots$) that no polynomials $U, V \in \mathbb{Z}[X]$ with $V(0) \ne 0$ satisfy $a_m V(m) = U(m)$ for all $m \ge 0$.
  5. **Positive non-vacuity witnesses:** Verified both $S_3$ ($2 \nmid 3$ upgraded to $1 \mid 2 \mid 6$) and Bertin's modular non-Cohen–Macaulay ring $\mathbb{F}_2[x_1, x_2, x_3, x_4]^{C_4}$ ($\mathrm{char}(k) = 2 \mid 4$).

## 3. Lean 4.19.0 Formalization Audit
- **Toolchain:** `leanprover/lean4:v4.19.0`, zero external dependencies, `moreLeanArgs = ["-DwarningAsError=true"]`.
- **Forbidden Constructs Check:** Zero `sorry`, zero `admit`, zero `native_decide`, zero custom `axiom` declarations across all seven `.lean` files (`PolySeries.lean`, `ChainDivisibility.lean`, `ModularPeriodic.lean`, `Determinant.lean`, `MatrixMolien.lean`, `Sharpness.lean`, `Conjecture00000000593.lean`).
- **Unconditional Matrix-Group Semantic Faithfulness (`Determinant.lean` & `MatrixMolien.lean`):** Proved full $n \times n$ determinant multiplicativity `det_mul` over general commutative rings `CRing`, the polynomial matrix geometric-series identity `charPolyMat_mul_geomPolyMat`, determinant cofactor divisibility `charDet_mul_geomDet_eq_chainProd` with strict numerator degree `< n * e`, formal power-series inversion `invUnitPoly`, and unconditional master theorems `conjecture_00000000593_master`, `matrix_molien_unconditional`, and `matrix_group_molien_theorem` directly from `∀ A ∈ G, A^e = I_n` (with zero external `hproper` assumption), instantiated end-to-end on `groupNegId2`.
- **Axiom Footprint (`lean-axioms.log`):** Every exported theorem depends exclusively on core Lean's standard logical axioms (`propext`, `Quot.sound`, and `Classical.choice`; with `klein_coprime_polyEq` depending on zero axioms).
- **No Vacuity / Trivialization:** All core theorems quantify universally over arbitrary variable counts `n : Nat`, arbitrary exponents `e : Nat`, arbitrary matrix groups `G : List (Mat Int n)`, arbitrary positive exponent lists `es ds : List Nat`, arbitrary periods `D : Nat`, and arbitrary integer power series `a : Nat → Int`.

## 4. LaTeX, PDF, Python, & Markdown Audit
- **`main.pdf`:** Visually inspected all pages via `read_file`; zero LaTeX errors, zero warnings, zero overfull horizontal or vertical boxes.
- **`verify.py`:** Pure Python 3.12 standard library; deterministic execution verified in `python-verify.log`.
- **`README.md`:** Audited against all GitHub Markdown math rules (uses `\mathrm`, `\lt`, `\bigl(...\bigr)`; zero `\operatorname`, `\coloneqq`, `\newcommand`, raw `<`/`>` inside math, `$(` openings, or local filesystem paths).
- **Artifact Hygiene:** `.lake/` and LaTeX auxiliary files (`*.aux`, `*.out`, `*.toc`, root `*.log`) removed after generating clean verification logs.
