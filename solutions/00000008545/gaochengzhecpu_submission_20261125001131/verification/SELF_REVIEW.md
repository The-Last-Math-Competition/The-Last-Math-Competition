# Self-Review Audit — Conjecture 00000008545

## 1. Conjecture & Verdict Verification
- **Conjecture ID:** `00000008545`
- **Source Fidelity:** `SOURCE.md` verified byte-identical to `conjectures/00000008545.md`.
- **Verdict:** **Disproved (False under all standard mathematical conventions).**

## 2. Semantic & Mathematical Completeness Audit
Conjecture `00000008545` defines lattice uniformity as the evenness (constancy/uniformity, Mandarin: 均匀) of element covering numbers and asserts a conjunction of two claims:
1. **Clause 1:** The spectra of upper and lower uniform lattices are symmetric (`上/下均匀的格的谱对称`).
2. **Clause 2:** The minimal example of failure of uniformity is the $5$-element nonmodular lattice $N_5$ (`均匀性的失败的最小例为 5 元素非模格`).

We verified that **no reasonable convention escapes refutation**:
- **Regime I (Global non-extremal covering constancy — $c^+$ constant on $L \setminus \{\hat{1}\}$, $c^-$ constant on $L \setminus \{\hat{0}\}$):**
  - *Universal theorem proved (`all_card_le_3_globally_uniform`):* Every finite lattice with $|L| \le 3$ is globally uniform.
  - *Counterexample (`disproof_global_minimal_counterexample`):* $B_2 = C_2 \times C_2$ has $|B_2| = 4 < 5$ and is distributive (hence modular), yet $c^+(\hat{0}) = 2 \neq 1 = c^+(a)$ and $c^-(\hat{1}) = 2 \neq 1 = c^-(a)$, refuting Clause 2. At size $5$, $M_3$, $B_2 \oplus \mathbf{1}$, and $\mathbf{1} \oplus B_2$ (all modular) also fail global uniformity.
  - *Ancillary global variants (`disproof_ancillary_global_variants`):* Unrestricted constancy on $L$ and literal arithmetic parity ($2 \mid c^+$) fail on $C_2$ ($|C_2|=2$, modular); undirected Hasse regularity fails on $C_3$ ($|C_3|=3$, modular) and holds on $N_5$.
- **Regime II (Strict interior covering constancy on $L \setminus \{\hat{0}, \hat{1}\}$):**
  - *Counterexamples (`disproof_interior_uniformity`):* $N_5$ **satisfies** both interior upper and lower uniformity ($c^+(x) = c^-(x) = 1$ on $\{a,b,c\}$), so $N_5$ is not a counterexample at all; meanwhile the $5$-element distributive modular lattices $B_2 \oplus \mathbf{1}$ and $\mathbf{1} \oplus B_2$ fail interior uniformity, refuting Clause 2. Furthermore, $N_5$ has Hasse adjacency trace $\operatorname{tr}(A^5) = 10 \neq 0$, refuting $0$-symmetry of the eigenvalue spectrum.
- **Regime III (Graded rank-wise covering constancy — Terwilliger uniform lattices):**
  - *Canonical rank uniqueness & $N_5$ non-gradedness (`grading_unique`, `N5_nonmodular_and_nongraded`):* Any two gradings on a finite lattice coincide everywhere, and $N_5$ is indeed the unique minimal counterexample to rank-uniformity.
  - *Whitney spectrum & rank-covering profile counterexample (`disproof_rank_uniform_whitney_and_profile`):* $B_2 \oplus \mathbf{1}$ ($|L|=5$, distributive and modular) is both rank-upper-uniform and rank-lower-uniform, yet its Whitney spectrum $(1,2,1,1)$ is not palindromic and its rank-covering profile violates top-bottom symmetry ($c^+(\hat{0}) = 2 \neq 1 = c^-(\hat{1})$).
  - *Covering-degree multiset & upper/lower duality counterexample (`disproof_rank_upper_uniform_multiset`):* The $7$-element graded lattice $L_7$ is rank-upper-uniform and interior-upper-uniform, yet fails rank-lower-uniformity, has non-palindromic Whitney spectrum $(1,3,2,1)$, and has unequal upper and lower covering-degree multisets $\{0,1,1,1,1,1,3\} \neq \{0,1,1,1,1,2,2\}$.
  - *Non-graded shortest-chain height layer uniformity + Hasse graph spectrum (`disproof_min_height_hasse_spectrum`):* $N_5 \oplus \mathbf{1}$ ($|L|=6$) has constant $c^+$ on every shortest-chain height layer from $\hat{0}$ yet satisfies $\operatorname{tr}(A^5) = 10 \neq 0$.
- **Non-Vacuity Audit (`nonvacuous_C3`, `nonvacuous_B2_rank_uniform`):** Explicitly proved that $C_3$ and $B_2$ inhabit all positive definitions (distributivity, modularity, interior uniformity, rank uniformity, palindromic Whitney spectrum, rank-covering symmetry, and multiset symmetry).

## 3. Lean 4 Formalization Audit (`lean/Main.lean`)
- **Toolchain:** `leanprover/lean4:v4.19.0` (self-contained Core Lean 4, zero external packages).
- **Compiler Flags:** `-DwarningAsError=true` enabled in `lakefile.toml` and verified standalone.
- **Forbidden Constructs Check:** Zero `sorry`, `admit`, `native_decide`, `Lean.ofReduceBool`, `unsafe`, `extern`, `implemented_by`, or custom `axiom` declarations.
- **Axiom Footprint (`verification/lean-axioms.log`):** Only constructive standard Lean kernel axioms `[propext, Quot.sound]` (or zero axioms on `distributive_implies_modular`).

## 4. Computational & Artifact Hygiene Audit
- **Python Verification (`verify.py` / `verification/python-verify.log`):** Exhaustively enumerates all unlabeled lattices for $1 \le n \le 7$ (confirming OEIS A006966: $1, 1, 1, 2, 5, 15, 53$) and verifies all claims; exits with code `0`.
- **LaTeX & PDF (`main.tex` / `main.pdf` / `verification/pdf-build.log`):** Compiles cleanly in two passes with `0` errors, `0` warnings, `0` overfull boxes, and `0` underfull boxes; all `.aux`, `.log`, and `.out` files removed from `package/`.
- **Cleanliness:** `lean/.lake/` removed after build verification; no temporary files remain in `package/`.
