# Conjecture 00000008545 — Disproof Package

- **Conjecture ID:** `00000008545`
- **Verdict:** **Disproved (False under every mathematical convention)**

## Official Statement (`SOURCE.md`)

> **English.** Definition: Uniformity of a lattice is the evenness of element covering numbers. Conjecture: The spectra of upper and lower uniform lattices are symmetric; and the minimal example of failure of uniformity is the 5-element nonmodular lattice. (minimal counterexample to uniformity)
>
> **中文。** 定义：格的一致性（均匀性）指元素覆盖数的均匀。猜想：上/下均匀的格的谱对称；均匀性的失败的最小例为 5 元素非模格。（均匀性最小反例）

## Summary of the Refutation

Let $\bigl(L, \le, \wedge, \vee, \hat{0}, \hat{1}\bigr)$ be a finite lattice, let $x \lessdot y$ denote the covering relation ($x \lt y$ with no $z$ satisfying $x \lt z \lt y$), and let $c^+(x) = |\{y \in L : x \lessdot y\}|$ and $c^-(x) = |\{y \in L : y \lessdot x\}|$ denote the upper and lower covering numbers of $x \in L$.

Conjecture `00000008545` asserts a conjunction of two claims:
1. **Clause 1 (Spectrum symmetry):** Upper and lower uniform lattices have symmetric spectra.
2. **Clause 2 (Minimal counterexample):** The minimal failure of uniformity is the $5$-element nonmodular pentagon lattice $N_5$.

We classify all natural definitions of covering-number uniformity ("元素覆盖数的均匀") and lattice spectra ("谱") and prove that the conjecture is **false under every convention**:

1. **Regime I — Global Non-Extremal Covering Uniformity** ($c^+$ constant on $L \setminus \{\hat{1}\}$ and $c^-$ constant on $L \setminus \{\hat{0}\}$):
   - Every finite lattice of cardinality $\le 3$ ($C_1, C_2, C_3$) is globally uniform (`all_card_le_3_globally_uniform`).
   - At cardinality **$4 \lt 5$**, the Boolean diamond **$B_2 = C_2 \times C_2$** is **distributive (hence modular)** yet fails both global upper uniformity ($c^+(\hat{0}) = 2 \neq 1 = c^+(a)$) and global lower uniformity ($c^-(\hat{1}) = 2 \neq 1 = c^-(a)$), refuting **Clause 2** (`disproof_global_minimal_counterexample`). Even at size $5$, the modular lattices $M_3$, $B_2 \oplus \mathbf{1}$, and $\mathbf{1} \oplus B_2$ also fail global uniformity. (Unrestricted constancy on $L$ and literal arithmetic parity fail at $C_2$ of size $2$, while undirected Hasse degree regularity fails at $C_3$ of size $3$ and holds on $N_5$.)

2. **Regime II — Strict Interior Covering Uniformity** ($c^+$ and $c^-$ constant on $L^\circ = L \setminus \{\hat{0}, \hat{1}\}$):
   - **$N_5$ satisfies strict interior uniformity** ($c^+(x) = c^-(x) = 1$ for all three interior elements of $N_5$), so $N_5$ is not a counterexample at all!
   - Instead, the minimal counterexamples at size $5$ are the **distributive (hence modular)** ordinal sums **$B_2 \oplus \mathbf{1}$** and **$\mathbf{1} \oplus B_2$**, refuting **Clause 2**; furthermore $N_5$ has Hasse adjacency matrix trace $\mathrm{tr}(A^5) = 10 \neq 0$, refuting $0$-symmetry of the graph eigenvalue spectrum (`disproof_interior_uniformity`).

3. **Regime III — Graded Rank-Wise Covering Uniformity** (Terwilliger's uniform posets/lattices: $L$ is graded and $c^+, c^-$ depend only on rank):
   - Under this strengthened definition, $N_5$ is indeed the unique minimal counterexample to uniformity, **but Clause 1 fails under every standard meaning of lattice spectrum**:
     - **Whitney / rank-size spectrum and rank-covering profile:** The $5$-element distributive modular lattice **$B_2 \oplus \mathbf{1}$** is *both* rank-upper-uniform and rank-lower-uniform, yet has non-palindromic Whitney spectrum $\bigl(1, 2, 1, 1) \neq (1, 1, 2, 1\bigr)$ and asymmetric rank-covering profile (`disproof_rank_uniform_whitney_and_profile`).
     - **Covering-degree multiset spectrum and upper/lower symmetry:** The $7$-element graded lattice **$L_7$** ($\hat{0} \lessdot p, q \lessdot u \lessdot \hat{1}$ and $\hat{0} \lessdot r \lessdot v \lessdot \hat{1}$) is rank-upper-uniform (and interior-upper-uniform), yet is *not* rank-lower-uniform, has asymmetric Whitney spectrum $\bigl(1, 3, 2, 1\bigr)$, and has unequal upper vs. lower covering-degree multisets $\{0, 1, 1, 1, 1, 1, 3\} \neq \{0, 1, 1, 1, 1, 2, 2\}$ (`disproof_rank_upper_uniform_multiset`).
     - **Shortest-chain height layer uniformity + Hasse graph spectrum:** The $6$-element lattice **$N_5 \oplus \mathbf{1}$** has constant $c^+$ on every shortest-chain height layer from $\hat{0}$ yet satisfies $\mathrm{tr}(A^5) = 10 \neq 0$ (`disproof_min_height_hasse_spectrum`).

## Package Layout & Reproduction Commands

- `SOURCE.md` — Exact copy of `conjectures/00000008545.md`.
- `main.tex`, `main.pdf` — Self-contained mathematical paper and compiled PDF.
- `verify.py` — Pure-Python exhaustive verification over all unlabeled lattices of sizes $1 \le n \le 7$.
- `lean/` — Self-contained Core Lean 4 (`v4.19.0`) formalization (`Main.lean`, `lakefile.toml`, `lean-toolchain`, `lake-manifest.json`), with zero external dependencies, zero `sorry`, zero `native_decide`, and zero custom axioms.
- `verification/` — Complete build and audit logs plus `SELF_REVIEW.md`.

To reproduce all checks locally:
```bash
python verify.py
cd lean && lake build && lake env lean -DwarningAsError=true Main.lean
pdflatex -interaction=nonstopmode -halt-on-error main.tex
```
