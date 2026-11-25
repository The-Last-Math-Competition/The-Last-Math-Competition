# Self-Review & Semantic Audit (`00000001242`)

## 1. Conjecture Statement Fidelity
- **Source (`SOURCE.md`):** Byte-for-byte identical to `conjectures/00000001242.md`.
- **Statement:** *"Definition: The lamp lighting game (lit-only sigma-game). Conjecture: The graphs with min-lit number at most ⌈n/2⌉ are exactly those with an odd bipartition (a lit-only extremal characterization)."*
- **Verdict:** **DISPROVED (FALSE)** across all standard literature conventions.

## 2. Semantic Coverage Audit (No Convention Escape Hatches)
To prevent any ambiguity over conventions in the lit-only $\sigma$-game literature (Wang & Wu 2006; Wu & Wang 2008; Goldwasser, Klostermeyer & Ware 2009), both `lean/Main.lean`, `main.tex`, and `verify.py` formalize and test **all $2 \times 3 \times 4 = 24$ combinations**:
1. **Move Rules (`MoveRule`):**
   - `MoveRule.openNbr` ($\sigma^-$): pressing a currently lit vertex $v \in S$ toggles all open neighbors $u \in N_G(v)$ while keeping $v$ lit ($v \notin N_G(v)$ by looplessness, proved in `toggleAt_openNbr_self`).
   - `MoveRule.closedNbr` ($\sigma^+$): pressing a currently lit vertex $v \in S$ toggles $N_G[v] = \{v\} \cup N_G(v)$.
2. **Extremal Minimum Light Number (`MinLitMode` & `minLit`):**
   - Defined as an actual `Nat`-valued function over the unbounded reflexive-transitive closure `Reach` (via bounded `Nat` extremal operators `leastUpTo` and `greatestUpTo` with proved attainability and bound theorems `minLitFrom_attained`, `minLitFrom_le_of_reach`, `minLitWorst_attained`, `le_minLitWorst`, `minLitWorstNonempty_attained`, `le_minLitWorstNonempty`):
     - `MinLitMode.fromAllLit`: starting from the all-lit configuration $V$.
     - `MinLitMode.worstAll`: worst-case maximum of $\operatorname{minLitFrom}(S_0)$ over all $S_0 \subseteq V$.
     - `MinLitMode.worstNonempty`: worst-case maximum over all non-empty $\emptyset \neq S_0 \subseteq V$.
   - Ceiling $\lceil n/2 \rceil$ (`ceilHalf n := (n + 1) / 2`) is verified via `ceilHalf_le_iff : ceilHalf n ≤ k ↔ n ≤ 2 * k`.
3. **Odd Bipartition (`OddBipMode` & `HasOddBipartition`):**
   - `existsSomeOdd`: $\exists$ bipartition $V = A \sqcup B$ with $|A|$ odd $\lor$ $|B|$ odd.
   - `existsBothOdd`: $\exists$ bipartition $V = A \sqcup B$ with $|A|$ odd $\land$ $|B|$ odd (automatically non-empty parts).
   - `everySomeOdd`: $G$ is bipartite and every bipartition has $|A|$ odd $\lor$ $|B|$ odd.
   - `everyBothOdd`: $G$ is bipartite and every bipartition has $|A|$ odd $\land$ $|B|$ odd.
4. **Graph-Class Restrictions Checked:**
   - All simple graphs (`Conjecture00000001242`) — refuted across all 24 conventions (`conjecture_00000001242_false_all_conventions`).
   - Connected graphs (`ConjectureConnected`) — refuted across all 24 conventions via $K_3$ and infinite family $K_n$ for all $n \ge 3$ (`conjecture_00000001242_false_connected_all_conventions`, `kn_infinite_counterexample_family`).
   - Connected bipartite graphs (`ConjectureConnectedBipartite`) — refuted across all 24 conventions via $C_4 = K_{2,2}$ and infinite family $K_{2k,2k}$ for all $k \ge 1$ (`conjecture_00000001242_false_connected_bipartite_all_conventions`, `k2k_bipartite_infinite_counterexample_family`).
   - Trees (`ConjectureTrees`) — refuted across all 24 conventions via the 4-vertex path $P_4$ (`conjecture_00000001242_false_trees_all_conventions`, `p4_tree_counterexample_all_conventions`).
   - Converse direction ($\Longleftarrow$) under $\sigma^-$ — refuted for all $m \ge 1$ by both $\overline{K_{2m}}$ (`emptyGraph_even_converse_counterexample`) and $K_2 \sqcup \overline{K_{2m}}$, which has edges (`k2PlusEmpty_converse_counterexample`).

## 3. Non-Vacuity and Non-Triviality Checks
- `k2_positive_witness`: proves $K_2$ ($n = 2$) is connected, satisfies `HasOddBipartition` under all 4 modes, and satisfies `minLit ≤ ceilHalf 2 = 1` under all 6 game conventions.
- `emptyGraph2_minLit_eq_two`: proves `minLit .openNbr .fromAllLit (emptyGraph 2) = 2 > 1 = ceilHalf 2`, confirming `minLit` is not trivially bounded by $\lceil n/2 \rceil$.
- `octahedronGraph_worstAll_gt_ceilHalf`: proves $K_{2,2,2}$ ($n = 6$) is connected and satisfies `ceilHalf 6 < minLit .openNbr .worstAll octahedronGraph` ($4 > 3$), confirming `minLit` is not trivially bounded by $\lceil n/2 \rceil$ even on connected graphs.

## 4. Technical & Build Hygiene Audit
- **Lean Toolchain:** `leanprover/lean4:v4.19.0` (Core Lean only, zero external packages).
- **Compiler Flags:** `moreLeanArgs = ["-DwarningAsError=true"]`; zero warnings or errors.
- **Forbidden Constructs:** Zero `sorry`, `admit`, `native_decide`, custom `axiom`, `unsafe`, `extern`, or `implemented_by`.
- **Kernel Axioms (`lean-axioms.log`):** Every main theorem depends solely on `[propext, Classical.choice, Quot.sound]`.
- **LaTeX (`main.tex` -> `main.pdf`):** Compiled twice with `pdflatex -interaction=nonstopmode -halt-on-error main.tex`; zero errors, zero undefined references, zero hyperref/amsthm warnings, and zero overfull/underfull `\hbox`es.
- **Python (`verify.py`):** Exhaustively checks all $1{,}099$ labelled graphs ($1 \le n \le 5$), all $208$ non-isomorphic graphs ($1 \le n \le 6$, matching OEIS A000088 & A001349), and all infinite counterexample families; exits with code `0`.
- **Cleanliness:** `.lake/`, `main.aux`, `main.log`, `main.out`, and `__pycache__/` removed from `package/`.
