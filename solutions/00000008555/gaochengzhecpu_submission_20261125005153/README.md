# Conjecture 00000008555 — Binary-Relation and Set-Map Representations of Finite Lattices

## Problem Statement

From `SOURCE.md`:

> **English.** Definition: A representation of a lattice is a family of maps to sets. Conjecture: A finite lattice can be completely represented by binary relations; the minimal number of relations of a representation is at most $|L|$, with equality for geometric lattices. (lattice representation relation count)
>
> **中文。** 定义：格的表示指其到集合映射族。猜想：有限格可由二元关系完全表示；表示的极小关系数 ≤ |L| 且等号为几何格。（格表示关系数）

---

## Final Verdict: **FALSE** (Positive Upper Bounds Proved; Geometric-Lattice Equality Refuted)

Conjecture `00000008555` is **false**. While the qualitative representability of every finite lattice by binary relations and the upper bound $\le |L|$ **hold** across standard relational and set-map models (in fact strengthening universally to $\le 1$ for unrestricted equivalence-relation or Galois representations and to $\le |L| - 1 \lt |L|$ for $2$-valued semilattice/order binary relations and subdirect congruences), the **equality $= |L|$ for geometric lattices fails strictly ($\lt |L|$)** across every nontrivial family-size, $2$-valued relation, dimension, congruence, and generator-count model on standard geometric lattices including $B_1$ ($\lvert L \rvert = 2$), $B_2$ ($\lvert L \rvert = 4$), $M_3$ ($\lvert L \rvert = 5$), $M_4$ ($\lvert L \rvert = 6$), $B_3$ ($\lvert L \rvert = 8$), and the non-modular geometric lattice $L(U_{3,4})$ ($\lvert L \rvert = 12$) (as well as $C_1$ when empty families are permitted). Furthermore:

- Under Boolean binary-relation operations $\bigl(\mathcal{P}(X \times X), \cap, \cup\bigr)$, even the first clause fails on non-distributive geometric lattices such as $M_3$, $M_4$, and $L(U_{3,4})$ by Birkhoff's distributivity obstruction.
- Under the degenerate image-cardinality reading $\lvert \varphi(L) \rvert$ of a single injective map $\varphi \colon L \hookrightarrow \mathrm{Eq}(X)$, injectivity forces $\lvert \varphi(L) \rvert = \lvert L \rvert$ tautologically for **every** finite lattice—including the non-geometric chain $C_3$ ($\lvert C_3 \rvert = 3$) and pentagon $N_5$ ($\lvert N_5 \rvert = 5$)—refuting the geometric-lattice characterization ("with equality for geometric lattices" / "且等号为几何格").

---

## Analysis Across All Six Mathematical Models

Let $L$ be a finite lattice (hence automatically a complete bounded lattice with bottom $\hat{0}$ and top $\hat{1}$).

1. **Model $\mathcal{M}_1$ — Equivalence-Relation Lattice Families ($m_{\mathrm{Eq}}(L)$):**
   A complete representation is a jointly injective family $\Phi = (\varphi_i \colon L \to \mathrm{Eq}(X_i))_{i \in I}$ of bounded $\bigl(\wedge, \vee, \hat{0}, \hat{1}\bigr)$-homomorphisms into equivalence-relation lattices $\bigl(\mathrm{Eq}(X_i), \cap, \vee_{\mathrm{Eq}}, \Delta_{X_i}, \nabla_{X_i}\bigr)$.
   - **Positive theorem:** By Whitman's theorem (proved constructively from scratch via a simultaneous $3$-point extension and quotient-free colimit in `lean/Main.lean`) and Pudlák–Tůma's finite partition theorem, every finite lattice embeds completely into $\mathrm{Eq}(X)$ via a **single** map: $m_{\mathrm{Eq}}(C_1) = 0 \lt 1$ and $m_{\mathrm{Eq}}(L) = 1 \le \lvert L \rvert$ for all $\lvert L \rvert \ge 2$.
   - **Geometric counterexamples:** Explicitly over finite base sets of sizes $2$ and $3$, $m_{\mathrm{Eq}}(B_1) = 1 \lt 2$, $m_{\mathrm{Eq}}(B_2) = 1 \lt 4$, and $m_{\mathrm{Eq}}(M_3) = 1 \lt 5$ (even the base set $X_3 = \{0,1,2\}$ for $\mathrm{Eq}(X_3) \cong M_3 \supset B_2$ has $\lvert X_3 \rvert = 3 \lt 4 \lt 5$).

2. **Model $\mathcal{M}_2$ — Boolean Binary-Relation Families ($m_{\mathrm{Bool}}(L)$):**
   Families of $\bigl(\wedge, \vee\bigr)$-homomorphisms into $\bigl(\mathcal{P}(X_i \times X_i), \cap, \cup\bigr)$ exist **if and only if $L$ is distributive**. The modular geometric diamond $M_3$ ($\lvert M_3 \rvert = 5$) is non-distributive and therefore admits **no** such representation at all ($m_{\mathrm{Bool}}(M_3) = \infty$), while distributive geometric lattices satisfy $m_{\mathrm{Bool}}(B_n) = 1 \lt 2^n$ for all $n \ge 1$.

3. **Model $\mathcal{M}_3$ — Set-Maps as Binary Relations via $\mathcal{P}(U_i)^L \cong \mathcal{P}(L \times U_i)$:**
   - *Unrestricted $U_i$ ($m_{\mathrm{Gal}}(L)$):* The principal-downset relation $R_{\le} = \{(x,y) \in L \times L : y \le x\}$ (and Formal Concept Analysis isomorphism $L \cong \mathfrak{B}(L,L,{\le_L})$) represents every finite lattice with $m_{\mathrm{Gal}}(L) \le 1$ ($0$ on $C_1$; $1 \lt \lvert L \rvert$ for $\lvert L \rvert \ge 2$; reduced context pair counts $\lvert I_{\mathrm{red}} \rvert$ are $0 \lt 2$ on $B_1$, $2 \lt 4$ on $B_2$, and $3 \lt 5$ on $M_3$).
   - *Singleton $U_i = \{\ast\}$ ($2$-valued relations $R_i \subseteq L \times \{\ast\}$):* Exact minimums satisfy universal strict inequalities across **all** finite lattices:
     $$m_{\wedge,\mathbf{2}}(L) = \lvert J(L) \rvert \le \lvert L \rvert - 1 \lt \lvert L \rvert, \qquad m_{\vee,\mathbf{2}}(L) = \lvert M(L) \rvert \le \lvert L \rvert - 1 \lt \lvert L \rvert, \qquad \dim_2(L) \le \lvert L \rvert - 1 \lt \lvert L \rvert.$$

4. **Model $\mathcal{M}_4$ — Carrier-Set Binary Relations $R_i \subseteq L \times L$:**
   - *Order / Ferrers dimension $\dim(L)$:* $\dim(L) \le \max\bigl(1, \lfloor \lvert L \rvert / 2 \rfloor\bigr) \lt \lvert L \rvert$ for all $\lvert L \rvert \ge 2$ (Hiraguchi); specifically $\dim(B_1) = 1 \lt 2$, $\dim(B_2) = 2 \lt 4$, and $\dim(M_3) = 2 \lt 5$.
   - *Subdirect congruence count $\mathrm{sub}(L)$:* Because $\mathrm{Con}(L)$ is distributive of height $\le \lvert L \rvert - 1$, $\mathrm{sub}(L) \le \lvert L \rvert - 1 \lt \lvert L \rvert$ universally; in particular $M_3$ is simple ($\mathrm{sub}(M_3) = 1 \lt 5$), $\mathrm{sub}(B_1) = 1 \lt 2$, and $\mathrm{sub}(B_2) = 2 \lt 4$.

5. **Model $\mathcal{M}_5$ — Generating Relations Inside $\mathrm{Eq}(X)$ ($g(L)$ and $g_{01}(L)$):**
   In $\mathrm{Eq}(\{0,1,2\})$, $\{R_{01}, R_{12}\}$ generates all $4$ relations of $B_2$ ($g(B_2) = g_{01}(B_2) = 2 \lt 4$), and $\{R_{01}, R_{02}, R_{12}\}$ generates all $5$ relations of $M_3$ ($g(M_3) = g_{01}(M_3) = 3 \lt 5$), while $g_{01}(C_1) = 0 \lt 1$ and $g_{01}(B_1) = 0 \lt 2$.

6. **Model $\mathcal{M}_6$ — Injective Image Cardinality ($\mathrm{img}(L) = \lvert \varphi(L) \rvert$):**
   Every injective map $\varphi \colon L \hookrightarrow \mathrm{Eq}(X)$ has $\lvert \varphi(L) \rvert = \lvert L \rvert$ for **every** finite lattice $L$. Explicit complete embeddings $C_3 \hookrightarrow \mathrm{Eq}(\{0,1,2\})$ ($\lvert \varphi(C_3) \rvert = 3$) and $N_5 \hookrightarrow \mathrm{Eq}(\{0,1,2,3\})$ ($\lvert \varphi(N_5) \rvert = 5$) show that non-geometric finite lattices satisfy equality equally well.

---

## Summary Table of Invariants

| Lattice $L$ | $\lvert L \rvert$ | Geometric? | $m_{\mathrm{Eq}}$ | $m_{\mathrm{Bool}}$ | $m_{\mathrm{Gal}}$ | $\lvert I_{\mathrm{red}} \rvert$ | $m_{\wedge,\mathbf{2}}$ | $m_{\vee,\mathbf{2}}$ | $\dim_2$ | $\dim$ | $\mathrm{sub}$ | $\bigl(g, g_{01}\bigr)$ | $\mathrm{img}$ |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: |
| $C_1$ | $1$ | Yes | $0$ | $0$ | $0$ | $0$ | $0$ | $0$ | $0$ | $1$ | $0$ | $\bigl(1, 0\bigr)$ | $1$ |
| $B_1$ | $2$ | Yes | $1$ | $1$ | $1$ | $0$ | $1$ | $1$ | $1$ | $1$ | $1$ | $\bigl(2, 0\bigr)$ | $2$ |
| $C_3$ | $3$ | No | $1$ | $1$ | $1$ | $1$ | $2$ | $2$ | $2$ | $1$ | $2$ | $\bigl(3, 1\bigr)$ | $3$ |
| $B_2$ | $4$ | Yes | $1$ | $1$ | $1$ | $2$ | $2$ | $2$ | $2$ | $2$ | $2$ | $\bigl(2, 2\bigr)$ | $4$ |
| $M_3$ | $5$ | Yes | $1$ | $\infty$ | $1$ | $3$ | $3$ | $3$ | $3$ | $2$ | $1$ | $\bigl(3, 3\bigr)$ | $5$ |
| $N_5$ | $5$ | No | $1$ | $\infty$ | $1$ | $4$ | $3$ | $3$ | $3$ | $2$ | $1$ | $\bigl(3, 3\bigr)$ | $5$ |
| $M_4$ | $6$ | Yes | $1$ | $\infty$ | $1$ | $4$ | $4$ | $4$ | $4$ | $2$ | $1$ | $\bigl(4, 4\bigr)$ | $6$ |
| $B_3$ | $8$ | Yes | $1$ | $1$ | $1$ | $6$ | $3$ | $3$ | $3$ | $3$ | $3$ | $\bigl(3, 3\bigr)$ | $8$ |
| $L(U_{3,4})$ | $12$ | Yes | $1$ | $\infty$ | $1$ | $12$ | $4$ | $6$ | $\le 4$ | $\le 4$ | $1$ | $\bigl(4, 4\bigr)$ | $12$ |

---

## Package Contents and Verification

- `SOURCE.md` — Original bilingual problem statement (unmodified).
- `main.tex` and `main.pdf` — Research paper containing full proofs, Hasse diagrams, invariant tables, and Lean correspondence mapping.
- `verify.py` — Standalone Python 3 verification script enumerating all $25$ unlabeled lattices of size $1 \le \lvert L \rvert \le 6$ plus $B_3$ and $L(U_{3,4})$, checking all invariants and Whitman's simultaneous extension step (exits with code `0`).
- `lean/` — Self-contained Core Lean `4.19.0` formalization (`lean-toolchain`, `lakefile.toml`, `lake-manifest.json`, `Main.lean`) with zero external dependencies, `-DwarningAsError=true`, zero `sorry`/`admit`/`native_decide`, and standard axioms (`propext`, `Classical.choice`, `Quot.sound`) only.
- `verification/` — Build and verification logs (`lake-build.log`, `lean-axioms.log`, `lean-version.log`, `pdf-build.log`, `python-verify.log`, `SELF_REVIEW.md`).
