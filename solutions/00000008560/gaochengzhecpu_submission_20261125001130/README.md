# Conjecture 00000008560 — Disproof and Formal Lean 4.19.0 Verification

## Official Conjecture (`SOURCE.md`)

- **English:** *Definition: The category of lattices is the category of lattices with order-preserving maps. Conjecture: Two finite lattice categories are equivalent if and only if the lattices are isomorphic; and the smallest nontrivial self-equivalence of the category is the duality equivalence, whose smallest example is the pentagon lattice at n = 3. (lattice category duality equivalence)*
- **中文:** *定义：格范畴为格与保序映射的范畴。猜想：两个有限格范畴等价 iff 格同构；范畴等价的最小非平凡自等价为对偶等价且其最小例为 n=3 的五边形格。（格范畴对偶等价）*

## Verdict: **DISPROVED (FALSE)**

Conjecture `00000008560` asserts a conjunction whose first part holds as a theorem, whose global autoequivalence classification holds, and whose final witness claim (*"whose smallest example is the pentagon lattice at n = 3"*) is **false under every faithful mathematical reading**:

1. **Clause 1 Holds (`clause1_holds`):** Viewing any finite lattice $L$ as a thin poset category $\mathcal{C}(L)$ (objects $x \in L$, unique morphism $x \to y$ iff $x \le y$), skeletalness of $\mathcal{C}(L)$ yields $\mathcal{C}(L_1) \simeq \mathcal{C}(L_2) \iff L_1 \cong L_2$ as lattices.
2. **Global Category Autoequivalence Classification (`clause2a_global_holds`):** In the category $\mathbf{Lat}_{\mathrm{fin}}^{\mathrm{ord}}$ of finite lattices with order-preserving maps, order duality $D = (-)^{\mathrm{op}} : L \mapsto L^{\mathrm{op}}, f \mapsto f$ is a strict involutive covariant self-equivalence that is not naturally isomorphic to $\mathrm{Id}$, and every covariant self-equivalence of $\mathbf{Lat}_{\mathrm{fin}}^{\mathrm{ord}}$ is naturally isomorphic either to $\mathrm{Id}$ or to $D$.
3. **Complete Refutation of Clause 2b (`conjecture_00000008560_complete_resolution`):**
   - **No pentagon at $|L| = 3$ (`no_pentagon_at_card_3`):** Every $3$-element lattice is isomorphic to the $3$-element chain $C_3$, which is distributive, modular, and self-dual.
   - **The pentagon lattice $N_5$ is self-dual and rigid (`N5_is_self_dual`, `N5_not_movedByDuality`, `N5_poset_cat_rigid`):** The pentagon lattice $N_5 = \{\hat{0}, a, b, c, \hat{1}\}$ has $|N_5| = 5$ (height $3$, $3$ interior elements) and satisfies $N_5^{\mathrm{op}} \cong N_5$ via $\hat{0} \leftrightarrow \hat{1}, a \leftrightarrow b, c \leftrightarrow c$. Thus $\lparen -)^{\mathrm{op}}$ fixes $N_5$ up to isomorphism at *every* parameter $n$, and $\mathrm{Aut}(N_5) = \{\mathrm{id}\}$ so $\mathcal{C}(N_5)$ has no nontrivial covariant self-equivalence.
   - **True minimal non-self-dual lattices (`all_card_le_4_self_dual`, `OneSumB2_isMovedByDuality`, `min_card_movedByDuality`):** Every finite lattice with $|L| \le 4$ (and every finite lattice of height $\le 2$) is self-dual. The unique smallest non-self-dual lattices ($L^{\mathrm{op}} \not\cong L$, occurring at $|L| = 5$ and height $3$) are the mutually dual planar **distributive** lattices $\mathbf{1} \oplus B_2$ and $B_2 \oplus \mathbf{1}$, not $N_5$.
   - **Individual thin-category readings (`B2_has_nontrivial_poset_autoEquiv`, `C2_contravariant_nontrivial`):** Nontrivial covariant self-equivalences of $\mathcal{C}(L)$ first occur on $B_2$ ($|B_2| = 4$, height $2$), nontrivial contravariant self-dualities of $\mathcal{C}(L)$ first occur on $C_2$ ($|C_2| = 2$, height $1$), and naturality of $\mathrm{Id} \Rightarrow (-)^{\mathrm{op}}$ on $\mathbf{Lat}_{\mathrm{fin}}^{\mathrm{ord}}$ already fails on $\{C_1, C_2\}$ ($|L| \le 2$).

## Package Structure

- `SOURCE.md` — Byte-identical copy of `conjectures/00000008560.md`.
- `main.tex`, `main.pdf` — Self-contained mathematical manuscript and compiled 9-page PDF.
- `verify.py` — Standalone Python 3.12 script exhaustively enumerating finite lattices ($1 \le |L| \le 6$, OEIS A006966) and verifying all claims.
- `lean/` — Self-contained Core Lean 4.19.0 formalization (`lean-toolchain`, `lakefile.toml`, `lake-manifest.json`, `Main.lean`), compiled with `-DwarningAsError=true` and zero external dependencies over `[propext, Quot.sound]` only.
- `verification/` — Build and verification logs (`lean-version.log`, `lake-build.log`, `lean-axioms.log`, `pdf-build.log`, `python-verify.log`, `SELF_REVIEW.md`).

## Reproduction Commands

```powershell
# 1. Exhaustive Python verification
python verify.py

# 2. Core Lean 4.19.0 formal verification
cd lean
lake build
cd ..

# 3. Two-pass LaTeX compilation
pdflatex -interaction=nonstopmode -halt-on-error main.tex
pdflatex -interaction=nonstopmode -halt-on-error main.tex
```
