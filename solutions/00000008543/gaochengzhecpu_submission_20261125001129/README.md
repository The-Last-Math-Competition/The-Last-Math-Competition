# Conjecture 00000008543 — Disproof (Boolean Lattice Automorphism Type)

## Official Statement (`SOURCE.md`)

- **English:** *Definition: A Boole lattice is a Boolean lattice. Conjecture: The automorphism group of a Boolean lattice is the symmetric group; its irreducible automorphisms are of transposition type; and the isomorphism classification is uniquely determined by the dimension. (Boolean lattice automorphism type)*
- **中文：** *定义：Boole 格即布尔格。猜想：布尔格的自同构群为对称群；其不可约自同构为对换型；同构分类由维数唯一决定。（布尔格自同构型）*

## Verdict: **DISPROVED (FALSE)**

Conjecture `00000008543` is **false** under every standard mathematical interpretation—both over **general Boolean lattices** (where all three clauses fail independently) and when restricted strictly to **finite Boolean lattices** $B_n = \mathcal{P}(\{0, \dots, n-1\})$ (where Clauses I and III hold, Clause II holds for $n \le 2$, and Clause II fails in **every** finite dimension $n \ge 3$).

### Summary of the Two-Level Refutation

1. **Level A — Finite Boolean Lattices $B_n$ ($n \ge 3$):**
   - **Positive Foundations (Faithfulness & Non-Vacuity):** For every $n \in \mathbb{N}$, $B_n = (\mathrm{Fin} n \to \mathrm{Bool})$ is an atomic Boolean lattice of dimension $n$ (`Atoms(B_n) ≃ Fin n`), $\mathrm{Aut}(B_n) \cong S_n$ (`finBoolAutGroupIso`), and $B_m \cong B_n \iff m = n$ (`finBool_iso_iff_eq`). For $n = 2$, every non-identity automorphism is indeed an atom transposition (`finBool2_nonid_isAtomTransposition`).
   - **Refutation of Clause II for Every $d = n + 3 \ge 3$:** The cyclic shift automorphism $\sigma_d = (0\;1\;\dots\;d-1) \in \mathrm{Aut}(B_d)$ (`cycleAut`) is irreducible under:
     - **(I1) Direct-factor / central-idempotent indecomposability** (`IsDirectFactorIrreducible`: its only fixed elements in $B_d$ are $\bot$ and $\top$);
     - **(I2) Boolean-sublattice simplicity** on $B_3$ (`IsSublatticeIrreducible`: $B_3$ has zero proper nontrivial $\sigma_3$-invariant Boolean sublattices);
     - **(I3) Disjoint-support cycle indecomposability** (`IsCycleIrreducible`: cannot be factored into two non-identity automorphisms of disjoint atom support);
     - **(I4) $\mathbb{F}_2$-linear irreducibility** on the $2$-dimensional augmentation hyperplane $W_0 \subset (B_3, \triangle)$ (`IsF2ReducedIrreducible3`: minimal polynomial $x^2 + x + 1$ over $\mathbb{F}_2$).
   - Yet $\sigma_d^2 \neq \mathrm{id}$ (exact order $d \ge 3$), so $\sigma_d$ fails even the broadest possible notion of transposition type (**non-identity involution** $f^2 = \mathrm{id}$, `IsInvolutionAut`), and hence is neither an atom transposition (`IsAtomTransposition`) nor conjugate to one (`IsConjugateToAtomTransposition`). Conversely, for $d \ge 3$, **no** atom transposition on $B_d$ is direct-factor irreducible (`atomTransposition_not_directFactorIrreducible`).

2. **Level B — General (Countably Infinite) Boolean Lattices:**
   - **Refutation of Clause I (`hybridBL_aut_not_iso_any_perm`):** Let $L_{\mathrm{dyad}}$ be the countable atomless Boolean lattice of $2^k$-periodic subsets of $\mathbb{N}$ (`dyadicBL`), and set $L_* = L_{\mathrm{dyad}} \times B_2$ (`hybridBL`). Every automorphism of $L_*$ permutes its two atoms $\{(\emptyset, e_0), (\emptyset, e_1)\}$ and therefore fixes $\bigl(\emptyset, \top\bigr)$ and $\bigl(\mathbb{N}, \bot\bigr)$, placing the right-factor swap $\zeta = (\mathrm{id}, \mathrm{swap}) \neq \mathrm{id}$ into the center $Z(\mathrm{Aut}(L_*))$ while $|\mathrm{Aut}(L_*)| \ge 4$. Because no symmetric group $\mathrm{Sym}(X)$ on **any** set $X$ (finite or infinite) can simultaneously satisfy $|\mathrm{Sym}(X)| \ge 3$ and $Z(\mathrm{Sym}(X)) \neq \{\mathrm{id}\}$, we obtain $\mathrm{Aut}(L_*) \not\cong \mathrm{Sym}(X)$ for **every** type `X : Type u` (and also $\mathrm{Aut}(L_{\mathrm{dyad}}) \not\cong \mathrm{Sym}(\mathrm{Atoms}(L_{\mathrm{dyad}}))$).
   - **Refutation of Clause III (`not_blIso_finCofin_prodFC`):** Let $L_{\mathrm{fc}}$ (`finCofinBL`) be the Boolean lattice of finite or cofinite subsets of $\mathbb{N}$, and compare $L_{\mathrm{fc}}$ with $L_{\mathrm{fc}} \times L_{\mathrm{fc}}$ (`prodFC`). Both are atomic Boolean lattices with explicit atom bijection $\mathrm{Atoms}(L_{\mathrm{fc}}) \simeq \mathbb{N} \simeq \mathrm{Atoms}(L_{\mathrm{fc}} \times L_{\mathrm{fc}})$, an explicit $\mathbb{F}_2$-linear bijection $\bigl(L_{\mathrm{fc}}, \triangle, \bot) \cong_{\mathbb{F}_2} (L_{\mathrm{fc}} \times L_{\mathrm{fc}}, \triangle, \bot\bigr)$ (`f2LinearIso_finCofin_prodFC`), unbounded poset chain height $\infty$, and countable cardinality $\aleph_0$. Nevertheless, $L_{\mathrm{fc}} \not\cong L_{\mathrm{fc}} \times L_{\mathrm{fc}}$ because $\bigl(\mathbb{N}, \emptyset\bigr)$ and its complement $\bigl(\emptyset, \mathbb{N}\bigr)$ in $L_{\mathrm{fc}} \times L_{\mathrm{fc}}$ both dominate infinitely many distinct atoms, which is impossible in $L_{\mathrm{fc}}$.

## Package Contents

- `SOURCE.md` — Exact copy of `conjectures/00000008543.md`.
- `main.tex`, `main.pdf` — Self-contained mathematical paper (10 pages, compiled with 2-pass `pdflatex`, zero errors/warnings/overfull boxes).
- `lean/` — Self-contained Core Lean 4.19.0 formalization (`lean-toolchain`, `lakefile.toml` with `-DwarningAsError=true`, `lake-manifest.json`, `Main.lean` with `#print axioms`).
- `verify.py` — Standalone Python 3.12 computational verification script (standard library only).
- `verification/` — Full build and verification logs (`lean-version.log`, `lake-build.log`, `lean-axioms.log`, `pdf-build.log`, `python-verify.log`) and `SELF_REVIEW.md`.

## Reproduction Instructions

```bash
# 1. Verify Core Lean 4.19.0 formalization (zero external dependencies)
cd lean
lake build

# 2. Run standalone Python 3.12 verification suite
cd ..
python verify.py

# 3. Compile LaTeX manuscript (two passes)
pdflatex -interaction=nonstopmode -halt-on-error main.tex
pdflatex -interaction=nonstopmode -halt-on-error main.tex
```
