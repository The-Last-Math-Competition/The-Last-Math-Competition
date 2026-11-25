# Conjecture 00000007610 — Same-Representation, Different-Center Extension Separation in Clifford Algebras

## Verdict: **TRUE**

Conjecture `00000007610` holds unconditionally. In the structure theory of Clifford algebras over a field $K$ with $\mathrm{char}(K) \neq 2$, the **irreducible-representation spectrum** $\mathrm{Spec}_{\mathrm{rep}}^K(A)$ (the cardinality of simple left $A$-module isomorphism classes together with their $K$-dimensions) and the **center spectrum** $\mathrm{Spec}_{\mathrm{cen}}(A)$ (the commutative ring/$K$-algebra isomorphism class of the genuine center $Z(A) = \{z \in A \mid \forall x \in A,\, z x = x z\}$, equivalently the affine scheme $\mathrm{Spec}(Z(A))$ with its residue fields) form two distinct structural layers that separate as soon as $K$ admits a quadratic field extension.

---

## Problem Statement

> **English.** Definition: Representation spectra and center spectra are two layers. Conjecture: There exist two Clifford algebras with the same irreducible-representation spectrum but different center spectra, and the separation is realized by an explicit field-extension pair with the same representation but different center. (same representation-different center extension separation)
>
> **中文。** 定义：表示谱与中心谱指两层。猜想：存在两 Clifford 代数的不可约表示谱相同而中心谱不同,分离由同表示异中心的显式域扩张对实现。（表示同-中心异扩张分离）

---

## Mathematical Summary

### 1. Why Field Extensions Are Essential (No-Go Over Algebraically Closed Fields)

Over an algebraically closed field such as $\mathbb{C}$, every nondegenerate Clifford algebra $\mathrm{Cl}_n(\mathbb{C})$ with $n \ge 1$ satisfies:
- Even $n = 2m$: $\mathrm{Cl}_{2m}(\mathbb{C}) \cong M_{2^m}(\mathbb{C})$, with $\mathrm{Spec}_{\mathrm{rep}}^{\mathbb{C}} = (1; [2^m])$ and $Z \cong \mathbb{C}$ ($\dim_{\mathbb{C}} Z = 1$).
- Odd $n = 2m + 1$: $\mathrm{Cl}_{2m+1}(\mathbb{C}) \cong M_{2^m}(\mathbb{C}) \times M_{2^m}(\mathbb{C})$, with $\mathrm{Spec}_{\mathrm{rep}}^{\mathbb{C}} = (2; [2^m, 2^m])$ and $Z \cong \mathbb{C} \times \mathbb{C}$ ($\dim_{\mathbb{C}} Z = 2$).

Thus over $\mathbb{C}$ alone, $\mathrm{Spec}_{\mathrm{rep}}^{\mathbb{C}}(\mathrm{Cl}_n(\mathbb{C}))$ uniquely determines $Z(\mathrm{Cl}_n(\mathbb{C}))$ up to $\mathbb{C}$-algebra isomorphism. More precisely, over **any** quadratically closed field $K$ ($\forall c \in K,\, \exists u \in K,\, u^2 = c$) with $\mathrm{char}(K) \neq 2$, every nondegenerate $1$-generator Clifford algebra $\mathrm{Cl}(K^1, (d_2)) \cong K \times K$ splits into two $1$-dimensional simple modules, whereas every nondegenerate $2$-generator Clifford algebra $\mathrm{Cl}(K^2, (d_0, d_1)) \cong M_2(K)$ has a unique $2$-dimensional simple module (`quadratically_closed_obstruction`). Hence a nontrivial quadratic field extension is both **necessary and sufficient** for separation.

### 2. Three Unconditional Separation Regimes (All Formalized in Lean 4.19.0)

| Regime | Explicit Clifford Algebra Pair | Irreducible-Representation Spectrum | Genuine Ring-Theoretic Center $Z(A)$ | Separation Invariant |
| :--- | :--- | :--- | :--- | :--- |
| **Regime I** (Fixed base field $\mathbb{Q}$) | $A_1 = \mathrm{Cl}_{1,1}(\mathbb{Q}) \cong M_2(\mathbb{Q})$ vs. $A_2 = \mathrm{Cl}_{0,1}(\mathbb{Q}) \cong \mathbb{Q}(i)$ | $\mathrm{Spec}_{\mathrm{rep}}^{\mathbb{Q}}(A_1) = (1; [2]) = \mathrm{Spec}_{\mathrm{rep}}^{\mathbb{Q}}(A_2)$ | $Z(A_1) \cong \mathbb{Q}$ vs. $Z(A_2) \cong \mathbb{Q}(i)$ | $\dim_{\mathbb{Q}} Z$: $1 \neq 2$, and $z^2 + 1 = 0$ solvable in $Z(A_2)$ only |
| **Regime II** (Same dimension $n = 1$) | $C_1 = \mathrm{Cl}(\mathbb{Q}^1, (2)) \cong \mathbb{Q}(\sqrt{2})$ vs. $C_2 = \mathrm{Cl}(\mathbb{Q}^1, (-1)) \cong \mathbb{Q}(i)$ | $\mathrm{Spec}_{\mathrm{rep}}^{\mathbb{Q}}(C_1) = (1; [2]) = \mathrm{Spec}_{\mathrm{rep}}^{\mathbb{Q}}(C_2)$ | $Z(C_1) \cong \mathbb{Q}(\sqrt{2})$ vs. $Z(C_2) \cong \mathbb{Q}(i)$ | $z^2 + 1 = 0$ unsolvable in $\mathbb{Q}(\sqrt{2})$ since $a^2 + 2b^2 + 1 \gt 0$ |
| **Regime III** (Base-field extension $\mathbb{Q} \hookrightarrow \mathbb{Q}(i)$) | $B_{\mathbb{Q}} = \mathrm{Cl}_{1,1}(\mathbb{Q})$ vs. $B_{\mathbb{Q}(i)} = \mathrm{Cl}_{1,1}(\mathbb{Q}(i))$ | $\mathrm{Spec}_{\mathbb{Q}} = (1; [2]) = \mathrm{Spec}_{\mathbb{Q}(i)}$ on identical integer spinor matrices | $Z(B_{\mathbb{Q}}) \cong \mathbb{Q}$ vs. $Z(B_{\mathbb{Q}(i)}) \cong \mathbb{Q}(i)$ | $Z(B_{\mathbb{Q}}) \not\simeq_{\mathrm{Ring}} Z(B_{\mathbb{Q}(i)})$ |

The exact same algebraic proofs hold verbatim over $\bigl(\mathbb{R}, \mathbb{C}\bigr)$ (since $-1 \notin (\mathbb{R}^\times)^2$), and lift in fixed dimension $n = 3$ to noncommutative $8$-dimensional Clifford algebras $\mathrm{Cl}(\mathbb{Q}^3, (1, -1, -1)) \cong M_2(\mathbb{Q}(i))$ vs. $\mathrm{Cl}(\mathbb{Q}^3, (1, -1, -2)) \cong M_2(\mathbb{Q}(\sqrt{-2}))$ with $\mathrm{Spec}_{\mathrm{rep}}^{\mathbb{Q}} = (1; [4])$.

---

## Lean 4.19.0 Formalization Architecture (`lean/`)

Built from first principles in pure Lean `v4.19.0` with `moreLeanArgs = ["-DwarningAsError=true"]`, **zero external dependencies**, **zero `sorry`**, and **zero custom axioms**:

- **`Conjecture00000007610/Algebra.lean`**: Genuine unital rings, fields, $K$-vector spaces, $K$-algebras, ring and $K$-algebra homomorphisms/isomorphisms (`RingIso`, `AlgIso`), proof that $\dim_K K^1 \neq \dim_K K^2$ (`not_kLinearIso_fin1_fin2`), and the genuine ring-theoretic center `Center A` (`{z : A | ∀ x : A, z * x = x * z}`) with transport under `RingIso` and `AlgIso`.
- **`Conjecture00000007610/Fields.lean`**: Exact rational field `RatQ` constructed from quotient pairs `(num, den)` with `0 \lt den`, proofs that $-1$ and $2$ are non-squares in $\mathbb{Q}$ (`ratQ_nonSquare_neg_one`, `ratQ_nonSquare_two`), general quadratic field extensions `QuadExt K d` (`Qi`, `Qsqrt2`), and unital ring non-homomorphism theorems `no_ringHom_qi_to_ratQ` and `no_ringHom_qi_to_qsqrt2`.
- **`Conjecture00000007610/Clifford.lean`**: Genuine $2^n$-dimensional Clifford algebra `Clifford K n d` for arbitrary $n \in \mathbb{N}$ via Chevalley's $\mathbb{Z}/2\mathbb{Z}$-graded recursion, exact $K$-dimension $2^n$ (`clifford_hasKDim`), fundamental identity $\iota(v)^2 = Q_d(v) \cdot 1$ (`Clifford.iota_sq`), and the **Universal Property of Clifford Algebras** (`Clifford.lift`, `Clifford.lift_iota`, `Clifford.lift_unique`).
- **`Conjecture00000007610/Modules.lean`**: Genuine left $A$-modules, submodules, textbook simple modules (`IsSimpleModule A M`: $M \neq \{0\}$ and every submodule is $\{0\}$ or $M$), module isomorphisms (`ModuleIso`), `HasUniqueSimpleModuleOfDim K A m` (existence of a simple module of exact $K$-dimension $m$ **and** uniqueness of simple left $A$-modules up to $A$-linear isomorphism across the universe), field simple-module classification (`field_simple_module_unique`), and $M_2(K)$ center and Morita simple-module classification (`mat2CenterAlgIso`, `mat2_hasUniqueSimpleModuleOfDim`).
- **`Conjecture00000007610/Separation.lean`**:
  - `cl11IsoMat2`: Explicit spinor $K$-algebra isomorphism $\mathrm{Cl}_{1,1}(K) \xrightarrow{\sim} M_2(K)$ for $\mathrm{char}(K) \neq 2$.
  - `regime_I_separation`: Unconditional separation for $\mathrm{Cl}_{1,1}(\mathbb{Q})$ vs. $\mathrm{Cl}_{0,1}(\mathbb{Q})$ with center pair $\bigl(\mathbb{Q}, \mathbb{Q}(i)\bigr)$.
  - `regime_II_same_dim_separation`: Unconditional same-dimension ($n = 1$, $\dim_{\mathbb{Q}} A = 2$) separation for $\mathrm{Cl}(\mathbb{Q}^1, (2))$ vs. $\mathrm{Cl}(\mathbb{Q}^1, (-1))$ with center pair $\bigl(\mathbb{Q}(\sqrt{2}), \mathbb{Q}(i)\bigr)$.
  - `regime_III_base_extension_separation`: Unconditional base-field extension separation along $\mathbb{Q} \hookrightarrow \mathbb{Q}(i)$ on $\mathrm{Cl}_{1,1}$.
  - `quadratically_closed_obstruction`: Formal proof that over any quadratically closed field ($\mathrm{char}(K) \neq 2$), no $1$-generator nondegenerate Clifford algebra can share $\mathrm{Spec}_{\mathrm{rep}}^K = (1; [2])$ with $\mathrm{Cl}_2$.
  - `conjecture_00000007610_true`: Combined existential theorem resolving Conjecture `00000007610`.

---

## Package Contents & Reproduction

- `SOURCE.md` — Exact unmodified problem statement.
- `main.tex`, `main.pdf` — Self-contained mathematical paper proving the obstruction theorem and all three separation regimes.
- `verify.py` — Standalone exact rational computational verification suite (Python 3 standard library only).
- `lean/` — Pure Lean `v4.19.0` formalization (`lake build` inside `lean/`).
- `verification/` — Build, version, axiom-audit, PDF compilation, Python verification logs, and `SELF_REVIEW.md`.
