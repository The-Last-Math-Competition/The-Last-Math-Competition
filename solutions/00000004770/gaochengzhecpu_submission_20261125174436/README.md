# Conjecture 00000004770 — Disproof and Formal Verification

**Verdict:** **FALSE** across all canonical annular and boundary noncrossing partition families (with machine-checked formal proofs in Core Lean 4.19.0 and exact combinatorial verification in Python, together with a complete characterization of the scope boundary for arbitrary induced sublattices).

---

## 1. Problem Summary

Conjecture `00000004770` (`SOURCE.md`, stated identically in English and Chinese) considers two combinatorial invariants of a family of noncrossing partitions under refinement order: its **Möbius function spectrum** and its **lattice isomorphism type**. It conjectures that:

1. There exist two families of noncrossing partitions with the same Möbius function spectrum and non-isomorphic lattices; and
2. This separation is realized by an explicit pair of an **annular family** and a **boundary family**.

---

## 2. Mathematical Resolution

### Why Low Orders and Coarse Counts Were Deceptive
Three numerical coincidences in free probability and Coxeter combinatorics make an annular-versus-boundary separation appear plausible at first sight:
- **The $\binom{2n}{n}$ equinumerosity family:** For all $n \ge 1$, Mingo–Nica's ${(n, 1)}$-annular noncrossing permutation poset $S_{\mathrm{NC}}(n, 1)$, Reiner's rotational/zero-block Type-$B$ lattice $\mathrm{NC}^{(B)}(n)$, and Simion's two half-disc reflection-boundary lattices $\mathrm{NC}^{\mathrm{sym}}_{\mathrm{edge}}(2n)$ and $\mathrm{NC}^{\mathrm{sym}}_{\mathrm{vert}}(2n)$ all have cardinality $\binom{2n}{n} = 2, 6, 20, 70, 252, \dots$ and are pairwise non-isomorphic for $n \ge 2$.
- **Low-order isomorphisms:** At $n = 1, 2$, $\mathrm{NC}_A(1, 1) \cong S_{\mathrm{NC}}(1, 1) \cong \mathrm{NC}(2) \cong \mathrm{NC}^{(B)}(1) \cong \mathrm{NC}^{\mathrm{sym}}(2)$ (size $2$) and $\mathrm{NC}_A(2, 1) = \Pi_3 = \mathrm{NC}(3) \cong \mathrm{NC}_\partial(2)$ (size $5$).
- **Top-Möbius coincidence at $n = 4$:** $\mu_{\mathrm{NC}_A(4, 1)}(0, 1) = +20 = \mu_{\mathrm{NC}^{(D)}(4)}(0, 1)$, although $\lvert \mathrm{NC}_A(4, 1) \rvert = 49 \neq 50 = \lvert \mathrm{NC}^{(D)}(4) \rvert$.

Upon exact structural analysis, **every canonical annular–boundary pair fails**, under all standard formulations of the Möbius function spectrum (lower-interval multiset, upper-interval multiset, characteristic polynomial, and full two-variable interval multiset):

1. **Obstruction I — Annular Non-Lattice Dichotomy:**
   - **Annular permutations $S_{\mathrm{NC}}(p, q)$:** For $p, q \ge 1$, $S_{\mathrm{NC}}(p, q)$ is a lattice **if and only if** $p = q = 1$. For all $p + q \ge 3$ (already at $S_{\mathrm{NC}}(2, 1)$ of size $6$), $S_{\mathrm{NC}}(p, q)$ fails both the join-semilattice and meet-semilattice axioms.
   - **Annular set partitions $\mathrm{NC}_A(p, q)$ ($p \ge q \ge 1$):** Under refinement order, $\mathrm{NC}_A(p, q)$ is a lattice **if and only if** $q = 1$ or $\bigl(p, q\bigr) \in \{(2, 2), (3, 2)\}$:
     - For $q = 1$, we prove the universal identity
       $$
 \mathrm{NC}_A(p, 1) = \bigl\{\pi \in \Pi(p + 1) : \pi\rvert_{[p]} \in \mathrm{NC}(p)\bigr\} = \mathrm{NC}_\partial^\circ(p),
 $$
       showing that $\mathrm{NC}_A(p, 1)$ is canonically isomorphic to the circular-boundary noncrossing partition lattice of cardinality $\frac{p + 3}{2} C_p$ and total Möbius number ${(-1)^p} \binom{2p - 2}{p - 1}$ (non-self-dual for all $p \ge 3$).
     - For ${(2, 2)}$ and ${(3, 2)}$, $\mathrm{NC}_A(2, 2) = \Pi_4$ ($15$ elements) and $\mathrm{NC}_A(3, 2) = \Pi_5$ ($52$ elements).
     - For **all** $p \ge q \ge 2$ with $p + q \ge 6$ (starting at ${(4, 2)}$ of size $189$ and ${(3, 3)}$ of size $200$), $\mathrm{NC}_A(p, q)$ fails both unique joins and unique meets.

2. **Obstruction II — Universal Canonical Rigidity:**
   - Within the equinumerous $\binom{2n}{n}$ family ($n \ge 2$), $\lvert \mu_{\mathrm{NC}^{(B)}(n)}(0, 1) \rvert = \binom{2n - 1}{n - 1} \gt C_{n - 1} = \lvert \mu_{\mathrm{NC}^{\mathrm{sym}}(2n)}(0, 1) \rvert$ ($3 \gt 1$, $10 \gt 2$, $35 \gt 5$, $\dots$), separating both lower-interval and full two-variable Möbius spectra. Meanwhile, Kreweras complementation gives an order-duality isomorphism between the two reflection-boundary lattices $\mathrm{NC}^{\mathrm{sym}}_{\mathrm{edge}}(2n)$ and $\mathrm{NC}^{\mathrm{sym}}_{\mathrm{vert}}(2n)$, which remain separated by their lower-interval Möbius spectra.
   - Across **all** parameters $\bigl(p, q, m\bigr) \in (\mathbb{N}^+)^3$ of all canonical annular lattices ($\mathrm{NC}_A(p, 1)$, $\mathrm{NC}_A(2, 2)$, $\mathrm{NC}_A(3, 2)$, $\mathrm{NC}(p) \times \mathrm{NC}(q)$, and rotational $\mathrm{NC}^{(B)}(p)$) and all canonical boundary lattices ($\mathrm{NC}_\partial(m) \cong \mathrm{NC}(m + 1)$, $\mathrm{NC}_\partial^\circ(m)$, $\mathrm{NC}^{(B)}(m)$, $\mathrm{NC}^{(D)}(m)$, and $\mathrm{NC}^{\mathrm{sym}}(m)$), exact division-free ratio bounds and the Type-$D$ central-binomial sandwich
     $$
 \binom{2m - 2}{m - 1} \lt \bigl\lvert \mu_{\mathrm{NC}^{(D)}(m)}(0, 1) \bigr\rvert \lt \binom{2m}{m} \qquad \bigl(m \ge 5\bigr)
 $$
     prove that $\bigl(\lvert \mathcal{A} \rvert, \lvert \mu_{\mathcal{A}}(0, 1) \rvert\bigr) = \bigl(\lvert \mathcal{B} \rvert, \lvert \mu_{\mathcal{B}}(0, 1) \rvert\bigr)$ holds **if and only if** $\bigl(\mathcal{A}, \mathcal{B}\bigr)$ is one of the six canonical lattice-isomorphic pairs.

3. **Scope Boundary — Arbitrary Induced Noncrossing Sublattices:**
   - Dropping canonical surface families in favor of arbitrary finite subposets inside planar $\mathrm{NC}(N)$, explicit $5$-element induced sublattices in $\mathrm{NC}(4)$ share the lower-interval Möbius spectrum $\{1^2, -1^2, 0^1\}$, and explicit $10$-element self-dual graded interval-partition sublattices in $\mathrm{NC}(8)$ share lower, upper, characteristic-polynomial, and full two-variable Möbius spectra ($\{1^{12}, -1^{11}, 0^{30}\}$) while being non-isomorphic. Thus the failure of Conjecture `00000004770` is a genuine rigidity theorem for canonical annular and boundary families.

---

## 3. Package Layout and Verification Commands

| Path | Description |
| :--- | :--- |
| `SOURCE.md` | Original untouched conjecture statement (English and Chinese) |
| `main.tex` / `main.pdf` | Self-contained mathematical paper and complete structural classification |
| `verify.py` | Standalone exact Python verification suite ($p + q \le 6$, parameter sweep up to $50$) |
| `lean/Conjecture00000004770/PosetMobius.lean` | Finite posets, lattices, incidence algebra, $\mu$ existence/uniqueness, dual symmetry, isomorphism invariance |
| `lean/Conjecture00000004770/PartitionsAndAnnulus.lean` | Set partitions, $\mathrm{NC}(N)$, $\mathrm{NC}_A(p, q)$, universal $\mathrm{NC}_A(p, 1) = \mathrm{NC}_\partial^\circ(p)$, universal join failure ($p \ge q \ge 2, p + q \ge 6$) |
| `lean/Conjecture00000004770/CanonicalRigidity.lean` | Size-$6$ disproofs ($S_{\mathrm{NC}}(2, 1)$, $\mathrm{NC}^{(B)}(2)$, $\mathrm{NC}^{\mathrm{sym}}(4)$) and universal all-parameter canonical rigidity |
| `lean/Conjecture00000004770/SubfamilyScope.lean` | Explicit $5$-element ($\mathrm{NC}(4)$) and $10$-element ($\mathrm{NC}(8)$) non-isomorphic Möbius-isospectral sublattices |
| `lean/Conjecture00000004770.lean` | Root module exporting `conjecture_00000004770_positive_foundations` and `conjecture_00000004770_disproof` |
| `verification/` | Build logs (`lake-build.log`, `lean-axioms.log`, `lean-version.log`, `pdf-build.log`, `python-verify.log`) and `SELF_REVIEW.md` |

To reproduce all checks from scratch:
- **Python verification:** run `python verify.py` from the package root.
- **Lean 4.19.0 formal verification:** run `lake build` inside `lean/` (configured with `leanprover/lean4:v4.19.0` and `-DwarningAsError=true`, zero external dependencies).
- **PDF build:** run `pdflatex main.tex` twice from the package root.
