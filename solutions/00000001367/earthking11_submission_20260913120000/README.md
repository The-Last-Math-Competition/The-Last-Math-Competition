# Submission for conjecture 00000001367 — verdict: **FALSE**

Directory: `earthking11_submission_20260913120000`

## Summary

Conjecture 00000001367 claims that the Cayley graph of $\mathbb{Z}^2$ with
generators $\{\pm e_1,\pm e_2\}$ has classical chromatic number $4$ and Borel
chromatic number $5$ (the Borel constraint forcing one extra color).

This is refuted. The graph is exactly the square grid, which is **bipartite**:
the parity map $(i,j)\mapsto(i+j)\bmod 2$ is a proper $2$-coloring. Therefore

* the classical chromatic number is **$2$**, not $4$; and
* since $\mathbb{Z}^2$ is countable, every subset is Borel, so the parity
  coloring is Borel measurable and the Borel chromatic number is also **$2$**,
  not $5$.

Both asserted values are wrong, and no extra color is forced by the Borel
constraint in this instance.

## Contents

| Path | Description |
|------|-------------|
| `README.md` | This file. |
| `main.tex` | Standalone article (amsmath/amssymb/amsthm) proving bipartiteness, $\chi=2$, and $\chi_B=2$ via countability. |
| `build/main.pdf` | Compiled article (`tectonic --outdir build main.tex`). |
| `reproduce.py` | Stdlib-only computational check that the parity coloring is proper on the patch $[-250,250]^2$; prints $\chi=2$, $\chi_B=2$, PASS, exit 0. |
| `lean4/` | Core Lean 4 formalisation (no Mathlib) of the combinatorial part. See `lean4/README.md`. |

## Lean 4

Pinned toolchain: `leanprover/lean4:v4.33.1` (`lean4/lean-toolchain`).

```sh
cd lean4
lake build
lake env lean Check.lean
```

`Main.lean` defines the grid adjacency `Adj`, the parity coloring `col`, proves
`parity_proper`, builds a proper `Fin 2`-coloring (`two_coloring_exists`), shows
no `Fin 3`-coloring is forced to be improper (`chromatic_not_four`), and collects
the refutation in `conjecture_00000001367_false`. The Borel-measurability step
(countable discrete space $\Rightarrow$ all subsets Borel) is a documented
mathematical statement, not formalised in core Lean; see `lean4/README.md`.

## Reproduce

```sh
python3 reproduce.py
cd lean4 && lake build && lake env lean Check.lean
cd .. && tectonic --outdir build main.tex
```

## Verdict

The conjecture is **false**: $\chi = 2$ and $\chi_{\mathrm{Borel}} = 2$.
