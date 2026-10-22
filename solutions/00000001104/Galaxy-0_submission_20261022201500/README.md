# Counterexample to conjecture 00000001104

Original problem: https://github.com/The-Last-Math-Competition/The-Last-Math-Competition/blob/main/conjectures/00000001104.md

For the Coxeter system of type A4, take W = S5, I = empty, x = 12345 and w = 34512. The empty-parabolic polynomial is the ordinary Kazhdan–Lusztig polynomial, which is 1 + 2q, not monic. The trivial parabolic group contains no affine A1 subgroup.

This verifies a known published example, not a new theorem in Kazhdan–Lusztig theory. See `solution.pdf` / `solution.tex` for the mathematical argument, primary references, and the explicit formalization boundary.

## Lean verification

Requires Lean 4.31.0 with its bundled Std only. No Mathlib or third-party dependencies.

```
lake build
lake env lean -DwarningAsError=true Main.lean
```

The computation is a full finite recurrence over the 120 permutations, not an assigned table of KL polynomial values. Integer lists store coefficients in increasing degree; `[1, 2, 0]` is 1 + 2q.

- `table_permutations`, `table_size`, `table_no_duplicates`, `swap_correct`, `descend_lt`, `descent_in_range`: finite data checks.
- `step_congr`: a recurrence step depends only on shorter second indices.
- `fuel_next`, `fuel_above`, `kl_recurrence`: length-based evaluation is stable and satisfies the actual recurrence, rather than relying on an unproved cutoff.
- `recurrence_unique`: uniqueness of the finite recurrence solution.
- `computed_polynomial`: kernel-checked equality `kl e w = [1,2,0]`.
- `ordinary_counterexample`: failure of universal monicity.
- `recurrence_counterexample`: failure for every family satisfying the same recurrence.

The final computation uses ordinary `decide`, not `native_decide`. The printed axiom audit uses only Lean's standard `propext` and, for the general uniqueness/recurrence theorems, `Quot.sound`; no admissions, custom axioms, or kernel bypasses.

Scope: Lean verifies the finite recurrence and its adequacy/uniqueness. Identification with the abstract Hecke-algebra definition uses the standard theorem cited in the paper. The empty-parabolic identification and exclusion of the affine exception are in the written proof, not claimed to be formalized from abstract Coxeter-group foundations.

## Supplementary cross-checks

```
python3 verification/recurrence_check.py
python3 verification/independent_r_check.py
```

Both use only the Python standard library. The second independently uses R-polynomials and the bar-inversion identity, not the mu recurrence used in Lean. Python output is supplementary and is not represented as a proof.

## PDF

On a standard TeX Live installation:

```
pdflatex -interaction=nonstopmode -halt-on-error solution.tex
pdflatex -interaction=nonstopmode -halt-on-error solution.tex
```

`build_pdf.sh` additionally supports the existing cloud image's unindexed TeX tree. It builds a format from already present TeX sources if necessary and does not install or download anything.

Sources were read and the original conjecture semantics checked on 2026-10-22. All files are confined to this submission; no problem statement, scoreboard or other submission is changed.
