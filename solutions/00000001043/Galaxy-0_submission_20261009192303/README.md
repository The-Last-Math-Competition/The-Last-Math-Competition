# TLMC 1043: a standard-Carlitz-rank counterexample

This project uses Lean 4.31.0 with its bundled `Std`, without Mathlib or external dependencies. Field elements are the concrete modular model `Fin 11`, using core Lean's residue addition, subtraction, multiplication, and powers. No abstract field instance is imported or assumed.

The explicit polynomial

    x − (x−7)^10 + (x−8)^10 − (x−9)^10 + (x−10)^10

induces `(7 8)(9 10)` on F₁₁. The project checks primality, polynomial evaluation, bijectivity, the zero-fixed inversion `I(x)=x^9`, and the complete exclusion of every standard Carlitz expression with at most four inversions.

## Meaning and source caveat

The official conjecture calls Carlitz rank the number of “AB-expression layers,” without defining A/B or citing another source. This submission uses the established mathematical meaning of Carlitz rank: the minimum inversion-count in alternating affine bijections and zero-fixed inversions. It does not claim the repository explains AB. See the full report for the exact primary-source definition and interpretation boundary.

## Formal scope

- `Base.lean`: arbitrary-length syntax and normalization for all nonzero affine slopes and unrestricted translations; exact stripping of normalized layers.
- `FieldModel.lean`: primality of 11, modular reciprocal law, and explicit polynomial equality.
- `Certificate.lean`: kernel-evaluated exclusion of all 11³ triples and 11⁴ quadruples of stripping parameters, including every zero coefficient.
- `Final.lean`: padding lower ranks by inversion pairs, complete rank-at-most-four disproof, and explicit polynomial counterexample.
- `Check.lean`: trusted-axiom audits of the principal theorems.

The finite certificate is not substituted for the semantics: `complete_normal_form` proves that every arbitrary expression counted by the standard rank is covered. `polynomial_counterexample` is the final explicit witness theorem. The project does not claim an exact rank, only that it is larger than four.

## Build and audit

With the specified toolchain available:

    lake build
    lake env lean Check.lean

For a low-memory serial direct build, using the same toolchain:

    export LEAN_PATH=.
    lean -o Base.olean Base.lean
    lean -o FieldModel.olean FieldModel.lean
    lean -o Certificate.olean Certificate.lean
    lean -o Final.olean Final.lean
    lean -o Main.olean Main.lean
    lean Check.lean

A formalization check must confirm successful compilation and the absence of `sorryAx` or any nonstandard axiom. No `native_decide` is used.

## Submission directory layout

The Lean source and Lake configuration are in `lean4/`. From this submission directory, the recommended complete check is:

    bash verify.sh

The shorter Lake commands above must be run after `cd lean4`. The verification script starts from a new temporary directory containing source files only, creates all Lean build products there, saves the clean-build and axiom logs under `logs/`, and runs the independent Python checker.

Build the report with `bash build_pdf.sh`. The script uses an existing TeX installation and includes a search-path/format fallback for installations without a prebuilt TeX index. It does not install software. `solution.tex` is the editable source and `solution.pdf` is the report.

The rank-at-most-four clause is the first part of a conjunction in the official statement. Its counterexample suffices for a disproof under the standard Carlitz-rank meaning; no independent interpretation of the undefined AB shorthand or the additional norm-basis clause is claimed.
