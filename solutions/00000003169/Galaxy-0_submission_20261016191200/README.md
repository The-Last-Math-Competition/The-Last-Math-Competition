# TLMC 00000003169: counterexample

For f=x+y+1 and g=(x+y)^3+x+2y+4 the unique complex root is (1,-2), simple and in the torus. The ideal equals (x-1,y+2), so this is a reduced nonempty complete intersection. Newton polytopes Δ and 3Δ have BKK-normalized mixed volume 3 (classical mixed area 3/2), both different from the root count 1.

The claim refuted is the original unconditional equality. The generic BKK equality and universal upper bound remain true. Source wording, domains, multiplicity and normalization are addressed in paper.pdf.

## Reproduce

Use an already installed Lean 4.31.0 toolchain, Python 3 standard library, and optionally pdfLaTeX:

    ./VERIFY.sh /absolute/path/to/lean-4.31.0/bin
    ./build_pdf.sh

On a minimal TeX image with a prebuilt pdflatex.fmt, its directory may be passed as the first build_pdf.sh argument. The helper sets standard installed TeX/font search paths; it installs nothing.

## Formal boundary

Algebra.lean uses genuine sparse-polynomial evaluation over arbitrary commutative rings, exact roots, generic ideal-generator identities, computed formal derivatives, and characteristic-zero nonzero-coefficient/torus proofs.

Geometry.lean defines a generic nonnegative-weight convex hull of exponent lists, proves support_f_hull/support_g_hull connecting the actual computed supports to the coordinate formulas, and proves the triangle and Minkowski descriptions over arbitrary linearly ordered fields. Triangle areas use the determinant formula, then mixed-area polarization.

Main.lean proves exhaustive nodup root enumeration for arbitrary commutative-ring carriers and uses that enumeration's length in the final mismatch theorem. It does not restrict the root count to rational roots. Root and area carriers are independent parameters.

The handwritten proof supplies the standard interpretation over C, the ideal quotient/regular-sequence/multiplicity argument, and the determinant-area identification with real Euclidean area. Lean does not construct a complex-number library, ideal/quotient scheme infrastructure or Lebesgue measure. These limits are expressly stated in paper.pdf; no conclusion-specific axiom hides them.

## Verification

- Lean 4.31.0 Std only; no package downloads.
- All Algebra, Geometry, Main modules compile.
- Independent leanchecker kernel replay passes for all three modules.
- Audit.lean reports only propext, Classical.choice, Quot.sound.
- No sorry, native_decide, external oracle, custom conclusion axiom or kernel bypass.
- verify.py independently checks four ideal identities, the formal derivative determinant, actual support convex hulls, Minkowski hull and exact rational area polarization.
- PDF rendered and visually checked on all three pages.

## Intended submission files

Algebra.lean; Geometry.lean; Main.lean; Audit.lean; lakefile.lean; lake-manifest.json; lean-toolchain; VERIFY.sh; verify.py; build_pdf.sh; paper.tex; paper.pdf; source.md; README.md; logs/toolchain.log; logs/build.log; logs/kernel-Algebra.log; logs/kernel-Geometry.log; logs/kernel-Main.log; logs/axioms.log; logs/independent.log.

Do not include Probe.lean, candidate search notes, .lake, .tex-cache, intermediate TeX files or obsolete failed-build logs. Parent may add independent review, eligibility, manifest and checksum files at publication.
