# Lean project for Conjecture 00000007914

This project proves a universal contradiction between finite ordered ranks in a nonnegative real set and the exact asymptotic asserted in the conjecture.

## Reproduction

Use the pinned `lean-toolchain` (Lean 4.19.0). From this folder run:

```sh
lake exe cache get
lake build
lake env lean -DwarningAsError=true CovolumeSpectrum.lean
lake env lean -DwarningAsError=true Audit.lean
```

`lake-manifest.json` locks Mathlib and all transitive dependencies. The mathematical proof is entirely in `CovolumeSpectrum.lean`; `Audit.lean` prints the axioms of the substantive theorems. No additional executable computation is required.

The author validated using a local stock Mathlib checkout/cache at the locked revision; local `.lake/packages` symlinks are disposable build infrastructure and are not part of the deliverable. A fresh project can fetch the same pinned stock dependencies through Lake. All dependency tracked sources were clean after validation.

## Main results

- `no_rankedAsymptotic`: no nonnegative real set has the source's finite ranks and asymptotic.
- `no_numericalConjecture`: the numerical conjunction, including well-ordering, is false for every nonnegative real set.
- `no_full_conjunction`: the same remains false with arbitrary additional clauses and a spectrum selected from the closure of nonnegative raw covolumes.
- `no_liminf_spectrum_conjunction`: the same contradiction for spectra selected from finite sequential limit inferiors, covering the Chinese liminf reading.
- `no_measure_spectrum_conjunction`: raw nonnegativity is supplied directly from an arbitrary family of measured spaces, covering quotient-volume measures.

See the parent folder's `proof.tex` / `proof.pdf` and `SEMANTIC_REVIEW.md` for the precise source-to-formal correspondence and the source's undefined 'limit-from-below' terminology.
