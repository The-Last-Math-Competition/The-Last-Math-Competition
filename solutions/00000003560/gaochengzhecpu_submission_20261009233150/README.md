# Conjecture 00000003560: equality does not imply congruence

The compact convex intervals A=[0,1] and B=[0,2] have positive finite Lebesgue measure and satisfy equality in Brunn--Minkowski in dimension one: their Minkowski sum is [0,3], and 3=1+2. Their metric diameters differ, so no Euclidean isometry maps A onto B. They are homothetic, B=2A.

This refutes the source's congruence conclusion for the original summands. The source supplies no equal-volume normalization. The submission does not assess a corrected statement up to positive homothety, separate volume normalization, or the additional genus-rate clause. The full proof and exact formalization correspondence are in `main.tex` and `main.pdf`; the bilingual source is preserved in `SOURCE.md`.

## Reproduction

In `lean/`, run `lake build` and `lake env lean -DwarningAsError=true Main.lean`. Lean 4.19.0, Mathlib commit c44e0c8ee63ca166450922a373c7409c5d26b00b and transitive dependencies are pinned through public Git URLs. A new machine can fetch official dependency artifacts with `lake exe cache get`. The proof itself is rebuilt from scratch. Run `tectonic main.tex` to export the PDF. No supplementary numerical program is required.

Actual compilation logs, standard axiom checks, source hashes, PDF inspection, author self-review and a separate delegated-agent review are in `verification/`. No external independent review is claimed.
