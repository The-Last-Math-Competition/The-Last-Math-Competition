# Disproof of conjecture 00000007788

For independent points sampled uniformly from the solid unit disk, the normalized expected missing area is at least `1 / (4 * (N + 1))`. Consequently its quadratic normalization diverges. This disproves the conjecture's dimension-two ball assertion and hence the original conjunction.

- `proof.tex` and `proof.pdf`: complete matching three-page mathematical report.
- `lean/`: standalone Lean 4.19.0 / Mathlib v4.19.0 project, exact dependency pins, source hashes, portable verifier and full author verification logs.
- `verification/`: the exact bilingual source and contribution rules, independent review records, final compilation record and eligibility record.

The formalization proves the actual product-uniform law, finite convex-hull volume, measurability, integrability, expected-volume correspondence, lower bound and asymptotic contradiction. No simulations or numerical certificates are needed.

After preparing the pinned dependencies and their standard caches, place Lean 4.19.0 on PATH and run `python3 verify.py` from `lean/`. The script rebuilds the authored project, replays all four Lean files with warnings treated as errors, and audits all 40 named declarations using only standard logical axioms. The Lean README and mathematical notes preserve the independent author's handoff provenance; their references to a stage before report preparation describe that earlier handoff.

Verification and independent review are local evidence. Maintainer acceptance is a separate decision.
