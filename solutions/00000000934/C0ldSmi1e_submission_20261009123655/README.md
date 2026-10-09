# Conjecture 00000000934 — complete mathematical core

The result is a proof in complex-valued L¹(R/Z) with normalized Haar/Lebesgue measure. The concrete sequence is f₀=0 and fₙ(x)=exp(2πinx)/n for n≥1. The formalization proves unconditional norm convergence after every infinite scalar sign choice, and failure of absolute norm convergence under every permutation; it additionally allows every complex unit phase.

- `Solution.lean`: complete mathematics; main theorem `Conjecture934.conjecture`, stronger theorem `Conjecture934.strengthened_conjecture`.
- `PROOF.md`: self-contained proof, exact conventions, source-to-theorem correspondence.
- `Audit.lean`: all-owned-declaration and full transitive dependency audit.
- `verify.sh`: reproducible build, fresh source replay with warnings as errors, and audit.
- `check_inputs_and_pins.py`: input SHA256 and nine pinned dependency revision checks, with tracked-source cleanliness.
- `VERIFICATION.md`: exact outcomes and failed-then-resolved attempts.
- `PROVENANCE.md`: all consulted materials and independent-author boundaries.
- `logs/`: final evidence and retained historical diagnostics; historical source snapshots are `.txt` files, not active Lean modules.
- `CORE-SHA256SUMS.json`: frozen inventory for downstream review. `.lake` build products and standard-library dependencies are excluded.

Use the Lean 4.19.0 toolchain named by `lean-toolchain` and dependencies at the exact revisions in `lake-manifest.json`. With `lake` in PATH, run `./verify.sh`. Alternatively set `LAKE_BIN` to an absolute path to that pinned toolchain's Lake executable. Dependencies may be installed from the manifest or supplied as an unchanged local cache. The script runs `lake build`, then independently elaborates `Solution.lean` afresh and audits the resulting module.

No numerical or experimental computation is needed for the proof. The Python program is only a provenance/pinning check. The audit is inspection tooling, not a mathematical axiom or proof-producing oracle.

This frozen core intentionally contains no LaTeX or PDF yet; those are to be produced once, downstream, from this completed and reviewed mathematics. No publication action has been taken by the author.
