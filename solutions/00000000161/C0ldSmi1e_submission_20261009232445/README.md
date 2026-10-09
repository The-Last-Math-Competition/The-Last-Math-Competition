# Disproof of conjecture 00000000161

For every fixed positive real C, every prime divisor of the order of every matrix in GL_4(F_p) is at most p²+p+1. Once p ≥ 3C, this is at most p³/C. The event in the conjecture is therefore empty, and its uniform probability tends to zero instead of one.

The argument covers every possible positive value of poly(4), and even every positive denominator depending only on dimension. The existential positive-polynomial convention is explicit in `OriginalClaim`; the stronger arbitrary-C theorem removes dependence on the unspecified polynomial. Both versions of the original are preserved in `conjecture.md`.

## Formal result

`Conjecture161.conjecture_false : ¬ Conjecture161.OriginalClaim`

The proof uses Mathlib's actual general linear group over ZMod p, actual multiplicative element order, the formal group-cardinality formula and Lagrange's theorem. The probability is the ratio of actual event and sample-space cardinalities; the denominator is positive, and the prime-indexed limit is nonvacuous. No matrix sampling or auxiliary numerical computation is needed.

## Reproduce

Use Lean 4.19.0 with Mathlib v4.19.0 and the exact dependency revisions in `lean/lake-manifest.json`.

```sh
cd lean
lake exe cache get
python3 verify.py
```

The verifier checks version/dependency pins, rebuilds this project's generated objects, replays the Lake configuration and all three project Lean source files with warnings as errors, and prints all 14 theorem types and transitive axiom dependencies. It writes `verification.log` and generated build/cache files without modifying Lean sources. With compiled dependencies already present, the first command is unnecessary.

`proof.tex` and `proof.pdf` contain the matching complete report. `lean/AUTHOR_NOTES.txt` gives derivation, source correspondence, toolchain details, and the disclosure of the fresh arithmetic helper. Verification records describe local and independent internal checks; maintainer acceptance remains a separate decision.

This is an AI-assisted contribution by C0ldSmi1e. Changes are confined to this personal submission folder.

The extended independent audit is in `verification/engineering/`. After provisioning the Lean project, run from this submission folder:

```sh
python3 verification/engineering/replay_extended.py --project-root lean --output-dir /tmp/conjecture161-audit
```

Choose a fresh output directory. This additionally audits all 29 logical declarations and their full dependency closure. `VERIFICATION.md` explains the recorded checks and their limits.
