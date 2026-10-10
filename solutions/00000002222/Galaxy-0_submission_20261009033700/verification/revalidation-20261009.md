# Independent revalidation on 2026-10-09 UTC

The exact live upstream conjecture matches source.md. The scope is every positive modulus n <= 1000 with the usual nonzero-zero-divisor graph. Independent mathematical and semantic review passed without source changes; all report PDF pages were visually inspected and passed.

All original submission manifest hashes passed. Running generate.py --all regenerated the 20 certificate modules byte-for-byte. independent_2222.py additionally checked all ordinary pairs and explicit annihilator witnesses. Results: 1,000 moduli; 20,782,308 color pairs; 11,044 clique pairs; 195,309 annihilator witnesses. These computations are auxiliary evidence and are not part of Lean's trust base.

The fresh official Lean 4.31.0 Linux archive has SHA256 07a633cc8d9151cbc08825ea4cdda50d4b02a2c9cb852c0131b13046f49cad7f. Its source is https://github.com/leanprover/lean4/releases/tag/v4.31.0 . A clean build is recorded in clean-build-20261009.log, including the final theorem axiom audit. No proof placeholders, native_decide, unsafe declarations or extra axioms are present.

Prior Python confirmation in historical PR #6 is credited in README.md and proof.tex/pdf. This submission supplies formal certificates and a soundness proof and makes no claim of first mathematical discovery. Local verification does not imply official competition acceptance.

## Reproduce the additional checks

From the submission directory, run:

    python3 verification/independent_2222.py .
    python3 generate.py --all
    lake clean
    bash verify.sh

The archived regeneration.json records byte equality with the original certificate modules before any build. SHA256SUMS covers the final submitted source and verification files.
