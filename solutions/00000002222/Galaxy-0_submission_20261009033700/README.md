# Conjecture 00000002222

For every positive n <= 1000, the nonzero-zero-divisor graph of Z/nZ has chromatic number equal to its clique number. Every modulus has a kernel-checked proper coloring and a clique of matching size.

## Graph semantics

Vertices are nonzero residues annihilating some nonzero residue. Distinct vertices are adjacent exactly when their product is zero modulo n. Zero and units are excluded. The graph is empty for n = 1 or a prime, so both invariants are zero.

Basic.lean proves the vertex/gcd equivalence, the reliability of the gcd-compressed independence checks, and the inequality between every clique size and every coloring size. EqualChromaticClique states attained common optimality, including universal lower bounds for all colorings and upper bounds for all cliques. It does not merely equate two algorithm outputs.

## Build

Pinned toolchain: Lean 4.31.0. Only Std; no Mathlib or network downloads.

    bash verify.sh

The script compiles the 20 certificate modules one at a time, then executes the full default lake build. For an independently clean verification, first run lake clean. A bare lake build also works but may compile several large certificate modules simultaneously. The serial script is recommended on machines with modest RAM.

The final theorem is TLMC2222.conjecture2222, covering all positive n <= 1000. Expected foundational axioms: propext, Classical.choice, and Quot.sound.

## Reproducibility

    python3 generate.py --all
    bash verify.sh

The Python program deterministically regenerates the certificate files and checks its arithmetic assertions. The Lean proof trusts none of the Python output: every certificate is established with decide, and the checker soundness theorem derives the actual graph-invariant assertion.

Files Cert00.lean through Cert19.lean cover 50 consecutive moduli each. Basic.lean contains all general arguments; Main.lean combines the ranges. proof.tex and proof.pdf contain the full mathematical report. source.md preserves the exact bilingual conjecture. verification/ contains actual build and validation records.

## Earlier computational evidence

Historical PR #6 reported Python confirmation over the 831 composite moduli but explicitly did not package this conjecture as a submission. This submission adds a full Lean-checked proof and independent certificate construction.
https://github.com/The-Last-Math-Competition/The-Last-Math-Competition/pull/6
