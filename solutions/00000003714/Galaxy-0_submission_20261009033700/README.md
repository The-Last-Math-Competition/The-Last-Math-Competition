# Conjecture 00000003714

The minimum order of an adjacency-cospectral nonisomorphic pair of finite simple undirected graphs is five. An explicit pair is K(1,4) and C4 disjoint union K1, both with characteristic polynomial X^5 - 4 X^3 and eigenvalues -2, 0, 0, 0, 2.

## Scope

The standard adjacency-spectrum convention is used. Graphs may be disconnected, as the source imposes no connectedness condition. This is not a claim about Laplacian spectra or the minimum restricted to connected graphs.

## Verification

Pinned toolchain: Lean 4.31.0. No Mathlib or external packages.

    lake build
    python3 check_graphs.py

Main.lean imports only Std. The Lean kernel checks every graph pair on 0, 1, 2, 3, and 4 vertices; equal characteristic polynomials always have a verified bijective adjacency-preserving map. At five vertices, masks 75 and 45 have the explicitly computed polynomial and are nonisomorphic because only the latter has an isolated vertex. The determinant is computed by the Leibniz formula with exact integer coefficient arithmetic.

Main theorem: TLMC3714.conjecture3714.
Axioms: propext and Quot.sound only.
The Python script is an independent exact cross-check, not a dependency of the proof.

proof.tex and proof.pdf contain the complete argument and explain the encoding and semantic correspondence. source.md preserves the bilingual source. verification/ records the actual checks and toolchain.
