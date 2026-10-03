# Disproof of conjecture `00000003027`

**Verdict: FALSE — the anyon fusion rules are NOT the input
category's Grothendieck ring.  At the Levin–Wen input Vec_{Z/2}: the
input Grothendieck ring is Z[Z/2], rank 2 (simples {1, x}, x·x = 1),
but the anyons are the simples of the Drinfeld center
Z(Vec_{Z/2}) = Rep(D(Z/2)) — the toric code with FOUR anyons
{1, e, m, ψ}, fusion e·m = ψ and e·e = m·m = ψ·ψ = 1 (all
associativity verified): rank 4 ≠ 2.  On the torus the ground-state
degeneracy is 4 = the center's rank, not the input's rank 2 — the
conjecture attributes the wrong ring in both clauses.**

## The conjecture (verbatim from `conjectures/00000003027.md`)

> Definition: String-net condensation of topological order: the
> mathematical realization of long-range entanglement. Conjecture:
> The excitation spectrum of string-net condensation: the fusion
> rules of anyons are the Grothendieck ring of the input category,
> and the rank of the ring is a lower bound for ground-state
> degeneracy. (string-net fusion Grothendieck ring)

## The refutation

The anyons of a Levin–Wen (string-net) model built on the input
category C are the simple objects of the **Drinfeld center Z(C)** —
not of C itself.  For the smallest non-trivial input C = Vec_{Z/2}:

* **Input ring**: Vec_{Z/2} has two simple objects {1, x} with
  x ⊗ x = 1; its Grothendieck ring is the group ring Z[Z/2] of
  rank 2.
* **Anyon ring**: Z(Vec_{Z/2}) ≅ Vec_{Z/2 × Z/2} (the toric-code
  category) has four simple objects {1, e, m, ψ} with group-law
  fusion: e·e = m·m = ψ·ψ = 1 and e·m = ψ — a fusion ring of
  rank 4 (associativity verified on all 64 triples).

Rank 4 ≠ 2: the conjecture's identification "fusion rules of anyons =
Grothendieck ring of the input category" is false — the string-net
excitation spectrum is governed by the center, which roughly
doubles the input data (electric e, magnetic m, and their product ψ
appear in addition to the vacuum).  Correspondingly, on the torus
the ground-state degeneracy of this model is 4 (the toric-code
number), which is the **center's** rank; the conjecture's clause
"rank of the (input) ring is a lower bound for GSD" is true here
(2 ≤ 4) but vacuous and misattributed — the GSD is exactly the
center rank, and the identification clause on which the conjecture
rests is what fails.

## Verification

* `reproduce.py` — the C2 group law (input ring, rank 2); the
  (Z/2)² fusion table with the four toric laws and e·m = ψ;
  associativity on all 4³ = 64 triples; the rank mismatch 4 ≠ 2;
  the torus GSD = 4 = center rank.
* Lean 4 (core, v4.33.1), `lean4/` — `input_rank` (2 = 1+1),
  `rank4` (4 = 2·2), `toric_laws` (fuse 1 1 = 0, fuse 2 2 = 0,
  fuse 3 3 = 0, fuse 1 2 = 3 — the XOR group law on 2-bit codes),
  `four_simples` (pairwise distinct), `conjecture_refuted` (2 ≠ 4
  assembly).  All 5 audited theorems report
  `does not depend on any axioms`.

## Boundary

The kernel certifies the two ranks (2 and 4), the toric fusion laws
on the 2-bit XOR encoding, the pairwise distinctness of the four
simples, and the mismatch 2 ≠ 4.  The identification of the anyon
category as the Drinfeld center Z(Vec_{Z/2}) ≅ Vec_{V₄} (toric code)
is classical (Levin–Wen; Kitaev's quantum double), cited in prose
and reproduced by the script's fusion table.  The identification
clause is refuted; the lower-bound clause, read on the input rank,
holds vacuously here (2 ≤ 4) but rests on the false identification.
