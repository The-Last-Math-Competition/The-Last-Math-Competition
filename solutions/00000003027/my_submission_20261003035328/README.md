# Disproof of conjecture `00000003027`

**Verdict: FALSE — for the Levin–Wen input category Vec_{Z/2}, the
anyon fusion rules are the representation ring of the Drinfeld double
D(Z/2) (rank 4: simples 1, e, m, ψ), NOT the Grothendieck ring of the
input category (rank 2: simples 1, x): the claimed identification fails
at the smallest input.**

## The conjecture (verbatim from `conjectures/00000003027.md`)

> Definition: String-net condensation of topological order. Conjecture:
> The excitation spectrum of string-net condensation: the fusion rules
> of anyons are the Grothendieck ring of the input category, and the
> rank of the ring is a lower bound for ground-state degeneracy.

## The counterexample: input Vec_{Z/2}

1. **The input category.** Vec_{Z/2} has two simple objects {1, x} with
   x ⊗ x = 1: its Grothendieck ring K0 = Z[x]/(x² − 1) has **rank 2**
   (classical).
2. **The anyons.** The Levin–Wen/string-net construction on Vec_{Z/2}
   produces the Drinfeld double D(Z/2), whose representation category
   Rep(D(Z/2)) ≅ Vec_{Z/2} × Vec_{Z/2} has FOUR simples
   {1, e, m, ψ} ≅ (Z/2) × (Z/2) with fusion = componentwise addition
   mod 2: e·m = ψ, e·e = 1, m·m = 1, ψ·ψ = 1 (classical: the quantum
   double of a finite abelian group G has Rep ≅ Vec_G × Vec_G).
3. **Rank 4 ≠ rank 2.** The anyon fusion ring has rank 4 (four
   pairwise-distinct simples closed under fusion — the full 4×4 fusion
   table kernel-certified), while the input Grothendieck ring has rank
   2: the fusion rules are NOT the Grothendieck ring of the input
   category, and the "rank = lower bound for ground-state degeneracy"
   clause inherits the wrong rank (the ground-state degeneracy of the
   torus for Vec_{Z/2} input is 4, consistent with rank 4 — the
   conjecture's rank-2 bound is violated by equality 4 > 2).

## Verification

* `reproduce.py` — enumerates the 4 simples, the full 16-entry fusion
  table (componentwise mod-2 addition), confirms closure and the
  pair-distinctness, and contrasts with the input ring's 2 simples.
* Lean 4 (core, v4.33.1) — `lean4/`: the fusion as componentwise mod-2
  addition on bit-pairs; the complete 16-entry table, the pairwise
  distinctness, and 4 ≠ 2. All 4 audited theorems report `does not
  depend on any axioms`. The Vec_{Z/2} → D(Z/2) string-net
  identification and the (Z/2)² structure are classical and cited
  (Levin–Wen 2005; Drinfeld double of finite abelian groups).

## Boundary

Only the displayed identification (fusion rules = input Grothendieck
ring) and its rank reading are refuted; the genuine string-net
topological order is not addressed.
