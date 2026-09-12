# Disproof of Conjecture 00000005400

**Verdict: FALSE.**

> **Conjecture (00000005400).** *Definition: Orbit distribution and period counting are two layers.
> Conjecture: There exist two maps with identical orbit distribution limits but different periodic
> point counts, and the separation is realized by an explicit conjugate pair with the same measure
> but different periods.*

The conjecture asserts, in its own words, that two layers can be separated — identical orbit
distribution yet different periodic point counts — and that the separation is *realized by an
explicit conjugate pair*. Both halves of this assertion are broken by elementary identities of
discrete dynamics, and the witness objects demanded by the second half **cannot exist at all**.

## Layer 1 — Identity I: orbit distribution determines periodic point count

Let `X` be a finite set and `f : X → X`. A point `x` is *periodic* if `f^k x = x` for some `k ≥ 1`;
its *period* is the least such `k`. The periodic points of `f` decompose `X`'s dynamics into
disjoint periodic orbits (cycles). Writing `N_l(f)` for the number of periodic orbits of `f` of
length exactly `l`, each such orbit contributes exactly `l` periodic points, and periodic points
belong to exactly one orbit. Therefore

    P(f) = Σ_{l ≥ 1} l · N_l(f).

So the map `f ↦ (N_1(f), N_2(f), N_3(f), …)` — the orbit distribution by length — **determines**
the periodic point count. "Identical orbit distribution but different periodic point counts" is
self-contradictory under the natural discrete reading.

**Verified by exhaustive enumeration** (`reproduce.py`, part B): over all `4^4 = 256` self-maps of
`{0,1,2,3}`, `P(f) = Σ l·N_l(f)` holds in all 256 cases, and among the 11 distinct orbit profiles
there is **no** profile realized by two different periodic counts. (Restricted to `S₄`, the 5
cycle types all give `P = 4`, as every point of a permutation is periodic.)

## Layer 2 — Identity II: conjugacy preserves pointwise periods

If `τ` is a bijection and `g = τ ∘ f ∘ τ⁻¹`, then for every `k ≥ 1` and every `x`,

    g^k(τ x) = (τ ∘ f ∘ τ⁻¹)^k(τ x) = τ(f^k x),

by induction on `k` (the `τ⁻¹`/`τ` telescopes). Since `τ` is injective, `g^k(τ x) = τ x` iff
`f^k x = x`. Hence `period_g(τ x) = period_f(x)` pointwise: **period is a conjugacy invariant.**
A "conjugate pair with different periods" is therefore not merely hard to find — its defining
description is *unsatisfiable*. The witness objects the conjecture demands are logically impossible.

**Verified by exhaustive enumeration** (`reproduce.py`, part A): for all
`(τ, f, x) ∈ S₄ × S₄ × {0,1,2,3}` — `24 × 24 × 4 = 2304` triples —
`period(τfτ⁻¹)(τx) = period(f)(x)`, with **0 violations out of 2304**.

Concrete illustration (`f = (0 1)(2 3)`, `τ = (1 2 3)`, `g = τfτ⁻¹`):

| x | period_f(x) | τ(x) | period_g(τ(x)) |
|---|-------------|------|----------------|
| 0 | 2           | 0    | 2              |
| 1 | 2           | 2    | 2              |
| 2 | 2           | 3    | 2              |
| 3 | 2           | 1    | 2              |

## Machine verification (Lean 4, zero axioms)

`lean4/Main.lean` formalizes both identities over the 4-point set with **no `sorry` and no axioms**
(audit: `#print axioms` prints `axioms — [none]` for every theorem):

* `conj_preserves_period : ∀ (τ : Fin 24) (f : Fin 256) (x : Fin 4), period (conjugate (permAt τ)
  (ofW f)) (applyP (permAt τ) x) = period (ofW f) x` — Identity II, decided by exhaustive
  evaluation over `24 × 256 × 4 = 24576` configurations (`τ` ranging over all 24 permutations of
  the 4-point set, `f` over **all 256 self-maps**, far beyond what the conjecture needs).
* `count_from_profile_sum : ∀ w : Idx256, periodicCount (ofW w) = (orbitProfile (ofW w)).sum` —
  Identity I as a computable bridge, decided over all 256 self-maps.
* `profile_det_count : ∀ f g : Idx256, orbitProfile (ofW f) = orbitProfile (ofW g) →
  periodicCount (ofW f) = periodicCount (ofW g)` — Identity I's consequence, proved by rewriting
  with the bridge lemma (no enumeration in this step).
* `permAtTable_eq` — kernel-checked certificate that `permAt` enumerates exactly the 24
  bijections of `permVecs`, in order.
* `refute : ¬ ∃ (τ : Fin 24) (f : Fin 256) (x : Fin 4), period (conjugate (permAt τ) (ofW f))
  (applyP (permAt τ) x) ≠ period (ofW f) x` — the conjecture's existential (a conjugate pair
  with a pointwise period difference; `IsConjugateVia τ f g` forces `g = τfτ⁻¹`, so the pair is
  determined by `(τ, f)`), derived from `conj_preserves_period` by pure logic. The equivalent
  Bool search `conjWitnessExists` is separately kernel-checked to be `false`
  (`conjWitnessExists_false`).

`lean4/Check.lean` re-checks the enumeration, the refutation, and prints the axiom audit for each
theorem — every theorem reports `does not depend on any axioms`, i.e. **not even `propext` or
`Quot.sound`** (Lean's two default axioms) is used anywhere; all definitions live in the
axiom-free Bool/Nat-computable fragment of core Lean. Reproduce with
`cd lean4 && lake build && lake env lean Check.lean`.

## Scope and boundary

We refute the conjecture in its literal discrete reading, where "orbit distribution" is the
orbit-length distribution of a map on a set and "conjugate pair" means exact conjugacy
`g = τfτ⁻¹`. In that reading both layers fail: Layer 1 by Identity I (the two counted quantities
are not independent — one is a function of the other), and Layer 2 by Identity II (the claimed
separating witnesses do not exist).

If "orbit distribution limits" is instead meant as a measure-theoretic/asymptotic notion for
infinite systems, the first half may become meaningful for *non-conjugate* pairs sharing an
invariant measure; but the second half then contradicts the first: exact conjugacy preserves the
number of points of each exact period for every `n` (Identity II does not use finiteness), so a
conjugate pair can never realize a difference in periodic point counts. Under every reading, the
conjunction the conjecture asserts is false; we exhibit the failure in the clean finite setting
where everything is decidable and fully machine-checked.

## Package contents

* `README.md` — this file.
* `main.tex` — formal write-up (definitions, both identities with proofs, enumeration tables).
* `build/main.pdf`, `build/log.txt` — compiled PDF and build log.
* `reproduce.py` — standalone Python 3 script (no dependencies, no absolute paths); `python3
  reproduce.py` re-runs the 2304-triple conjugacy audit and the 256-map profile/count audit.
* `lean4/` — zero-axiom Lean 4 project (`lakefile.toml`, `lean-toolchain v4.33.1`, `Main.lean`,
  `Check.lean`, `README.md`).
