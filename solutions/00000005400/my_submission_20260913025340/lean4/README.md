# lean4 — machine verification of the disproof of 00000005400

Zero-dependency Lean 4 project (toolchain `leanprover/lean4:v4.33.1`, no
Mathlib). Every theorem is proved by kernel-checked computation (`decide`/`rfl`)
or by rewriting with such a lemma: **no `sorry`, no axioms**.

## Build and check

```sh
lake build
lake env lean Check.lean
```

`Check.lean` re-runs the enumerations, prints the concrete conjugate pair
`(f, τ, τfτ⁻¹) = ((0 1)(2 3), (1 2 3), (0 2)(1 3))`, and audits axioms; every
`#print axioms` line reports `does not depend on any axioms`.

## Contents

* `Main.lean` — the development (namespace `Tlmc5400`):
  * `Perm := Fin 4 → Fin 4`, `applyP`, `iterP`, `period` (least `k ≥ 1` with
    `f^k x = x`, search over `1..4`), `invP`, `conjugate`, `IsConjugateVia`.
  * Complete enumeration of `S₄`: `allVecs` (256 image vectors), `permVecs`
    (the 24 bijections), `permAt` (indexed access), with
    `permVecs_length : permVecs.length = 24`.
  * All 256 self-maps via the base-4 digit encoding `ofW : Fin 256 → Perm`.
  * Orbit machinery: `onCycle`, `periodicPoints`, `periodicCount`,
    `sameCycle`, `cycleRep`, `cycleLen`, `orbitProfile` (sorted cycle lengths).
  * Theorems:
    * `count_from_profile_sum : ∀ w : Fin 256, periodicCount (ofW w) =
      (orbitProfile (ofW w)).sum` — Identity I bridge, `decide` over all 256
      self-maps;
    * `profile_det_count : ∀ f g : Fin 256, orbitProfile (ofW f) =
      orbitProfile (ofW g) → periodicCount (ofW f) = periodicCount (ofW g)` —
      by rewriting with the bridge;
    * `conj_preserves_period : ∀ (τ : Fin 24) (f : Fin 256) (x : Fin 4),
      period (conjugate (permAt τ) (ofW f)) (applyP (permAt τ) x) =
      period (ofW f) x` — Identity II, `decide` over 24576 configurations;
    * `permAtTable_eq` — kernel-checked: `permAt` enumerates exactly the 24
      permutations of `permVecs`, in order;
    * `conjWitnessExists_false` — the complete-enumeration Bool search for a
      separating conjugate pair is `false` (kernel-checked);
    * `refute : ¬ ∃ (τ : Fin 24) (f : Fin 256) (x : Fin 4), period (conjugate
      (permAt τ) (ofW f)) (applyP (permAt τ) x) ≠ period (ofW f) x` — the
      negation of the conjecture's existential, derived from
      `conj_preserves_period` by pure logic.

  All definitions are kept in the axiom-free Bool/Nat-computable fragment of
  Lean core, so the audit reports **no axioms at all** — not even `propext` or
  `Quot.sound`.

## What is being refuted

Conjecture 00000005400 claims two maps with identical orbit distribution but
different periodic point counts, realized by a conjugate pair with different
periods. Identity I makes the first half self-contradictory (the periodic
count is a function of the profile); Identity II makes the second half's
witnesses nonexistent (period is a conjugacy invariant). See the package
`README.md` and `main.tex` for the full argument.
