# Problem 00000000568: the once-punctured torus has infinitely many cluster variables

This submission disproves only the explicitly printed finite formula for `N(g,1)`, at genus 1 with one interior marked point on the closed torus. The usual complete binomial sum gives 12. The complete native Markov-seed cluster-variable set is infinite. This does not interpret the unspecified general Poincaré coefficients or count the three variables in an individual cluster.

The exact surface-to-Markov-seed identification is the published geometric definition bridge in Fomin–Shapiro–Thurston, Example 4.6 and Definitions 5.1–5.2. Its Theorem 7.11 uses the plain component for a closed surface with one puncture. The report explicitly discloses that the surface topology and the general arc-complex comparison are not re-proved in Lean. They are not added as Lean axioms.

The proof constructs the true fraction field of `MvPolynomial (Fin 3) ℚ`, the exact two-triangle signed adjacency/Markov matrix, every matrix and coordinate mutation, and all finite-word reachable seeds. Every seed is proved algebraically independent and field-generating. The variable set consists of actual rational functions from all three available directions; the algebra is the actual native `ℤ`-subalgebra it generates, with coefficient-free exchange coefficients 1.

An actual alternating 0/1 path is identified with a sequence in `Localization.Away (X₀ * X₁)`. That localization has both an injective map into the ambient field and a lawful ring specialization sending all three coordinates to 1. Its actual sequence satisfies the recurrence with coefficient 3 and is strictly increasing after the first term. This proves distinct actual cluster variables and native `Set.Infinite`, excluding every finite count. There is no field evaluation at `(1,1,1)` and no infinite-type `Nat.card` fallback.

Files include the complete original bilingual source, report LaTeX/PDF, a complete pinned Lean project, raw four-gate logs, exhaustive ordinary axiom coverage, source-bound execution receipts and SHA256 manifest. The complete proof contains no `sorry`, `native_decide` or extra axioms. Organizer acceptance is pending.

From `lean/`, with Lean 4.33.0 and pinned Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`:

```sh
lean --version
lake build +Main
lake env lean -DwarningAsError=true Check.lean
lake env leanchecker --fresh Main
```

Alternatively, after `lean --version`, run `./verify.sh` for the last three commands. The audit enumerates every actual owned declaration, including generated names, and prints ordinary axiom dependencies for each. Only `propext`, `Classical.choice` and `Quot.sound` are allowed. The production job uses CPUs `[0,2]` and two Lean threads; its diagnostic timings do not establish a causal efficiency gain.
