# Conjecture 00000002212: a counterexample

**Result:** false. The numerical semigroups `H = <3,4,5>` and `K = <3,7,8>` have the same minimum generator, 3, but their catenary degrees are respectively 3 and 5. Both are minimally three-generated.

The proof is self-contained. It uses the standard catenary distance between factorizations, proves global chain bounds by a terminating normal-form argument, and obtains sharp lower bounds from the fibers of 9 in H and 15 in K. No bounded computational search is used to infer a global invariant.

## Files and validation

- `proof.tex` and `proof.pdf`: mathematical report.
- `Counterexample.lean`: complete Lean formalization, importing only `Std`.
- `lean-toolchain`, `lakefile.toml`, `lake-manifest.json`: reproducible Lean 4.24.0 project.
- `verification.txt`: compilation result and axiom audit.

Run from this directory:

```text
lake build
lake env lean Counterexample.lean
```

The final theorems are `CatenaryCounterexample.counterexample` and `CatenaryCounterexample.conjecture_false`. The latter formally negates the existence of any function of the minimum generator that gives the catenary degree of every admissible triple; it is stronger than merely ruling out an explicit formula.

`Admissible` includes positivity, strict ordering, unique one-letter factorizations of each generator, and an explicit conductor beyond which every natural number is represented. `member_zero` and `member_add` verify the submonoid properties. `normalise` and `normalise_h` establish unrestricted global upper bounds by induction on the total number of factors other than 3. The definitions `distance`, `Chain`, `Bound`, and `CatenaryDegree` implement the usual catenary invariant itself.

The conjecture's parenthetical description as a graph diameter is interpreted in the standard catenary sense: the least distance threshold connecting every factorization fiber, not ordinary unweighted graph diameter.

## Earlier rejected submission

[PR #245, reviewer comment](https://github.com/The-Last-Math-Competition/The-Last-Math-Competition/pull/245#issuecomment-5965086293) was closed as invalid. Its examples used redundant generators, including `25 = 5*5` and `35 = 5*7`, so they were not minimally three-generated. Its Lean development did not define the catenary degree, and finite stability windows and the stated generic Betti argument did not prove global upper bounds.

This submission addresses those issues directly: both displayed triples are minimal; the standard catenary degree is defined; and all factorization fibers are covered by a proved terminating normalization, not a finite test window. The previous rejection does not constitute a solution of this conjecture.

Author: `asfigh665`. Date: 2026-10-15.
