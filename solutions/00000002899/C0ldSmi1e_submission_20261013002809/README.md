# Conjecture 00000002899: the displayed Kakeya asymptotic bound

For every dimension `d >= 2`, every fixed real `c`, and every field-size
threshold `Q`, this submission constructs an odd prime `p >= Q` and an actual
Kakeya subset of `(ZMod p)^d` whose size is less than `p^d(1-c/p)`.
The true minimum is bounded above by that set's size, so the proposed eventual
lower bound fails. The family has size `((p^2+2p-1)/2)*p^(d-2)`.

**Interpretation limit:** the original says "of type" without defining it.
This result refutes the displayed leading coefficient one with fixed `c`.
It does not refute an unspecified positive-constant `Omega(q^d)` bound,
allow `c` to grow with `q`, or claim the constructed family is optimal.
The report explains this scope against both exact original statements.

The main declarations are:

- `Conjecture2899.counterexamples_in_each_dimension`: actual counterexamples
  for arbitrary `d >= 2`, real `c`, and natural `Q`.
- `Conjecture2899.not_proposedEventualLowerBound`: explicit negation of the
  eventual bound quantified over finite fields.
- `Conjecture2899.normalized_minimum_upper_bound_in_each_dimension`: the true
  minimum divided by `q^d` is at most `1/2+1/q-1/(2*q^2)` in odd characteristic.

`IsKakeya` uses complete affine lines in every nonzero vector direction.
`minimumKakeyaSize` is the least cardinality among all actual Kakeya finsets;
attainment and comparison with every admissible set are proved separately.
Square fibers, actual set cardinalities, and arbitrarily large prime witnesses
are proved symbolically. No external numerical computation is a proof premise.

## Reproduce the Lean check

Lean 4.19.0 and all nine dependency revisions are fixed in the included
toolchain and manifest. Mathlib is v4.19.0 at
`c44e0c8ee63ca166450922a373c7409c5d26b00b`.
With the pinned toolchain and dependencies available, run from `lean/`:

```sh
lake build
lake env lean -DwarningAsError=true Conjecture2899/Geometry.lean
lake env lean -DwarningAsError=true Conjecture2899/Squares.lean
lake env lean -DwarningAsError=true Conjecture2899/Counting.lean
lake env lean -DwarningAsError=true Conjecture2899/Minimum.lean
lake env lean -DwarningAsError=true Conjecture2899/Bounds.lean
lake env lean -DwarningAsError=true Conjecture2899/Asymptotic.lean
lake env lean -DwarningAsError=true Conjecture2899/AxiomAudit.lean
lake env lean -DwarningAsError=true Conjecture2899.lean
lake env lean -DwarningAsError=true lakefile.lean
```

All eight source modules are reached by the default target, including the
axiom audit, which prints all 25 named declarations' axiom dependencies and
the critical definitions and theorem types. Preserve the lockfile revisions.
No compiled Lean output or dependency cache is distributed.

## Contents and verification

`report.tex` and `report.pdf` contain the complete mathematical argument and
formal correspondence. `conjecture.md` is the exact bilingual source.
`VERIFICATION.md` documents the independent build, strict source replay,
declaration audit, controls, identities, and explicit trust limits.
The source/configuration freeze and independent reviews are in `evidence/`.

The evidence archives preserve raw engineering receipts and author development
records, with separate SHA-256 inventories. Historical failed attempts are
retained as development history, clearly separate from the final verified
project in `lean/`; they are not additional proof premises. Historical paths
describe the original execution environment. The portable build commands above
do not require those paths.

The generic independent verifier is included unchanged. No additional numerical
program or search is required to establish the result. Run this from the
submission directory to check the packaged bytes:

```sh
shasum -a 256 -c SHA256SUMS
```

The eligibility record is a dated observation of public repository metadata;
local validation and publication are distinct from maintainer acceptance.
