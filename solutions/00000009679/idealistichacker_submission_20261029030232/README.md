# Disproof of Conjecture 00000009679

For the standard analytic definition of a cusp form, the conjecture's first
universal clause is false. Let `tau = sqrt(2) + i`. This is an algebraic point
in the upper half-plane, and it lies in no quadratic subfield of the complex
numbers. The level-one weight-12 discriminant `Delta = eta^24` is a genuine
cusp form and has no zero in the upper half-plane. Therefore

`f = (Delta(tau))^(-1) * Delta`

is a fixed nonzero cusp form with `f(tau) = 1`, an algebraic value.

This uses evaluation rescaling, not Fourier or Hecke normalization. Neither
source language requires algebraic Fourier coefficients or a specified
normalization. We do not claim that this example satisfies either additional
restriction, overturns a theorem of Nesterenko, or separately resolves the
later CM-period/class-number clause. Refuting the necessary first clause is
sufficient to refute the conjunction as written.

## Artifacts and Formal Objects

- `main.tex` and its actually compiled `main.pdf` give the mathematical proof.
- `source.md` preserves the complete bilingual official Git blob.
- `statement-alignment.md` maps source conditions to actual Lean objects.
- `lean4/AlgebraicPoint.lean` proves the algebraic point and its exclusion from
  every degree-two `IntermediateField Rat Complex`, using actual rational
  linear independence and dimension, rather than assuming a non-CM label.
- `lean4/NormalizedCusp.lean` uses actual `CuspForm.discriminant`, its
  nonvanishing theorem, complex scalar action, the algebraic value one and
  the negation of an explicit necessary universal clause.
- `lean4/Check.lean` prints the types and axiom closures of all 19 public
  theorems. The two mathematical modules also contain the same module-local
  read-only type/axiom queries; no executable evaluation is used.
- `reproduce.py` checks the source, fixed configuration and physical
  dependencies, clears only this project's build directory, builds `Main`,
  replays both mathematical sources and `Main`, and audits every advertised
  theorem's actual type and axioms. `tests/test_reproduce.py` tests both
  rejection gates and the supplementary exact arithmetic diagnostics.

## Reproduction

Requires Python 3.10+, Git, and an independently installed Lean 4.33.1 toolchain.
Mathlib is fixed at `0df444a360eaa60ab8c11dca51a86af692955474`; the eight
additional dependencies are fixed in `lean4/lake-manifest.json`. From this
submission directory, with a checkout containing the original conjecture:

```text
python reproduce.py --lake <Lean4.33.1-lake> --repo <source-checkout>
python -m unittest discover -s tests -v
```

The default path runs `lake update` only after checking the exact manifest.
For existing complete, physical dependency checkouts use:

```text
python reproduce.py --lake <Lean4.33.1-lake> --repo <source-checkout> --skip-update
```

This offline mode does not fetch or prepare dependencies. It requires all nine
checkouts to own ordinary `.git` directories, verifies exact origins, HEADs,
index/tree equality and every tracked byte before and after the run, and
rejects junctions, redirected Git metadata and real symbolic links. On Windows
three precisely pinned inert Git-link blobs may be ordinary exact link-text
files, never real links; their benchmark/document paths are not executed.
`--preflight-only` is a static check, not a build or publication approval.

For a deterministic PDF rebuild, run Tectonic 0.15.0 on `main.tex` with the
process environment variable `SOURCE_DATE_EPOCH=0`. The submitted PDF and
the release coordinator use that same epoch; PDF comparison is byte-for-byte,
not a comparison that ignores dates or trailer IDs.

Only the submission's own `lean4/.lake/build` is cleaned. Installed compiler,
dependency binaries and caches remain trust inputs. This is not a full
dependency rebuild, an empty-machine bootstrap, a Linux/hosted-CI result or
an OS sandbox claim. Do not run unreviewed third-party build scripts.

## Mathematical and Verification Boundaries

The main negation is `ModularValue9679.level_one_value_assertion_false`; the
explicit witness is `ModularValue9679.actual_counterexample`. Imaginary
quadratic subfields are represented by actual degree-two intermediate fields
with a nonreal element. The stronger field-exclusion theorem covers every
degree-two intermediate field, so it does not rely on choosing just `Q(i)`.
The usual number-field terminology is explained and reviewed mathematically;
no general Lean classification of all number-field embeddings is advertised.

The rational symbolic quotient-algebra checks in Python verify a quartic
identity, a coefficient minor and bounded rational-complex inverses. They do
not evaluate the discriminant's infinite product or certify transcendence;
the actual point, field, cusp-form and universal-negation arguments are Lean
theorems. Allowed axiom closures are only `propext`, `Classical.choice` and
`Quot.sound` (or empty).

AI-assisted mathematics, implementation and review for `idealistichacker`.
Separate AI review is not human expert endorsement. Shared toolchain/cache
correlation is disclosed. Publication is not organizer acceptance, priority,
ranking, a score or an award. Organizer conjectures and metadata are unchanged.
