# Disproof of conjecture 00000007842

## Result

The conjecture is internally inconsistent. Its universal lower bound is
`theta(G) >= 4/3`, while its claimed tree-like concentration target is either
`(log 3)/2` or `log(3/2)`. With natural logarithms both are at most1.
For epsilon1/6 the target-neighborhood event is EMPTY under the lower bound,
so its probability is0 at every graph size and cannot tend to1.

This disproves the full conjunction. It does not compute any blanket time,
identify the correct spectrum, or assert that both individual clauses are false.
It does not depend on selecting a branching model or defining tree-like graphs:
no sampling family whatsoever can satisfy both necessary numerical clauses.

## Statement and Lean alignment

- `source.md` preserves BOTH exact original language versions.
- `statement-alignment.md` records the one-way implication from the full source
  to the necessary conjunction, not a claimed equivalence.
- `lean4/Main.lean` uses actual Mathlib real logarithms, measures and limits.
  It proves both negations and explicitly substitutes the original ratio of
  expected blanket and cover time functions into any graph sampling map.
- The source-facing `ConcentratesInProbability` wrapper explicitly carries normalized
  probability laws and measurable random variables, then projects to the broader
  necessary neighborhood-mass condition.
- No stochastic-walk calculation is assumed: the contradiction holds for every
  real-valued interpretation of the stated ratio.
- Every public theorem is listed in `submission.json` and audited by
  `lean4/Check.lean`; only propext, Classical.choice and Quot.sound are allowed.

## Reproduce

Lean4.33.1; Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`.
From this directory, with that Lean release installed:

```text
python reproduce.py --repo <LastMathC-checkout> --lake <Lake-executable>
```

The default mode updates the exact Git-pinned dependencies and builds the project.
If the exact dependencies have ALREADY been materialized, offline validation is:

```text
python reproduce.py --repo <LastMathC-checkout> --lake <Lake-executable> --skip-update
```

Offline mode verifies every dependency's Git HEAD, origin and clean tracked source
before skipping updates. No machine-local path dependency is committed. A clean
project rebuild, warning-as-error source replay and full theorem dependency audit
are required in both modes. Auxiliary decimal/Fraction checks are finite numerical
regressions, not a simulation of graph walks and not the infinite proof.

Recompile `main.tex` with Tectonic0.15.0 and `SOURCE_DATE_EPOCH=0`; `main.pdf`
is the actual compiled three-page report, not a link or a renamed text file.

## Provenance and review boundary

- Upstream source commit: `9b795e7a94a6076e49a65a6489e1caf9153abd23`.
- Conjecture blob: `075b190a8cb157c3cbb46db832e7ddc4e64ada51`.
- Raw SHA-256: `09751ed8def1feb0f573fb27567c1aba7f7f43682ca4419240f03d70c1fb0c70`.
- Only this personal submission folder is proposed; conjectures, metadata,
  organizer review folders and leaderboards are untouched.

AI-assisted submission by GitHub account idealistichacker. Independent Agent
review is recorded in `review.json` when actually complete and bound to the frozen
content hash. It is internal AI review, NOT human or organizer review, upstream
acceptance, a score or an award. Maintainers retain all review/merge authority.

The concentration clause is read substantively, as asserting an actual concentrating
graph ensemble. A common sample space may be all eligible finite labelled graphs,
with each size-specific law supported on that size. We do not reinterpret an empty
universal class as an existing stochastic ensemble.
