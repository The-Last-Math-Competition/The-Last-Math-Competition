# Portable verification

Install Python 3.9 or newer, Git, and Lean's standard elan/Lake tooling, with
`lake` on `PATH`. The included `lean-toolchain` selects Lean 4.19.0.

From this `lean` directory, obtain the stock dependencies and their optional
official build cache, then run:

```sh
lake exe cache get
python3 verify.py
```

The verifier uses only Python's standard library. It checks the exact five
proof/configuration file hashes, the complete authored Lean source inventory,
and all nine locked dependency revisions and tracked-source cleanliness. It
removes only this project's generated `.lake/build` directory, runs the full
`lake build`, and replays both proof and audit sources with warnings treated
as errors. A generated strict type audit checks the complete expected output
for all twelve theorem types, including their quantified hypotheses and
universes. All twelve axiom dependency lines must match exactly; only
`propext`, `Classical.choice`, and `Quot.sound` are expected.

A scoped token scan of authored Lean code excludes comments and strings and
rejects proof placeholders, custom axioms, native decision shortcuts, unsafe
declarations, and metaprogramming/trust bypass constructs. This scan supplements
the frozen source hashes and Lean's kernel checks; it is not a general parser
or a replacement for proof checking.

The script prints `PASS` only after every check succeeds; any failed check
returns a nonzero exit status. Full command logs and the machine-readable
verdict are written under `.lake/verification/`. The existing project build
cache is deliberately regenerated on every run. Stock dependency caches may
be reused; the script does not rebuild all of Mathlib. A change to any pinned
proof/configuration file requires a fresh review and a deliberate update of
the verifier's expected hashes and, where appropriate, type outputs.

No auxiliary numerical computation is needed. These checks establish
reproducibility and kernel validation of the stated formal propositions.
Whether those propositions resolve the original conjecture requires the
separate semantic review.

