# Author verification and semantic self-review

## Final verified mathematical content

The frozen core is `Conjecture1624.lean`, SHA-256
`f2135c4b339236755e8b6fd6dd23e7685d7831dbdbad3f2d9aaf924f5e4a7487`.
It contains three definitions and ten named theorems. `Verification.lean` contributes
eight separate challenge theorems; Lean generated three additional proof helpers across
the two modules. Every one of these 24 owned/generated declarations is included in the
audit, not merely the final two theorems.

The full dependency traversal contains **27,632 declarations**. Its only axioms are
`propext`, `Classical.choice`, and `Quot.sound`. There are no unauthorized axioms, unsafe
dependencies, or partial dependencies. The audit separately applies Lean's standard
`collectAxioms` to every owned/generated declaration, and prints explicit axiom reports
for all ten named core theorems. The full import record covers **3,430 modules**.

The final clean replay removes the owned build directory, builds both proof roots, and
runs the core, challenge suite, and audit with warnings treated as errors. Actual exit
codes and logs are in `records/replay-result.json` and `records/replay-*.log`; all final
commands must have exit code zero and the summary status must be `PASS`.

The negative replay in `records/stale-audit-negative-test.json` deliberately replaces
the audit with a Lean file that compiles successfully but produces no audit report, after
seeding an old PASS report. Its expected outcome is a failed replay: exit code 1 with
“Audit did not create a new regular dependency report.” The challenge passed, and the
stale report was removed. This negative test is expected to fail at the replay level;
that failure confirms the safeguard and is not a failed mathematical proof.

The source checksum manifest is restricted to exactly the five original keys with
exactly the original verified digests. The entire working Lake manifest must equal the
source manifest after only its top-level package name changes to `conjecture1624`.
All package revisions and tracked-source cleanliness are checked. Both compressed large
JSON archives have zero gzip timestamps and decompress to the content hashes recorded
in the final replay summary.

## Definition and coverage challenges

1. A positive-measure closed interval is gapless. Its exterior half-lines do not create
   internal spectral gaps.
2. A singleton is closed, has empty interior and no gaps, but measure zero. Positive
   measure/nontriviality therefore cannot simply be omitted from the main obstruction.
3. The two-band spectrum [0,1] ∪ [2,3] has the gap (1,2).
4. The component through 3/2 is exactly that open interval, with boundary endpoints 1,2.
5. The smaller omitted interval (5/4,7/4) is not a full gap; endpoint conditions matter.
6. The two-band spectrum contains a whole neighborhood of energy 1/2 while possessing
   a gap elsewhere. A statement about one reference energy is a different claim.
7. The punctured real line has no open-interval gaps but is not order convex. The
   closedness hypothesis in the characterization is substantive.
8. The universal potential theorem still rules out the source conjunction when both
   extra predicates are always true. No special potential model limits the disproof.

## Author's semantic self-review

- The statement being negated is the literal existence claim with all of its geometric
  requirements, in both source languages. Neither source text was changed.
- “Cantor” uses compactness, perfection, and nowhere density, with no measure-zero clause.
  The argument applies more generally than that definition and therefore does not depend
  on adding an exotic restriction to Cantor sets.
- Positive Lebesgue measure is used only to obtain two distinct points. Closedness gives
  endpoint membership for the supremum and infimum; empty interior supplies a missing
  point strictly between the initial two points. Each of these steps is formalized.
- The produced interval has finite endpoints, positive length, endpoints in the spectrum,
  empty intersection with the spectrum, and a proved equality to the entire complementary
  connected component. It is a genuine internal gap under the standard definition.
- The operator-independent lift quantifies over every potential type and real spectrum
  assignment. Unused quasiperiodic/singular-measure predicates remain completely
  unrestricted, so the formalization cannot succeed merely by selecting a narrow model.
- The real-spectrum and global internal-gap reading is stated explicitly. The proof does
  not purport to settle an unstated meaning involving a selected energy or a different
  specialized use of “gapless.” No such qualifier appears in the supplied bilingual text.
- Lean compilation and the dependency audit support the formal mathematics; they do not
  by themselves certify the natural-language mapping. That mapping is separately argued
  in `REPORT.md` and `SOURCE-MAPPING.md`.

## Limits and retained history

The pinned compiled standard library was reused and fingerprinted, not freshly rebuilt
from its source. The mathematical proof has no numerical approximation step and no
external mathematical search or imported problem solution. Development snapshots and
failed compiler/audit-tool diagnostics are preserved as plain archival text and are not
claimed to compile. The final build imports none of those failed attempts.

This package does not certify publication eligibility, competing-submission status, final
repository placement, or a PDF review. The parent workflow is responsible for those
operations and for independent review of the completed author package.
