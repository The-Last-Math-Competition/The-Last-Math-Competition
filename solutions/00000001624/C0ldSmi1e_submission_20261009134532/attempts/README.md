# Honest development archive

These `.lean.txt` files preserve the exact Lean source bytes from development attempts.
They are not executable project roots and are not all claimed to compile. Numbered logs
in `../records/` record the diagnostics; final successful replay logs use `replay-` names.

| Snapshot | Corresponding log | Outcome |
|---|---|---|
| 001-initial.lean.txt | 001-initial.log | Proof elaborated; Lake manifest input-ref warning and an unnecessary-`simpa` linter warning. |
| 002-order-characterization.lean.txt | 002-order-characterization.log | Added no-gaps/order-convexity equivalence; explicit warnings-as-errors rejected the same unnecessary-`simpa` lint. |
| 003-warning-fix.lean.txt | 003-warning-fix.log | Core passed explicit warnings-as-errors. This is the frozen core. |
| 004-api-probe.lean.txt | 005-api-probe.log | Successful standard-library/runtime signature and definition inspection. |
| 005-verification-initial.lean.txt | 006-verification-initial.log | Failed: omitted explicit point argument to `interior_singleton`; one unnecessary-`simpa` lint. |
| 006-audit-api-probe.lean.txt | 007-audit-api-probe.log | Inspection included unavailable qualified API names; expected exploratory errors retained. |
| 007-verification-fix.lean.txt | 008-verification-fix.log | All eight challenge theorems passed. Final file only improves one explanatory comment about open-interval boundary endpoints. |
| 008-audit-api-probe-two.lean.txt | 009-audit-api-probe-two.log | Inspection identified underlying aliases; unavailable API probes produced exploratory errors. |
| 009-audit-initial.lean.txt | 011-audit-initial.log | Audit tooling failed on shadowing a mutable variable. Lean refused evaluation of the erroneous audit term. |
| 010-audit-shadowing-fix.lean.txt | 012-audit-shadowing-fix.log | Audit tooling failed because an imported `liftIO` resolved to the command-elaboration monad instead of the core monad. |
| 011-audit-io-fix.lean.txt | 013-audit-io-fix.log | Audit passed: 24 owned/generated and 27,632 transitive declarations, only the three permitted standard axioms. |

Logs mentioning Lean's recovery admission for an erroneous audit tool are failed
elaboration diagnostics, not accepted proof terms. No incomplete attempt is imported by
`Conjecture1624.lean` or `Verification.lean`. The final audit tool itself compiles with
warnings-as-errors and reports no admitted proof or unauthorized axiom in the audited graph.

`004-lake-build.log` and `010-lake-build-verification.log` record successful incremental
builds. `014-clean-replay-driver.log` records the first complete successful replay;
`015-final-replay-driver.log` records the next successful replay after comment and
archive-output refinements; its name predates the independent replay-hardening findings.
`017-hardened-final-replay-driver.log` and `replay-*.log` record the final hardened replay.
`016-stale-audit-test-driver.log` and `stale-audit-negative-test.*` preserve the successful
negative integration test that rejects a deliberately disabled audit. There was no abandoned mathematical proof direction:
the core gap construction elaborated on the first attempt, and the failures were lint,
API-discovery, and audit-tool implementation issues.

The two archived Python snapshots preserve the pre-hardening verification scripts:
`012-replay-before-fresh-audit.py.txt` could reuse an old PASS report if the audit
accidentally stopped producing one; `013-replay-before-input-contract.py.txt` already
fixed that issue but had not yet enforced the complete checksum key set and entire
normalized Lake manifest. Independent engineering review identified these fail-closed
validation gaps after the mathematical core was frozen. They did not alter any proof or
its axiom dependencies. The final script fixes all three gaps and is the only replay
entrypoint delivered as executable Python.
