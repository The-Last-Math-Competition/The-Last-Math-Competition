# Conjecture 00000001663: disproof of the literal strengthened conjunction

The added rigidity assertion fails for any graph paired with itself: its deck is unchanged and its unlabelled unit edge-edit distance is zero. The formal target retains **both** the classical reconstruction assertion and the added rigidity assertion, and proves the negation of that conjunction. This does not settle classical Kelly–Ulam reconstruction.

Read `REPORT.md` for the exact statement, conventions, mathematical proof, and source-to-theorem map. Read `VERIFICATION.md` for actual results, pin and cache limitations, strict replay, portable source review, and rejection controls.

- Main mathematical root: `Conjecture1663.lean`.
- Independently spelled-out statement check: `Verification.lean`.
- Main theorem: `Conjecture1663.originalClaim_false`.
- Strict fresh replay: `python3 scripts/replay.py`.
- Rejection controls: `python3 scripts/negative_controls.py`.
- Final author run locator: `evidence/FINAL_RUN.json`.
- Input source copies: `source/`.
- Archived failed attempts (never imported): `archive/`.

The working package is `tlmc1663`; all nine dependency revisions are unchanged from the supplied pinned manifest. The project requires Lean 4.19.0. Only `propext`, `Classical.choice`, and `Quot.sound` occur in the audited proof dependency closure.

The author has made no submission, eligibility, independent-review, or maintainer-acceptance claim. Any LaTeX/PDF packaging and publication are handled separately.
