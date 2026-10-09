# Record layout

`root-build/` and `root-controls/` contain the final independent runner's raw command/result records, dependency checks, exact compiled inventory, and proof-dependency closure. Generated temporary projects, dependency checkouts, and build caches are omitted. Embedded absolute paths identify the original execution locations and are not required for reproduction. Run the public scripts to generate fresh records on another machine.

`semantic-review/` contains the separate reviewer's original-first reasoning, build/audit logs, entire-report review, engineering-claim review, and final package review. `ReviewerAudit.lean` is their supplemental endpoint check; it imports the submitted `Solution` and can be run from the prepared Lean project with that directory on the import path.

`technical-summary.json` and `technical-provenance.json` describe the earlier engineering pass by the zero-fiber helper. Its named preliminary attempt directories are retained locally rather than included here. This preparatory role is not an independent semantic review. The final reproducible engineering evidence is the separate root run above.

`external-eligibility-summary.json` and the operational sections of `root-final-review.json` bind the larger locally retained public-history capture by hashes. They are summaries, not a bundled copy of that capture. `publication-gate.json` records the subsequent immediate publication check. `report-visual-review.json` binds the final source/PDF pair and both-page inspection.

`source-manifest.json` covers all inputs to the public verifier. The submission-level `SHA256SUMS.json` additionally binds the report, documentation, and included records, excluding that manifest itself. Neither manifest is a maintainer endorsement.
