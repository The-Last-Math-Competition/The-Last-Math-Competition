# Verification and review record

This submission disproves the original conjecture's unqualified convexity assertion. A constant two-atom probability law has a genuine LDP with a proper good rate, but every finite nonnegative sublevel and the exact zero level are nonconvex. Read report.pdf and input/ORIGINAL.md together for the statement, definitions, and scope limits.

## Checks completed

- Independent mathematical review of both source languages, every proof module and the full report; all four mathematical files also compiled independently with warnings treated as errors. See evidence/independent-review.txt.
- Fresh complete Lake build against the pinned Lean 4.19.0 / Mathlib v4.19.0 project; original verify.sh executed successfully; all seven mathematical and verification Lean files replayed with warnings treated as errors.
- Exact inventory of 47 mathematical declarations and their 15,665 reachable dependencies. Only propext, Classical.choice and Quot.sound occur as axioms; no mathematical root has an unsafe dependency. Six Lean-generated runtime declarations are recorded separately and are unreachable from mathematical roots.
- Seven rejection controls cover admissions, custom axioms, native decision, unsafe declarations, unsafe proof use, altered frozen files and unlisted modules. Each was rejected as intended.
- All nine dependency repositories' source bytes and revisions checked before and after; 4,061 imported compiled modules fingerprinted. Stock compiled caches were reused explicitly; this was not a full rebuild of Lean or Mathlib.
- Native LaTeX compilation succeeded. The exported five-page PDF was rendered and every page visually inspected. Two formatting-only line-wrap repairs are independently reviewed. No mathematical text changed.

No mathematical auxiliary computation is required. All supplied build and audit programs used for verification have been executed; original failures and limitations remain recorded. Local validation does not imply maintainer acceptance.

## Reproduce and inspect evidence

VERIFICATION.md gives the full isolated-verifier command. README.md gives the ordinary Lake workflow. verification-manifest.json freezes the tested source and exact declaration inventory; SHA256SUMS.json covers the final submission files except itself.

The original command logs, dependency graphs, generated rejection controls and bootstrap sources are preserved losslessly in evidence/engineering-evidence.tar.gz. From this folder, extract with:

```sh
tar -xzf evidence/engineering-evidence.tar.gz
```

This restores verification-evidence/ and the engineering package's original PACKAGE_SHA256SUMS.json. evidence/engineering-result.json is the concise result; evidence/engineering-archive-check.json records the archive's verified contents. Source and command paths inside historical records identify the original local run; the portable project has no absolute dependency paths.

The author, independent reviewer, and PDF build records have their own evidence archives. The author's two unused generated .olean files are omitted while their hashes remain recorded. The helper's earliest failure logs had been overwritten; preserved transcript copies and fresh reproductions are explicitly labeled. The two failed engineering bootstraps and the first failed PDF export are retained as failures, not counted as successful checks.

Eligibility and observation limits are recorded in evidence/eligibility-review.json. Only this personal submission folder is changed.
