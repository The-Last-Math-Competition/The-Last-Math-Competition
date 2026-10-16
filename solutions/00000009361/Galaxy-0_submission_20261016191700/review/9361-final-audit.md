# Independent final audit — TLMC 00000009361

Date: 2026-10-16, 19:15 UTC
Verdict: PASS. The frozen mathematical proof, Lean certificate and three-page PDF are mutually consistent and suitable for submission, subject to separate eligibility and duplicate checks.

## Source fidelity and mathematical interpretation

Read the current bilingual source through the GitHub connector. The exact statement prefix in source.md matches Git blob 3c1e3568c9aa81b24440aa69a23149d953e1b4d4; the file then adds a clearly identified provenance footer.

The source is interpreted using positional exchangeability of a random permutation of distinct ordered labels. This is explicitly stated in the PDF and README, and is the conventional meaning appropriate to record indicators. Positional invariance acts transitively on the permutation sample space and therefore implies uniformity. No independent-entry assumption is smuggled in. The text correctly distinguishes conjugation invariance and correctly identifies the independent Bernoulli variables as the positionwise record indicators, not the total record count itself.

Verified the insertion/deletion bijection, strict-order preservation, final-record criterion, exact pattern recurrence, all-pattern product formula, empty case, deterministic first record, probability normalization and generating-function consequence. The proof is valid for every n, not only the sizes tested by Python.

## Formal semantic review

Read all proof modules and their theorem interfaces:

- Permutations.lean proves validity equivalent to List.Perm (List.range n), actual enumeration completeness and absence of duplicates, rise/drop inverse identities with their correct side conditions, strict order preservation, and factorial cardinality.
- RecordSemantics.lean defines a genuine left-to-right scan, proves its relation to reverse storage, establishes the record extension rule, and proves the chronological permutation enumeration complete and duplicate-free.
- RecordsCount.lean proves the recurrence by counting actual valid permutations and all insertion ranks; proves the exact chronological joint-pattern count; and derives its rational uniform probability as the Bernoulli product. Reversed flag indexing correctly assigns chronological position k parameter 1/k. The denominator is nonzero by factorial positivity.
- Main.lean accurately identifies the principal interfaces and explicitly states the remaining elementary exchangeability/probability interpretation.
- Audit.lean audits the relevant sample-space, semantic, counting and probability entry points.

The full chain from actual permutations to chronological records to exact joint counts and normalized rational joint probabilities is proved. It is not an unconnected rank-code sample-space surrogate. The finite probability ratio is formalized; general probability-library exchangeability and independence predicates are not claimed. The PDF supplies the short conventional interpretation transparently.

## Independent clean verification

Copied only source, configuration, verification script and Python test files from the frozen directory into a separate clean audit workspace, leaving the frozen directory unchanged. Ran the supplied VERIFY.sh with installed Lean 4.31.0 and bundled Std. Results:

- Fresh build of Permutations, RecordSemantics, RecordsCount, Main and Audit: PASS.
- Warning-as-error rechecking of all four principal modules: PASS.
- Independent leanchecker kernel replay of all four principal modules: PASS.
- Axiom audit: only propext, Classical.choice and Quot.sound.
- Independent chronological Python enumeration for n=0,...,8: all 511 Boolean patterns across these sizes PASS.

No downloads or installations were used. Full reproducibility output is in 9361-final-verification.log.

## Final document and packaging review

Read the final main.tex, README.md, Main.lean, Audit.lean and source.md. Independently rendered the frozen main.pdf and visually inspected all three pages:

1. Statement, exact count, exchangeability convention and bijection: correct and legible.
2. Record recurrence, uniformity, joint probability and generating function: correct and legible.
3. Formalization/trust boundary and source provenance: accurate and legible.

No clipped equations, missing glyphs, overlapping content, or overflowing theorem identifiers were found. The PDF hash matches the announced frozen version. The README accurately distinguishes formal and handwritten parts and calls for a fresh eligibility check before publication. This audit verifies mathematical and artifact quality, not publication eligibility or authorization.

## Frozen SHA-256 hashes

- Permutations.lean: dde3868261915e58391971a8beefd1fbad89a001b81a35bd2c00c53f1f1d9903
- RecordSemantics.lean: cd71629c2aac5120fa3d5239cd69a0978271bc6772873a32f7cbab746e48e96d
- RecordsCount.lean: 69e9a86d0531d95e7e1d70ec8006c258107d68056d8c22c094467344c95f2266
- Main.lean: 20aeba4b708aee4ab236fe1e560a6bb74fcd008cda47c759b5491c90738a8239
- Audit.lean: 9316fa2dc89431470773082cec48f4a7be75bb3fe4f709d593f4519ec0374fc4
- main.tex: a93a1e326e1d7b842551ebd445555d30ab21b02060a11140eede63db42ef7db9
- main.pdf: 8703056a57b4c0b14082940fc45e36f42bad5834e8d440eafceb99347d3abb27
- source.md: 84321fb8c162fbee39eb93d04cc12aec3977f464c74dca81408bcc5a9221ca6b
- README.md: 51f1e7c4acb70efc35257ab0cd8a5aafdae035f02165408cadbc7b7de447421b
