# Independent author materials and boundaries

The author read `ORIGINAL.md`, `RULES.en.md`, and `RULES.zh-CN.md` completely before solving. The original source SHA256 was supplied as efa0ad90c2a2d6e560019106dbb313192078fcd6769972eabc53c179a283c52a; the supplied clean-input manifest `SHA256SUMS.json` SHA256 was 1b6ce2a1de00707fe55bf3fba767f834d139b546ffbb005d30b191eb502a4da6. This is distinct from the Lake manifest, whose SHA256 is e878dc305e653df9abe0d98cba7c1423804555f529d4a82700fd8de019b8b70c. The clean-input manifest and all five listed files are independently checked in `logs/input-and-pin-check.log`.

The only supplied task inputs were in `/private/tmp/tlmc934-author-input/`: the exact bilingual source, both rule files, lean-toolchain, lake-manifest.json, and their SHA256SUMS.json inventory. Neutral standard-library information came from `/private/tmp/tlmc-standard-library-419/` (nine pinned dependency packages in total, including Mathlib). The library root consisted of symlinks; their link metadata was observed while finding Mathlib. No target outside the explicitly allowed standard-library content was inspected. Mathlib was copied into this private project by copy-on-write before building missing library object files; the other neutral dependency directories were linked. No prior submission, selector notes, operational history, unrelated mathematics, thread/app inventory, or another agent's work was consulted. No mathematical subagent was spawned, no web search was performed, and no third-party communication or publication occurred.

The supplied Lean 4.19.0 runtime was used. Standard API probes (`#check`, `#print`, and one metadata-only `#eval` listing compiler options) inspected library definitions; no runtime/native computation was used to certify mathematics. A lookup for Lean runtime source files found those files absent and returned no contents.

The following standard-library material was actually read in full or relevant excerpts, or returned in targeted search results:

- `Mathlib/Analysis/Fourier/AddCircle.lean` (full file).
- `Mathlib/Analysis/PSeries.lean` (p-series and harmonic-series declarations/proofs).
- `Mathlib/Analysis/InnerProductSpace/Subspace.lean` (orthogonal families and square-norm summability proof).
- `Mathlib/Analysis/InnerProductSpace/Orthonormal.lean` and `l2Space.lean` (search results on restriction and orthogonal summability).
- `Mathlib/MeasureTheory/Function/LpSpace/Basic.lean`, `Indicator.lean`, and `ContinuousFunctions.lean` (a.e. quotient, norms, monotonicity, and API search results).
- `Mathlib/MeasureTheory/Function/LpSeminorm/CompareExp.lean` (the first 155 lines, containing the probability-space Lp norm comparison and monotone exponent membership).
- `Mathlib/MeasureTheory/Measure/Typeclasses/Probability.lean` (nonzero probability measure).
- `Mathlib/MeasureTheory/Integral/Bochner/Basic.lean` (integral-norm identities in search results).
- `Mathlib/Topology/Algebra/InfiniteSum/Real.lean`, `NatInt.lean`, `Basic.lean`, and `Mathlib/Analysis/Normed/Group/InfiniteSum.lean` (targeted API searches for unconditional/permuted/ordinary convergence). The exact `HasSum` and `Summable` definitions were printed by Lean.
- `Mathlib/Util/AssertNoSorry.lean`, `AssertExists.lean`, `Export.lean`, and `Mathlib/Tactic/MinImports.lean` (audit implementation examples); `Mathlib/Tactic/Core.lean` (compiler-generated-stage search result).
- Broad searches under standard `Mathlib/Analysis`, `Mathlib/MeasureTheory`, and finally `Mathlib` for relevant theorem names or audit APIs. These returned only neutral standard-library knowledge.

The author independently selected the Fourier construction. The parent supplied only the exact task, clean-context boundaries, verification requirements, and operational status. No mathematical construction or proof was received from the parent or any other agent.
