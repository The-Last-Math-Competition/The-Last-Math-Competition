# Verification record

The frozen mathematical source and unchanged bilingual original were checked against the entire report. The proof author, a separate semantic reviewer, a technical verifier, and the coordinating contributor performed the roles described below. These are contributor-side checks, not a repository-maintainer review.

## Exact mathematical scope

`solutionCount k` is `Cardinal.mk` of the subtype of pairs `(x,y) : ℤ × ℤ` satisfying `x^3 - 2*y^3 = k`. It does not replace an infinite count by zero. `MaximumIsTwelve` includes both a universal upper bound and attainment. `Conjecture` is this assertion conjoined with finiteness of the parameters attaining 12. Refuting this necessary conjunction refutes the full source assertion irrespective of its further unspecified torsion/enumeration clause. The nonzero-parameter formulation has a separate endpoint.

The reviewer independently derived the scaling obstruction after reading the original, before reading the submitted proof. They rebuilt the proof, expanded both endpoints to the original integer solution subtypes in a separate `ReviewerAudit.lean`, inspected the source-authored axiom dependencies, and read the whole report. Both PDF pages were extracted, rendered, and visually checked. See `verification/semantic-review/` for the records and the final package review.

## Build and proof audit

The coordinating contributor independently ran the public scripts against the frozen inputs on Lean 4.19.0. The nine dependency revisions and clean tracked state were checked before and after each run. A new project was fully built; all three Lean modules were replayed with `-DwarningAsError=true`. Inputs were rehashed after execution. The raw command records and results are in `verification/root-build/` and `verification/root-controls/`.

The resulting inventory contains **32 owned compiled constants**: **27 safe mathematical declarations** and **5 exact compiler-generated execution definitions**. The safe roots' transitive closure follows both types and values, including theorem proof bodies and imported intermediates: **10,899 constants**, **zero unsafe proof dependencies**, and only `propext`, `Classical.choice`, and `Quot.sound` as foundational axioms. The mathematical source has no admitted proof, custom axiom, or native decision shortcut.

Lean generates five unsafe execution helpers when compiling the frozen source. They are explicitly named in `verify.py` and `Audit.lean`, bound to the source hash, and matched against the complete inventory. One execution helper uses Lean's `lcProof` erasure artifact. This is allowed only in these exact runtime definitions; it is forbidden in every safe mathematical/proof dependency. There is no blanket compiler-name exception. Every owned axiom declaration and unsafe placeholder is rejected, including one bearing an allowlisted name. The inventory and proof closure are included; the record does not claim that the compiled environment contains no unsafe execution definitions.

## Verification controls

All **25 unit tests** passed. All **10 compiled adversarial fixtures** first compiled successfully and were then rejected for the intended audit diagnostic:

1. An authored custom axiom outside the expected namespace.
2. An authored unsafe definition outside the expected namespace.
3. An unsafe definition with a compiler-looking name.
4. An axiom using an exactly allowlisted compiler name.
5. An admitted proof, also rejected by strict source replay.
6. A hidden imported axiom in a proof value.
7. A hidden imported axiom in a type.
8. A hidden imported admitted proof.
9. A hidden imported unsafe proof dependency.
10. A hidden imported `lcProof` dependency.

An additional revision-mismatch control rejected a deliberately incorrect expected Mathlib revision; the real checkout was not modified. Two temporary negative fixtures intentionally use unchecked declaration insertion to ensure the audit detects invalid dependencies hidden behind an imported theorem. The generated Lean fixture modules are confined to temporary test projects; their source strings also appear in `test_verify.py` and recorded fixture descriptions. They are not part of `Solution.lean`, `Inspect.lean`, or the public `Audit.lean` module. Expected audit failures are test successes only after successful fixture compilation and a matching diagnostic.

No auxiliary numerical search or unverified computation is needed for the theorem. The Python code checks the proof package and its controls; it does not establish the mathematical result. Reproduction instructions are in `README.md`.

## Authorship and review provenance

The proof author received the exact original, repository rules, and standard libraries. A fresh-context helper proved the zero-fiber lemma. After independently deriving and announcing the scaling argument, the author used the agent inventory to check capacity and accidentally saw unrelated earlier task summaries, one containing unrelated mathematical details. No prior solution or strategy for conjecture 1735 was exposed or used, and no linked prior proof was opened. The causal order and limitations are preserved in `verification/author-access-provenance.txt`; we do not claim zero historical exposure of every kind.

The zero-fiber helper later assembled the engineering verifier. Consequently, that engineering pass is not described as independent mathematical review. The separate semantic reviewer began with fresh context and the original problem before seeing the author source. The coordinating contributor separately reviewed the final code and reran the full portable verification and controls. Engineering infrastructure was adapted from earlier verification tooling only after this mathematical source was frozen; no prior mathematical argument was imported into it.

## Report and eligibility

The included report was compiled successfully with the built-in LaTeX compiler and exported with an existing Tectonic installation using cached resources. The final matching PDF has two pages; both were inspected for content, legibility, clipping, and pagination. `verification/report-visual-review.json` binds the exact source and PDF hashes.

Public eligibility was checked against the exact original, current bilingual contribution rules, metadata, current submissions and feedback, and observed public reference history. The frozen operational check covered 2,047 distinct current or previously observed public tips; no competing submission was found for this problem. Its compact evidence summary is included, with hashes binding the retained local capture. Unknown private or unobserved deleted material is outside that public check. An immediate publication-state check is recorded separately before submission.

Only this personal submission folder is included in the pull request. The conjecture, repository rules, leaderboard, metadata, and other contributors' materials are unchanged. The accompanying verification records report local validation, not acceptance by a maintainer.
