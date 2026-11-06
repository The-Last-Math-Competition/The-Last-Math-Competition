# Independent review of TLMC 00000008872

Review completed: 2026-10-19 19:47:21 UTC.

Verdict: PASS for mathematical semantics, source-only build, all axiom/kernel checks including fresh-environment replay, and the PDF review.

## Conclusion and exact scope

The counterexample is mathematically valid under the standard finite short normal-play interpretation explicitly stated in the report. The two witnesses are the zero game and star. Both are all-small, both satisfy the source's immediate-number-options condition, both have atomic weight zero and numerical component zero, and their normal-play outcomes differ. Thus the asserted completeness fails, including on the source's narrower domain. No conclusion about the other conjuncts is needed.

The original statement does not give a formal definition of “number part.” The report discloses its interpretation as the numerical component modulo infinitesimals. On these two games that interpretation is defensible and unambiguous: they lie strictly between every positive canonical dyadic bound and its negative. The proof does not replace game equivalence by equality modulo infinitesimals, nor does it claim to refute every imaginable alternative assignment to an undefined term.

## Source verification

The original conjecture was independently fetched from its [upstream GitHub file](https://github.com/The-Last-Math-Competition/The-Last-Math-Competition/blob/main/conjectures/00000008872.md). Its Git blob is `d3dda6a52716663037d0bb0d56db233e9412f006`; computing the blob hash of `source-conjecture.md` gives exactly this value. Both English and Chinese versions were checked.

The mathematical reference was independently inspected in the [arXiv v2 text](https://arxiv.org/html/2007.03949v2), the downloaded PDF (pages 11–12), and its TeX source. Definitions 3–5 supply the far-star and atomic-weight framework. Examples 5–6 explicitly give atomic weight zero for Nim heaps. The convention for multiplying zero by up gives zero. The reference also identifies all-small games as infinitesimal. These statements agree with the report's use of the reference.

## Semantic review

### Actual games, sums, and comparisons

`Game` represents arbitrary finite game trees with finite lists of Left and Right options. It is not a two-element surrogate tailored to the witnesses. `le` is the standard recursive Conway comparison. `add` permits exactly a move in one summand. `nimHeap n` gives each player every smaller canonical heap as an option.

`AllSmall` recursively requires both players to have moves together or neither to have a move. Zero and star satisfy this. `IsNumber` uses the recursive number-game condition, with every Left option strictly below every Right option. `source_option_condition` verifies that zero and star meet the original statement's additional immediate-options condition. It is not necessary to regard star itself as a number.

`outcome_zero_heap` connects the independently recursive move evaluator with Conway comparison. `outcome_sum_nim` identifies the evaluator with the actual disjunctive sum with the canonical heap. Thus the eventual-outcome argument is about real normal play rather than an invented Boolean invariant. `distinct_outcomes` gives `(false, false)` for zero and `(true, true)` for star, so the empty context already distinguishes them.

### Numerical component

The recursively defined `tiny n` are the canonical games 1, 1/2, 1/4, and so on. `NumericalPartZero` requires both strict dyadic bounds for every natural index. `NumberParts.lean` proves these bounds by actual Conway comparisons, separately for zero and star. These are universal bounds, not numerical experiments. This establishes the common zero numerical component for the stated interpretation without identifying the games themselves.

### Why the finite-context far-star formulation is valid

The formal far-star device is not an ordinary fixed finite heap. In particular, the convention for adding two formal far stars must not be asserted of finite heaps. The final report explicitly makes this distinction.

For completeness, the bridge used here can be justified directly. Fix a finite game Y and put q_Y(n) = o(Y + *n), recording the two first-player winning statuses. When a single formal far star remains, a legal move either changes Y to one of its finitely many options while retaining far star, or replaces far star by a finite heap. Induct on Y. By induction, the first kind of move has the same winning status as its sufficiently large finite-heap approximation. For each of the two players, the existence of a winning move of the second kind is an existential statement over natural heap sizes. If it is true, it has a finite witness; if false, every finite prefix is false. A sufficiently large common threshold therefore captures both such existential statements and every option of Y. The formal one-far-star outcome equals the eventual value of q_Y(n).

Applying this fact separately to G+X and H+X shows that equality of formal far-star outcomes for every finite context X is precisely the per-context eventual equality used in `FarStarEquiv`. There is no need for a single bound uniform over all X. The convention involving two formal far stars is unused because the contexts here are finite short games and exactly one far star is added.

The formal stabilization proof is stronger than an existence claim: `outcome_stable` proves stability when n is at least `sizeOf g + 1`. Its two-bit update map is idempotent; all 16 Boolean assignments were also checked independently during this review. `star_heap` proves the exact contextual star/Nim-toggle identity directly from moves. Toggle changes the index by one, so `sizeOf x + 2` suffices in `star_farStarEquiv_zero`.

For all-small games, the definition's zero fiber is therefore represented correctly by `HasAtomicWeightZero`. It is not a function stipulated to return zero on zero and star. The project intentionally does not formalize a total atomic-weight function or the entire existence-and-uniqueness theory for arbitrary weights; its zero-fiber semantics and the named reference suffice for this counterexample.

### Restricted domain and final theorem

During review, a scope issue was identified and corrected: negating completeness over all all-small games would not by itself negate completeness restricted to games whose immediate options are numbers. The final `CompleteSourceZeroFiber` includes both restrictions, and `not_completeSourceZeroFiber` directly negates that exact restricted universal using the same witnesses. This resolves the domain issue without enlarging or changing the source's domain.

## Mechanical verification

The final source-only build is isolated in a fresh temporary directory. Only the eight `.lean` modules, `lakefile.lean`, and `lean-toolchain` were copied; no submitted `.olean`, `.lake`, build products, or external package cache was used. The project imports only Lean's bundled `Std` and its own modules. The toolchain is Lean 4.31.0, commit `68218e876d2a38b1985b8590fff244a83c321783`; the bundled Lake reports version `5.0.0-src+68218e8`.

Results:

- Fresh `lake build`: PASS, all 10 jobs.
- All eight modules checked with `-DwarningAsError=true`: PASS.
- Axiom audit of all 90 explicitly named project definitions, inductives, and theorems: PASS. The only dependencies found are `propext`, `Classical.choice`, and `Quot.sound`. This is not an “axiom-free” claim.
- Source inspection for proof holes, custom axioms, `native_decide`, unsafe declarations, and metaprogramming bypasses: PASS.
- Kernel replay of all eight newly built project modules using `leanchecker`: PASS.
- Supplemental fresh-environment `leanchecker --fresh -v Main`, replaying the final `Main` module and its entire imported dependency closure: PASS (exit 0).

The final main counterexample, the far-star equivalence, and both completeness-negation theorems use only the three standard foundational axioms above. The original transient `StarHeap` build error was repaired by restoring the needed pair-projection reduction; the corrected source is included in these clean checks.

Exact commands, complete logs, the generated 90-declaration audit source, and source hashes are in `verification/independent-final/`. The authoritative build log is `clean-build.log`; the warning, axiom, replay, and integrity logs are separate. Hashes of the completed logs, generated audit source, and reproduction script are recorded in `completed-evidence-sha256.txt`. Earlier development logs are not evidence for the final source.

## PDF verification

The final frozen `solution.tex` was rebuilt independently using the provided cloud PDF build script, then all four pages were independently rendered at 110 dpi and inspected. Every page is legible; displayed formulas, logical quantifiers, references, theorem names, and commands render correctly. No missing glyphs, clipping, overlap, or lost text was observed. The final PDF contains four pages, including the added restricted-domain theorem discussion. TeX reports one cosmetic 0.67682 pt overfull line; visual inspection shows no clipping, and it does not affect the proof or readability.

The final renderings are `verification/independent-render/page-1.png` through `page-4.png`.

## Exact final artifact hashes

```text
ac2812f7d12d0db6e6770102fd12ef2d9958dbfdfd3c20bcfad5c5bf89424168  solution.tex
1ac08d37a03b165359ec09471f2a2e8eefb958b8f2220d4c47343bb131bfb426  solution.pdf
54987b84358c787edf9b22d0bb9a557ef4477df309be5a008539b0643db44168  source-conjecture.md
f234f44933ee83de4f3952b4a77d5e8336da32a08a022f79c6e589895bec6294  lean/Core.lean
2e5388846f8cc497c0f93f784f1554ffc1c9989bdeaf8aab71b79ac0b2edb333  lean/Main.lean
65e3325d89f7099f4b2af6224e8415ec059069281320c8e14ac294a34acab446  lean/NumberParts.lean
3910c4917051f5ea9da51aa2fb2be4f16e559fc2ac73664a80f07c86167ea6a2  lean/OutcomeBridge.lean
af29898942704af30e7c9b310eda4e09b0f4595e7827eb9131c80042d9949c2f  lean/Stabilization.lean
4126859d62f8ebbf1512f2a7aaf7f38d91c949416b8ed411792e015db8bc2d07  lean/StarHeap.lean
bac7bf4869fc2814f128cc4e7a62119b3cd91b2a122d6d13f2a1a1276128c0fb  lean/Sums.lean
dcce3390408dc508a37502e6f083c0a0dc64faea0c066f07c7a58e5195fd3d2a  lean/Toggle.lean
18c775e9e16b9d1994319bb3dbbd1ec0193e625a3eef07b1b8a5c6f760a14aa0  lean/lakefile.lean
efac0b94923b2d8b6840cd35be9177ad0fc5ab2332f4f4311c98712cee92fdee  lean/lean-toolchain
```

## Remaining limitations

The report's declared finite short-game universe and disclosed numerical-component interpretation are essential scope statements, not hidden hypotheses. There is no claim to formalize arbitrary infinite-game contexts, all nonzero atomic weights, or the remaining spectrum, sum, and temperature assertions. No mathematical or formal-proof blocker remains for the first completeness assertion within the stated scope.
