# Independent core mathematical review — conjecture 00000000934

**Verdict: PASS_CORE_MATHEMATICS. No mathematical or formal-scope finding.**

The frozen core proves the complete existential assertion under the conventional complex-valued, normed-space interpretation already accepted by the independent source review. The result is not restricted to a finite set of sign choices or to a particular ordering. This receipt does not approve any later LaTeX/PDF, engineering package, eligibility check, or release action.

## Exact inputs and isolation

The reviewed source is `/private/tmp/tlmc934-author/frozen-core`. Its `CORE-SHA256SUMS.json` has SHA-256 `41f401cdaea862da9247638deb6da15ded9ab350b13710ce7b71273ae8f6ff3e`. Before reading or executing the core, all 43 listed file hashes were checked, with no extra source files or missing listed files. An independent private copy was then made at `/private/tmp/tlmc934-independent-math-review/core`. All 43 original and copied files were checked again after replay and remained byte-identical. The reviewer added only separate inspection/check files and private build dependencies; no author's source or proof was repaired.

Principal identities:

| Input | SHA-256 |
|---|---|
| `Solution.lean` | `c519a1bba9351c813496d043ef8db4dd4ce3d287f4f5c69a715d84730d4e92e9` |
| `PROOF.md` | `5c8ee0a75af97682e91e2ddef3b178855f45031a271b2ddef4d58235f6d7ea8e` |
| `Audit.lean` | `1f55dc744e1c4020973949d5043f5cfd8bdc49929191a939945df5de16746555` |
| Exact bilingual original | `efa0ad90c2a2d6e560019106dbb313192078fcd6769972eabc53c179a283c52a` |
| Clean input manifest | `1b6ce2a1de00707fe55bf3fba767f834d139b546ffbb005d30b191eb502a4da6` |
| Lake manifest | `e878dc305e653df9abe0d98cba7c1423804555f529d4a82700fd8de019b8b70c` |

The original also has Git blob SHA-1 `1ef0b578222bd95a8f601b753e4b263169b4f83a`, matching the earlier source-only assessment. The original and both rule files in `/private/tmp/tlmc934-author-input` were read fully and independently matched to their manifest.

## Mathematical statement and actual ambient space

The actual theorem has no section assumptions or unproved instance arguments. It produces one sequence `f : ℕ → Lp ℂ 1 μ`, where `μ` is `AddCircle.haarAddCircle` on `AddCircle (1 : ℝ)`. That circle is the additive quotient of ℝ by the integer multiples of 1, hence ℝ/ℤ. The imported measure is the normalized additive Haar measure, with actual `IsAddHaarMeasure` and `IsProbabilityMeasure` instances. The source's `measure_eq_volume` proves agreement with the standard circumference-one volume.

`Lp` is the finite-Lp-norm subgroup of `AEEqFun`, and `AEEqFun` is the quotient of almost-everywhere strongly measurable functions by almost-everywhere equality. The `L1_norm_integral` declaration has the actual type `∀ f : L1, ‖f‖ = ∫ x, ‖f x‖ ∂μ`. Thus neither the space nor the norm has been replaced by a sequence model, a chosen representative topology, or an artificially defined norm.

The main conjunction is exactly:

1. `Summable f`;
2. for every `ε : ℕ → ℂ` satisfying `∀ n, ε n = 1 ∨ ε n = -1`, `Summable (fun n => ε n • f n)`;
3. for every `π : Equiv.Perm ℕ`, `¬ Summable (fun n => ‖f (π n)‖)`.

Printing the actual `HasSum` and `Summable` definitions confirmed the finite-subset-net interpretation, in the topology of this normed `Lp` space. The separate `phase_unconditional_norm` statement also exports convergence of the norms of finite-subset-sum errors. `phase_permutation_norm` places the limit existential before the universal permutation, so every permutation of any fixed phase-changed series has the same limit. The phase may change the limit, as it should.

The sign predicate allows every infinite sign choice without computability, finite-support, or eventual-constancy restrictions. The stronger theorem allows all complex unit phases. A permutation is an actual equivalence ℕ ≃ ℕ. Absolute convergence is convergence of the real nonnegative norm series. `phase_norm_partial_sums_diverge` additionally establishes divergence of the ordinary reordered norm partial sums to +∞, avoiding any confusion between ordinary and unconditional scalar summability.

The final Orlicz parenthetical is retained as descriptive attribution. Neither the original nor the mathematical core specifies an independent endpoint theorem. No such theorem or additional hypothesis has been imported. The explicitly stated complex scalar convention is within the conventional source scope; no separate real-valued theorem is claimed.

## Independent proof and prose correspondence assessment

Every line of the active mathematical source and `PROOF.md` was reviewed. The construction is the actual Fourier monomial class `term n = (n : ℂ)⁻¹ • fourierLp 1 (n : ℤ)`, with zero at index 0. `term_ae` and `representative_on_real` identify its almost-everywhere representative with the stated exponential. The added zero term creates no discrepancy with the positive-index presentation.

The proof correctly restricts the integer-indexed orthonormal Fourier family to the injective natural-number indexing. For each arbitrary unit-phase choice, the coefficient square norms are precisely the reciprocal-square sequence, which is summable. The imported orthogonal-family summability equivalence is a complete-space finite-subset Cauchy result, not a mere pointwise or weak-convergence result. Its hypotheses are satisfied in the actual complex L² space. The human proof's symmetric-difference norm identity and square-series tail estimate describe this same argument. The library's Fourier orthogonality proof uses translation by a half-period to negate a nonzero character, as the prose states.

The transfer to L¹ uses the genuine inclusion of almost-everywhere classes and the probability-space bound \(\|g\|_1\le\|g\|_2\). The two uses of choice are benign and fully constrained:

- `inclusionLinear_exists` explicitly constructs the linear map `f ↦ ⟨f.1, Lp.antitone ... f.2⟩`, with addition and scalar multiplication laws proved by reflexivity. `inclusionLinear_apply` is the choice specification for every input.
- `inclusion_norm_le` substitutes this exact action, compares the actual extended Lp norms at exponents 1 and 2 on a probability space, and converts to real norms using finiteness of the L² norm.
- `inclusion_exists` explicitly constructs `inclusionLinear.mkContinuous 1` using that bound. `inclusion_apply` specifies the action of the chosen continuous map for every input. Combining the apply equations gives preservation of the underlying `AEEqFun` class and the same norm bound for the actual chosen continuous map. Reviewer-only checks of both consequences compiled without source modification.
- `inclusion_fourier` therefore identifies exactly the Fourier L² class with the corresponding Fourier L¹ class. Applying the continuous linear map to the unconditional L² sum yields precisely the claimed L¹ sequence.

The absolute-convergence obstruction is also exact. `fourier_L1_norm` uses modulus one and total measure one to prove L¹ monomial norm one; `term_norm` gives `(n : ℝ)⁻¹`, including the zero-index convention. The standard harmonic nonsummability theorem and a genuine permutation summability equivalence then give the universally quantified failure of absolute rearrangement. Unit phases preserve the norm. The human proof's harmonic blocks, reindexing explanation, and divergence conclusion agree with these formal declarations. There is no appeal to a numerical experiment or unverified asymptotic claim.

## Every owned declaration and complete dependency closure

The source has 31 explicit declarations. Both the author's audit and a separately written reviewer audit selected declarations by **defining module**, not merely by namespace, and found 36 declarations after elaboration, including all five generated helpers. The independent audit printed every actual type and body and checked every owned declaration's full `Lean.collectAxioms` result. It also separately traversed constant references in both types and values, including opaque theorem bodies, until closure.

The complete named inventory and printed types/bodies are retained in the logs. Its semantic groups cover all 31 explicit declarations:

- Actual spaces/measure: `Circle`, `μ`, `L1`, `L2`, `measure_eq_volume`, `L1_norm_integral`.
- Fully specified inclusions: `inclusionLinear_exists`, `inclusionLinear`, `inclusionLinear_apply`, `inclusion_norm_le`, `inclusion_exists`, `inclusion`, `inclusion_apply`, `inclusion_fourier`.
- Actual witness and norms: `term`, `term_ae`, `representative_on_real`, `fourier_L1_norm`, `term_norm`.
- Unconditional, sign, phase, permutation, and absolute clauses: `phase_L2_summable`, `phase_summable`, `term_summable`, `IsSignChoice`, `sign_summable`, `no_absolute_rearrangement`, `phase_no_absolute_rearrangement`, `phase_unconditional_norm`, `phase_permutation_norm`, `phase_norm_partial_sums_diverge`.
- Closed complete existential results: `conjecture`, `strengthened_conjecture`.

The generated helpers are `L2._proof_1`, `inclusionLinear._proof_2`, `inclusionLinear._proof_3`, `phase_L2_summable._proof_4`, and `term.eq_1`, all in `Conjecture934`. Their actual bodies respectively supply the numeral instance, the standard topological additive-group instance, the exponent-monotonicity membership proof, the inverse-power identity, and the defining term equation. None is unsafe or an axiom.

**Independent result: 36 owned declarations; 30,946 transitive constants; only `propext`, `Classical.choice`, and `Quot.sound`; no owned axiom and no unsafe constant anywhere in this closure.** The entire independent closure name file is byte-identical to the author's, with SHA-256 `84d1e821e1e21444ab03587e4805a455c422f09a79c77adf2e2b072e2dbd3503`. The mathematical source contains no admission, custom axiom, `native_decide`, `unsafe`, implementation substitution, executable oracle, or option disabling checks. Audit `run_cmd`/IO code inspects metadata and is not imported by the mathematical proof or used as a proof-producing oracle.

Historical diagnostics show that earlier direct definitions created unsafe executable compiler stages. Those logs and complete snapshot differences were inspected as evidence, not instructions. The final mathematical maps have the same proved action but no such generated stages. The strict audit was not weakened in the final core; the independent audit verifies the final environment directly. Thus historical failures are not being passed off as successful final certification.

## Independent replay results

Lean reports `Lean (version 4.19.0, arm64-apple-darwin23.6.0, commit 6caaee842e94, Release)`. All nine dependency revisions and their tracked-source cleanliness passed both before and after replay. Packages were copied privately from the permitted neutral standard-library cache. The build independently rebuilt the nine missing standard-library modules, including Fourier/AddCircle, and then `Solution`.

The exact commands, working directories, durations, exit codes, and logs are in the four `commands-*.json` files. All required final checks returned exit 0:

| Check | Result |
|---|---|
| Pinned runtime version | Pass |
| Original/manifest bytes and nine pinned dependency revisions, before and after | Pass |
| `lake build` | Pass |
| `lake env lean -DwarningAsError=true lakefile.lean` | Pass |
| Fresh `Solution.lean` elaboration with `-DwarningAsError=true` and new `Solution.olean` | Pass, no diagnostics |
| Author `Audit.lean` replay with warnings as errors | Pass |
| Independent actual-type/body/axiom/closure audit with warnings as errors | Pass |
| Explicit Haar/probability, actual inclusion action/bound, and fully expanded source-shaped theorem checks | Pass, no diagnostics |

The operations of the fail-fast `verify.sh` were independently executed as individually recorded commands; the literal wrapper was read completely but not separately invoked. The Python checker, package configuration, toolchain declaration, Lake manifest, and full audit source were also read before execution.

Two **reviewer-only diagnostic attempts** required correction: an unavailable pretty-print option `pp.maxDepth`, and an unqualified `IsAddHaarMeasure` name in the additional inspection checks. Both initial logs and inspection sources are preserved. The corrected inspection files passed. These failures did not originate in, or cause any edit to, the frozen core.

## Scope, limitations, and materials consulted

The complete bilingual original, both clean operative rules, every active core source/configuration/verification/proof document, the author's retained diagnostics, and the complete historical-source differences were consulted. The 30,946-name file was mechanically compared in full, and every corresponding transitive declaration was traversed by the independent audit; this is not a claim of manually rereading 30,946 library proofs. Relevant neutral standard-library definitions/proofs were inspected for the circle and Haar measure, Fourier monomials and orthogonality, `Lp`/`AEEqFun`, exponent comparison, the L¹ integral norm, orthogonal-family summability, p-series and harmonic nonsummability, finite-subset `HasSum`, and nonnegative norm partial sums.

The trusted base includes the supplied Lean runtime and pinned neutral standard-library artifacts. Existing standard-library artifacts were reused where available; the entire nine-package library was not rebuilt from scratch. No author-private working file or author build cache was needed. No prior submission, selector/operational material, unrelated mathematics, external solution, web search, app/thread inventory, or other agent's mathematical work was consulted. No mathematical subagent or external communication was used.

This is a full review of the **frozen core mathematics**, not the later submission package. It does not certify a future LaTeX/PDF rendering, prose transcription, submission format, external eligibility, historical Orlicz attribution, or a separately formalized real-valued version. Those limits do not leave a gap in the exact complex-valued theorem reviewed here.
