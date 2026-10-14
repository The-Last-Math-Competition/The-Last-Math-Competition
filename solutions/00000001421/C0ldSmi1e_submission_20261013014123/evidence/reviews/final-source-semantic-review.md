# Independent frozen-source semantic review: 00000001421

## Verdict and scope

**PASS — no semantic source correction required.** I read all eight frozen Lean modules, totaling 1,395 lines, and all three project configuration files. The source implements the approved mathematical counterexample with the required connections to the actual stochastic walk, complete character basis, characteristic polynomials, algebraic multiplicities, matrix powers, total-variation distances, least mixing times, and limits. The final certificate has no mathematical premise. Its four implication-negation corollaries concern the constructed family and, together with the verified class-membership facts, supply a counterexample to the universal sufficient direction.

This verdict is for the original statement's **explicit multiplicity/ordinary-spectral-gap criterion under standard total-variation cutoff semantics**, in both minimum-eigenvalue readings approved in phase 1. The exact interpretation limits below remain essential. It is not a claim that undefined source prose has acquired a formal meaning.

This is a complete source-semantic review. I did not perform a build or declaration-closure audit; the parent assigned those to independent work. Successful compilation and the full axiom/dependency audit remain separate release gates. The LaTeX report and PDF were not part of this frozen snapshot and have not yet been reviewed here.

## Frozen identity and independence

Reviewed source root: `1421/review-source/lean`.

I independently recomputed SHA-256 for the freeze manifest and every listed file. All hashes match. The exact manifest SHA-256 is:

`db3effdd39210ad094c0f16e0fba2f19819086aa9cee8a921208b3cf0eb055f0`.

The exact original statement SHA-256 is `7fefa10d25b135f3e825f57cabc3043c445fd51f1afb38d2a41b026438b6777a`. I used the original English/Chinese statement and rules already independently reviewed in phase 1, the finalized phase-1 plan, and my phase-1 obligations. I did not read selector material, other competition mathematics or submissions, public eligibility evidence, or author helper reviews. Generic Mathlib source was inspected to check the meanings of `AddChar`, its character count and complex basis, doubly stochastic matrices, root multiplicity, and the natural-number infimum API.

After completing my full source read, I commissioned a supplementary clean-context check limited to the original statement and `Basic`, `MixingBase`, and `Counterexample`. It independently found no hidden profile premise or cutoff-definition mismatch within the stated interpretation. This narrow check does not substitute for the full review recorded here, and did not inspect imported proof internals or run a build.

| Frozen file | Lines | SHA-256 |
|---|---:|---|
| `Conjecture1421/Basic.lean` | 78 | `5cf93d1513856529aa689fe660ec161f8ad12fc8f193a891178a7a817d0348ea` |
| `Conjecture1421/Walk.lean` | 140 | `75877bbe9bf47d4ca4fdc4da1aa15eaa9a7b248fe2fe5f08d55a055cd9c07ba6` |
| `Conjecture1421/Powers.lean` | 274 | `4c1a7c8e910ebb519820f7c32b13806e387d478ad45dc9f41780d007e5e80f45` |
| `Conjecture1421/MixingBase.lean` | 155 | `e1853bb23d25081d85a6851a232c68c7ee314671702296bc489df0dbe203249d` |
| `Conjecture1421/Spectrum.lean` | 553 | `b0b481591648e664f54598d87191cc5d4571a0125f2ac1f342d909fd026cbb94` |
| `Conjecture1421/Counterexample.lean` | 187 | `2c44e84f19dcf36d6d3e7ddc330ceb67f9584b2ad7077d18b0fba3a9d949d331` |
| `Conjecture1421/Audit.lean` | 7 | `2279ef3b2e5ab267d951e4aa085ffba8c06d4fb5d46637b7775bbd1cf705dbed` |
| `Conjecture1421.lean` | 1 | `e20f5013b67f2d4bfd7f8a50fed91e0bc9b0b8e4a5850d914c533817a1b4b483` |
| `lakefile.toml` | 14 | `45e272047ad06aaff8a151c368f50fa1ec90a244453fff1c88313dba37eaa397` |
| `lake-manifest.json` | 116 | `3b254936ad62d6f97a4699869caf076bc3416c9a9dfc41a4b925316e1dc12db8` |
| `lean-toolchain` | 1 | `55e97be96000b5e9e290c9e74482e5e317861499a5540353ce845471bded8cea` |

## 1. Actual group and stochastic walk

`Basic.lean:15–39` defines `State n = ZMod 2 × ZMod (n+4)`, the support, jump probabilities, the matrix `transition n x y = jumpLaw n (y-x)`, actual matrix-power TV distance, and the finite maximum over starting states. The probabilities and the uniform law have the correct normalization for `2(n+4)` states. The finite and nonzero modulus instances are valid for every natural `n`; there is no empty or trivial-group edge case.

`Walk.lean` proves the support cardinality, zero exclusion, symmetry, and full additive-subgroup generation. Its `jumpLaw_uniform` and `transition_uniform` identify the displayed piecewise implementation with holding probability `1/2` plus probability `1/2` distributed uniformly over the nonidentity support. The diagonal is exactly `1/2`, not merely bounded below by that number.

The source proves entrywise nonnegativity, all row sums equal to one, symmetry, membership in Mathlib's genuine doubly stochastic submonoid, and closure of that property under the actual matrix powers. It separately proves uniform mass one, nonnegativity, and stationarity. The two-step positivity proof uses the concrete intermediate state `(x.1,y.2)` and bounds its positive contribution by the full nonnegative matrix-product sum. Thus it gives actual irreducibility; positive holding also supplies the expected aperiodicity. No abstract Markov-process encoding is needed for this finite matrix walk.

`state_card` and `group_order_tendsto` prove the group sizes are `2(n+4)` and tend to infinity. Both are exposed in the final certificate, satisfying the phase-1 request to make the growing-family property explicit.

## 2. Actual characters, full spectra, and multiplicities

`Spectrum.lean:10–40` uses Mathlib's actual `AddChar` objects and constructs a proved equivalence between product-factor characters and all characters of the state group. These objects satisfy the character homomorphism laws; they are not numerical indices named “characters.” `AddChar.card_eq` is used to count the factors, and `AddChar.complexBasis` is the complete complex function-space basis consisting of their actual values.

`complexTransition` is the entrywise complexification of the already-defined real transition matrix. `character_action` proves the convolution eigenfunction identity for its actual `mulVec`. `character_toMatrix` then proves diagonalization in the complete character basis; `charpoly_eq_product` uses basis invariance to identify the actual transition matrix's characteristic polynomial. This rules out a list of eigenvalues that lacks completeness.

The resulting characteristic polynomial is

`(X−1)(X−q)(X−r)^(n+3)(X−s)^(n+3)`,

where `q=1−1/(n+4)`, `r=1/2`, and `s=1/2−1/(n+4)`. The four roots are proved real, positive, strictly ordered `1>q>r>s>0`, and exhaustive. The only character of eigenvalue one is the trivial character (`0` in Mathlib's additive notation for characters). The complete basis and polynomial establish the stationary eigenvalue's simplicity as well.

`maxNontrivialEigenvalue` and `minTransitionEigenvalue` are genuine finite extrema over all nontrivial characters. Although their definitions take real parts, the independent reality theorem eliminates any mismatch between real parts and eigenvalues. The extrema are proved to be `q` and `s`. Consequently `spectralGap`, defined as one minus the largest nontrivial eigenvalue, is the actual ordinary gap `1/(n+4)`, with positivity proved. All transition eigenvalues are positive, so no absolute-eigenvalue ordering issue arises in this family.

`minTransitionMultiplicity` is `Polynomial.rootMultiplicity` of the actual matrix's characteristic polynomial at its actual minimum nontrivial eigenvalue. Its value `n+3` follows from the full polynomial and distinctness of the roots. It is not a hard-coded multiplicity. Together with complete character diagonalization, this is the same multiplicity obtained by counting the corresponding irreducible abelian character modes.

The alternative reading is implemented equally concretely: `complexComplement = 1 - complexTransition` is the actual matrix `I-P`. The source proves its character action, diagonal matrix, full characteristic polynomial, exhaustive root classification, and nonnegative real spectrum. `complement_character_positive_iff` identifies its positive character eigenvalues with nontrivial characters. The infimum of these eigenvalues equals `spectralGap`, and every positive root of the actual complement polynomial is at least that gap. `gapModeMultiplicity` is root multiplicity in this actual complement polynomial at that gap and is proved to equal one. Thus the second interpretation is not obtained by simply renaming the transition eigenvalue or stipulating a scalar multiplicity.

The proved ratios are exactly `(n+4)(n+3)` and `n+4`, and their divergences are derived from those identifications. Full characteristic polynomials, actual extrema, actual multiplicities, and all key bridges are included in the certificate.

## 3. Actual powers and total variation

`Powers.lean` independently proves the closed formula for `transition n ^ t` by matrix induction. The auxiliary `coordKernel` is a four-dimensional family of matrices and its multiplication recurrence is proved by finite sums. `transition_pow_coord` starts from the matrix identity at time zero and uses right multiplication by the actual transition matrix. Thus the profile is a theorem about the defined stochastic process, not a replacement definition of its evolution.

The formula in `transition_pow_apply` matches the phase-1 kernel exactly. Both scalar inequalities needed to control absolute values are proved by induction, with appropriate positivity hypotheses supplied. The signs of stationary deviations are verified separately for the starting first-coordinate block and the other block, including both possibilities for equality of the second coordinates. The actual absolute-value finite sums are then evaluated.

`tvFrom_eq` proves the distance from every starting state is `1−1/(2(n+4))` at time zero and `q^t/2` thereafter. `worstTV_eq` derives the same formula for the actual finite supremum over starts. These definitions are precisely the conventional finite-state total-variation distance to the uniform stationary law, including its factor of one half.

## 4. Actual least mixing times, limits, and cutoff failure

`MixingBase.lean:13` defines `mixingTime` using the infimum of the actual TV threshold set. Its helper theorems temporarily take the profile identity as an explicit section parameter. This is legitimate modularization, not an assumption surviving the result: `verified_counterexample` supplies the proved `worstTV_eq` to every helper that uses it, including threshold nonemptiness, attainment, mixing bounds, limits, and cutoff negation.

For every positive tolerance, the source proves the threshold set nonempty before invoking `Nat.sInf_mem`. The least-time property is also proved. It therefore cannot exploit Lean's convention that the natural-number infimum of an empty set is zero. The formulas at zero and one give `t(3/4)=1`. The attained quarter threshold and Bernoulli's inequality give `t(1/4)≥(n+4)/2`; hence the actual ordinary mixing times diverge.

The window is defined with real subtraction as `t(1/4)−t(3/4)`, and is proved positive. The time/window ratio is therefore an actual threshold-width ratio without natural-number subtraction or zero-denominator artifacts. It is bounded by two and tends to one. The source proves it does not tend to infinity.

`HasTVCutoff` is a mandatory, fully defined predicate quantified over all real tolerances `0<ε<1/2`, with convergence of `t(ε)/t(1−ε)` to one. This satisfies the phase-1 correction. The source negates it using `ε=1/4`: the denominator is exactly one while the numerator diverges. Finite early-index denominator behavior at other tolerances cannot affect this contradiction. The family separately satisfies the standard prerequisite that ordinary mixing times diverge.

## 5. Closed capstones and configuration

`CounterexampleCertificate` contains the structural and asymptotic obligations, not only two unrelated scalar sequences. Its proof `verified_counterexample` constructs every field from proved source or standard generic library facts, without theorem parameters or an assumed certificate. The source supplies all the temporary `hprofile` hypotheses with `worstTV_eq`.

The four final corollaries negate the actual-family implication from either spectral-ratio divergence to either quantified TV cutoff or time/window separation. They do not pretend to formalize a universal class of all finite random walks. That is appropriate for a counterexample: the closed certificate shows this concrete family belongs to the asserted class and satisfies the antecedents, while the corollaries establish failure of the conclusions. The report must explain this witness-to-universal-refutation step rather than describe the four scalar statements in isolation.

The top-level library imports `Counterexample`. `Audit.lean` prints axioms for all five capstones but is not itself evidence of the independently required closure audit. Source inspection and a targeted textual scan found no `sorry`, `admit`, added axiom, `unsafe`, `native_decide`, implementation replacement, external code hook, or source trust option. This observation is supplementary to, and does not replace, the parent's compiled-declaration audit.

The project requests Lean `v4.19.0`, Mathlib `v4.19.0`, and warnings as errors. The dependency manifest pins Mathlib to `c44e0c8ee63ca166450922a373c7409c5d26b00b` and pins the transitive dependencies. There are no custom build scripts, path dependencies, or configuration definitions that change the mathematical objects. Actual build reproducibility remains the independent build reviewer's responsibility.

## 6. Exact interpretation limits for the report

These limits are substantive and must remain visible in the final report and submission description:

1. The source does not specify a distance or define a mixing window precisely. The implementation uses standard total variation, true least threshold times, and the quarter-to-three-quarter width, and additionally proves failure of the usual quantified TV cutoff criterion. It must not be represented as a theorem about every possible mixing metric or arbitrary window definition.
2. The source does not mathematically define “conditional spectral gap,” an associated conditioning operation, or “second-order behavior.” The implementation computes the ordinary spectral gap. It must not claim that an unspecified alternative conditional quantity was computed or that unknown additional hypotheses were disproved.
3. “Characters of the generating support” is interpreted as actual characters of the group generated by that support. Here the support is proved to generate the entire finite abelian state group. The support itself is not generally a group. In this setting the actual complex group characters are the one-dimensional irreducible abelian characters; the implementation establishes their complete spectral basis rather than introducing a categorical representation object.
4. Both plausible “minimal nontrivial eigenvalue” meanings are addressed: minimum nontrivial transition eigenvalue and smallest positive eigenvalue of `I-P`. Neither should be conflated with the other in the prose. The ratios have different values, and both diverge.
5. No general Diaconis–Saloff-Coste comparison theorem, or unspecified characterization by that name, is formalized. The result falsifies the explicit ordinary-gap numerical sufficient direction; an undefined comparison clause supplies no additional precise hypothesis that can be checked. An intended further restriction would require a clarified statement.

These limits were present in the approved phase-1 plan and are correctly retained in the source module comment. They do not conceal an omitted hypothesis of the actual theorem. Conversely, removing them from the prose would overstate what the source proves.

## Required corrections and next gate

**Required source corrections: none.** The two phase-1 drafting requirements—mandatory quantified TV cutoff and explicit group-order divergence—are both fulfilled. No dropped stochastic, spectral, character, minimum-time, or matrix-power bridge was found.

Proceed to independent build/closure verification and then full report/PDF review. Approval of this frozen source does not approve any subsequently changed bytes; source changes require a new hash record and review of the changes. Report approval must check the exact family, full proof, interpretation limits, and correspondence with this fixed formalization.
