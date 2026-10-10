# Independent semantic review: conjecture 00000000302

## Verdict and review scope

**PASS on mathematical semantics, full LaTeX source review, and complete two-page PDF review.** The frozen development proves the original equality under the explicitly disclosed conventional interpretation of the source's omitted domains and quantifiers. Both sets whose dimensions are compared have actual Hausdorff dimension one. I found no mathematical gap, weakened target, replacement dimension, substituted model set, or extra hypothesis on the final theorem. The final PDF has no observed visual defect.

This review independently read the complete original bilingual statement, both rule files, the dependency/toolchain pins, every submitted definition and proof, the complete frozen argument and provenance, and the complete LaTeX source. It inspected the relevant definitions and proofs in the permitted pristine stock Mathlib. It did not use the author's build artifacts, sibling/prior solutions, selection records, repository history, PRs, app histories, or helper agents. Independent rebuilding and kernel-axiom verification are assigned to the separate engineering review and are not claimed as performed here. The author's provenance assertions are recorded as assertions, not independently certified facts about the author's historical conduct.

The source ambiguity is a disclosed limitation, not an outstanding proof defect: neither language explicitly binds `p,q` or states their domains. The reviewed interpretation is real `x`, integer `p`, and every positive natural denominator `q`, with a positive real constant uniform in both `p,q`. No claim is made about an unspecified alternative interpretation.

## Exact reviewed identities

SHA-256 values were computed directly from the permitted files.

| File | SHA-256 |
| --- | --- |
| original `conjectures/00000000302.md` | `8afbb17d3361f807602fae3ba1e9622ded8a5060a7039ee5dd33f97f10c2103b` |
| `RULES.en.md` | `200d9a783c08a5edfd1b508e6942b3b851a63c726506291f6de6a59773f1163a` |
| `RULES.zh-CN.md` | `7c5b49bb84403feea1eb14d23d48491400c7749d58db345cd317231949a9e82b` |
| `Conjecture302.lean` | `aedd718cba074730350efded0fbd45b49f1e328b28eed847854c0b01949fef1f` |
| `Audit.lean` | `bedbc63410992b36630ac77341bcc060df0c103b64c195feefbcb9837061467b` |
| `lakefile.lean` | `c26ffaa3f4917ebf9e35e5782c6182f2c45001d0be47a5ef4a552dd37c97542d` |
| `lean-toolchain` | `55e97be96000b5e9e290c9e74482e5e317861499a5540353ce845471bded8cea` |
| `lake-manifest.json` | `56f7aa9722d120b38ffe868179164054411be9398660939609cb8a0c55e48637` |
| frozen `ARGUMENT.md` | `f3ed6c18dd2dbad208b3cc6d8eb66e8cc72e8942d53c5e73d604642777c2ac76` |
| frozen `PROVENANCE.md` | `1e8f64bad779cb768400b65a3d53846f7ad40352c07eb10a2dadc95a7c8c3ba8` |
| `FROZEN_SHA256.json` | `5b000c262def26c4cd39ceb26bfcd3e6d7935b08a03d06a9e1e316cc87fb05a8` |
| historical initially reviewed `proof.tex` | `c06895def4537a30201cc138c965a599e7d9496d0d0be26bdd1ec553729f58e6` |
| final complete submission `proof.tex` | `6b0944500e6906bce652fa2e82b758d7154a140c73a7ad2fec4e3996f1660121` |
| final complete submission `proof.pdf` | `b56e6e5d8776c8b0638936859b625a0ffb3648ac862eddb1e4533acf355b9764` |

The proof and freeze-manifest digests exactly match the identities supplied to this reviewer. The pins name Lean `leanprover/lean4:v4.19.0` and Mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`; all eight transitive package pins are present in the manifest. The project files contain no custom logic or mathematical assumptions in their configuration.

The full LaTeX source reviewed is `/Users/daniel/.codex/worktrees/competition-explore/The-Last-Math-Competition/solutions/00000000302/C0ldSmi1e_submission_20261010000034/proof.tex`. The frozen mathematical source is `/private/tmp/tlmc302-proof/Conjecture302.lean`.

## Source statement and conventional interpretation

The entire English mathematical statement is:

> Definition: II_α = {ξ : ∃c > 0, |ξ − p/q| > c/q^{2+α}} (the exponent-badly-approximable set). Conjecture: dim_H(II_{1/3} ∩ II_{1/2}) = dim_H(II_{1/2}).

The Chinese mathematical content is identical; it calls this the exponent-badly-approximable set and repeats the same equality and strict inequality. Neither language adds a condition that the other omits.

`Conjecture302.II` is precisely

```lean
def II (α : ℝ) : Set ℝ :=
  {x | ∃ c : ℝ, 0 < c ∧ ∀ (p : ℤ) (q : ℕ), 0 < q →
    c / (q : ℝ) ^ (2 + α) < |x - (p : ℝ) / q|}
```

The existential quantifier precedes both universal quantifiers, so the same `c` works for all fractions. Integer numerators include negative and zero numerators. All positive denominators and unreduced representations are tested. Denominator zero is excluded by the final definition. The power is real power because both its base and exponent are real. The strict inequality is preserved exactly, merely reversing its displayed order relative to the original `>` notation. The ambient metric is the usual metric on the full real line, and no unit-interval restriction appears.

The complete final theorem type is:

```lean
Conjecture302.conjecture :
  dimH (Conjecture302.II (1 / 3) ∩ Conjecture302.II (1 / 2)) =
    dimH (Conjecture302.II (1 / 2))
```

Both numerical parameters are real numbers, inferred from `II : ℝ → Set ℝ`; thus these are real `1/3` and `1/2`, not natural-number division. Both `dimH` occurrences are Mathlib's metric Hausdorff dimension valued in `ℝ≥0∞`. The theorem has no hidden section variables, hypotheses, typeclass parameters, assumed dimension equalities, or custom axioms. Expanding `II` gives exactly the conventional quantified equality above.

## Review of every submitted definition and theorem

1. **`II`** is the original approximation predicate with the domains made explicit, as checked above. The namespace does not redefine `dimH`, `volume`, `Irrational`, or `LiouvilleWith`.

2. **`mem_II_of_not_liouvilleWith`** has hypotheses `0 < α`, `Irrational x`, and `¬LiouvilleWith (2 + α) x`, and conclusion `x ∈ II α`. Negating frequency at constant one yields eventually, for every integer numerator, `1/q^(2+α) ≤ |x-p/q|`. Irrationality supplies `x ≠ p/q`, including the harmless totalized zero-denominator case in the intermediate filter statement, so the non-equality guard in `LiouvilleWith` cannot weaken that inference. `eventually_atTop` gives a single threshold `N` uniform in the numerator. The bounded-denominator theorem supplies a single `ε > 0` valid for every integer numerator and every natural denominator at most `N`. The choice `c = min 1 ε / 2` has `c > 0`, `c < 1`, and `c < ε`. For `q ≥ N`, division by the strictly positive real power gives the required strict inequality. For positive `q < N`, natural-number positivity gives `q ≥ 1`; since `2+α > 0`, its real power is at least one. Therefore `c/q^(2+α) ≤ c < ε ≤ |x-p/q|`. Both branches cover all positive denominators. There is no erroneous minimum over infinitely many numerators: the stock separation theorem proves uniform separation from each closed lattice before taking the finite denominator bound.

3. **`ae_irrational`** has exactly `∀ᵐ x : ℝ, Irrational x`, with the default real measure being Lebesgue measure. `Irrational x` is definitionally nonmembership in the range of rational casting. That range is countable, and the stock no-atoms lemma proves its Lebesgue measure is zero. The inference therefore has the intended semantics.

4. **`ae_mem_II`** has hypothesis only `0 < α` and establishes `∀ᵐ x : ℝ, x ∈ II α`. It intersects the two almost-everywhere statements, specializes the stock approximation theorem at exponent `2+α > 2`, and applies item 2. This proves full measure for each positive parameter; it neither asserts nor requires that `II α` equal the irrational set.

5. **`dimH_eq_one_of_ae_mem`** concerns an arbitrary `s : Set ℝ`, assuming only almost-everywhere membership. Upper dimension bound follows from `s ⊆ univ` and the proved stock theorem `Real.dimH_univ`. Almost-everywhere membership gives equality of sets almost everywhere with `univ`, hence `volume s = ∞` by `measure_congr` and `Real.volume_univ`. The stock identity between one-dimensional Hausdorff measure and Lebesgue measure gives `H¹(s) = ∞`; the stock definition/API of Hausdorff dimension then gives `1 ≤ dimH s`. No measurability hypothesis is silently needed here: Mathlib's measures evaluate sets through their outer measure and `measure_congr` accepts almost-everywhere equality. Combining the bounds proves exact equality to one.

6. **`dimH_II`** applies item 5 to item 4 for any `α > 0`. It assumes no dimension fact about the approximation set.

7. **`dimH_inter_II`** assumes `α > 0` and `β > 0`, intersects the two almost-everywhere membership statements using filter conjunction, and applies item 5. The intersection is the actual set intersection of the two previously defined approximation sets. No unjustified inference about dimensions of arbitrary intersections is used.

8. **`conjecture`** applies items 6 and 7 at real parameters `1/3` and `1/2`, proving their positivity with `norm_num`, and rewrites both sides to one. It is unconditional and has precisely the complete target stated above.

`Audit.lean` imports the proof, prints the definition of `II`, checks all seven theorem types, and requests all seven axiom dependency lists. It introduces no mathematical declaration or assumption. The source contains no `sorry`, `admit`, custom `axiom`, `unsafe`, or evaluative shortcut. The separate engineering review must establish successful compilation and the actual transitive kernel-axiom output; this semantic review does not treat a source inspection as a replacement for that check.

## Stock library bridge semantics

The decisive stock source files inspected have the following hashes, relative to `/private/tmp/tlmc-standard-library-419/mathlib`:

| Mathlib source | SHA-256 |
| --- | --- |
| `Mathlib/NumberTheory/Transcendental/Liouville/LiouvilleWith.lean` | `636de6aa7c0ed83c47b110b91e3d963288fadec47046bed2ea46bc780ad2def2` |
| `Mathlib/NumberTheory/Transcendental/Liouville/Measure.lean` | `21645fff469da941e8a50b60f77ce2da0ec2d34187eb70c12416ab30d9910bc3` |
| `Mathlib/Topology/Instances/Irrational.lean` | `937c5f73b39a2f8cfef28b2baa18b27b97dc2f900e12eb448d42cf9650214cd0` |
| `Mathlib/Data/Real/Irrational.lean` | `e1f14ce6887f62d0ba4255cca6f861a7a21191db6220ccbc43bb91d96d847107` |
| `Mathlib/MeasureTheory/Measure/Typeclasses/NoAtoms.lean` | `f840a5341797290644d0bae0b916c866e7f98a6d25b3894de87341ff4c1cfdb7` |
| `Mathlib/Topology/MetricSpace/HausdorffDimension.lean` | `6c5cc878f910906404b44b67426c7e7565fdc2027c7ae60295ce64f18e967b59` |
| `Mathlib/MeasureTheory/Measure/Hausdorff.lean` | `e5776024a1266f614180d34174f9149318305327d51f3111dfaf30509d1e5fd5` |

At `LiouvilleWith.lean:47`, the predicate is literally

```lean
∃ C, ∃ᶠ n : ℕ in atTop, ∃ m : ℤ,
  x ≠ m / n ∧ |x - m / n| < C / n ^ p
```

Here `C,p,x` are real. Frequency at natural `atTop` means arbitrarily large, equivalently infinitely many, denominators. The inclusion of zero among natural numbers has no effect on frequency. At `Measure.lean:105`, `ae_not_liouvilleWith` states almost everywhere `∀ p > (2 : ℝ), ¬LiouvilleWith p x`, stronger than the fixed-exponent fact needed here. The proof passes through the nullity of the union over all exponents above two, reduces it to a countable family of translated rational-approximation limsup sets, bounds their interval measures by summable real-power series, and invokes the first Borel–Cantelli measure lemma. This is a genuine Diophantine approximation theorem, not an abstract stand-in or axiom about `II`.

At `Topology/Instances/Irrational.lean:71–86`, the separation theorem establishes that a sufficiently small real neighborhood of zero consists of lower bounds for the distances from `x` to all fractions with bounded denominator. Its proof uses closedness of the scaled integer lattice, irrational nonmembership, and a finite intersection over denominators. `.exists_gt` extracts a positive member of this neighborhood. All integer numerators are covered, not merely bounded numerators or reduced fractions.

At `Hausdorff.lean:534`, `hausdorffMeasure d` is the metric outer-measure construction from the cost `diameter^d`. The covering formula and zero-scale limit are the ordinary Hausdorff-measure construction. At `HausdorffDimension.lean:92`, `dimH` is the supremum of nonnegative exponents having infinite Hausdorff measure, and the surrounding zero/infinite-measure lemmas confirm the usual critical-exponent interpretation. `le_dimH_of_hausdorffMeasure_eq_top` at line 121 follows directly from this supremum. `dimH_mono` at line 146 is proved from measure monotonicity. `hausdorffMeasure_real` at `Hausdorff.lean:997` proves the exact real-line measure identity via the stock finite-product volume calculation. `Real.dimH_univ` at `HausdorffDimension.lean:461` is proved from the finite-dimensional real-space result, whose proof uses actual ball measures and invariance under continuous linear equivalences. None of these are assumed dimension values supplied by the submission.

## Complete argument and LaTeX claim review

The frozen `ARGUMENT.md` was read in full. Its proof is mathematically sound and agrees with the Lean development. Its explanation of the stronger stock almost-everywhere theorem versus the fixed-exponent elementary argument is accurate.

All five sections, abstract, theorem, lemma, proofs, and concluding reproduction paragraphs of `proof.tex` were read in full:

- **Abstract and main theorem:** Correctly state the stronger full-measure and dimension-one conclusions for positive parameters. “Complete argument formalized” is accurate at the mathematical level: the formal proof uses the proved stock measure theorem rather than reproducing the report's particular interval counting proof verbatim.
- **Statement/conventions:** Faithfully quotes both languages' shared formula and explicitly discloses the omitted quantifiers. The uniform constant, full real line, all positive denominators, real powers, and genuine Hausdorff dimension agree with the Lean definition.
- **Approximation lemma:** For fixed integer `m`, positive integer `K`, and positive `q`, the contributing numerators lie between `(m−K)q` and `(m+1+K)q`, so the stated upper count `(1+2K)q+1` is valid. Each interval has length `2K/q^s`, giving the displayed measure bound. Both resulting power series converge for `s>2`. The limsup exceptional sets are null by the first Borel–Cantelli lemma. Countable union over integer intervals and positive integer constants covers all real points and all real constants, since every real constant is bounded above by a positive integer. Defining the auxiliary sets without the non-equality guard only enlarges them and is harmless. All sets used in this elementary measure argument are measurable interval unions.
- **Uniform strict bound:** The same irrationality, common large-denominator threshold, finite family of closed-lattice bounds, and halved-minimum constant used in Lean are present. The report handles an empty finite denominator range and states the large-denominator condition with `max(1,N)`, so no zero-denominator ambiguity remains. Both branches prove a strict inequality with one common positive constant.
- **Dimension and intersection:** Full measure is used correctly to obtain infinite real-line measure and hence dimension at least one, while monotonicity gives at most one. The intersection step uses full measure, not a false general assertion about intersection dimension. The parameters are substituted correctly.
- **Formal correspondence:** Names and roles of all mentioned theorems are accurate; the final theorem has no extra assumptions. The stated Lean/Mathlib versions and commit agree with the input pins, and the audit source requests exactly seven theorem-type checks and seven axiom checks. Numerical computation is neither used nor needed. Statements that compiler outputs, review records, artifact hashes, and `ORIGINAL.md` accompany the final submission are packaging claims for the coordinator/engineering review to verify; they are not unproved mathematical premises.

No mathematical correction to the LaTeX or frozen argument is required. The only interpretation caveat is the source's expressly disclosed missing domains and quantifiers. This review is local independent model review and is not maintainer acceptance.

## Final source and PDF verification

The initial source was preserved at `/private/tmp/tlmc302-pdf/initial-layout/proof.tex`; its hash matches the historical source reviewed in full. A direct textual comparison with the final submission source showed exactly two layout/editorial changes: `11pt` became `10pt`, and the sentence beginning `Its theorem` was moved to a new paragraph and changed to begin `The theorem`. No mathematical formula, hypothesis, assertion, or proof step changed. The final source SHA-256 is `6b0944500e6906bce652fa2e82b758d7154a140c73a7ad2fec4e3996f1660121`.

I directly hashed and extracted all text from the final PDF at the same submission path, `proof.pdf`; it has exactly two pages and SHA-256 `b56e6e5d8776c8b0638936859b625a0ffb3648ac862eddb1e4533acf355b9764`. Its complete extracted text agrees with the reviewed final source, including all five sections, the abstract, the full theorem and lemma, every displayed estimate, the final parameter substitution, and the reproduction statements. The final compiler log contains no warning, error, overfull, or underfull message, and records two pages. This is a check of the provided log and output, not a claim that this reviewer separately reran the compiler.

Following the PDF skill's read-only visual-review workflow, I inspected both supplied full-page PNG renders. Page 1 contains the title/attribution, abstract, statement and conventions, main theorem, and complete approximation lemma/proof. Page 2 contains the complete strict-constant argument, Hausdorff-dimension argument, and formal correspondence/reproduction section. The formulas, integer/real/natural symbols, strict versus non-strict inequalities, theorem references, long Lean identifiers, and pinned commit are legible and correctly rendered. Margins, section transitions, and page numbers are consistent; no text is clipped, overlapped, missing, or replaced by a broken glyph. No visual correction is required.

| Visual evidence | SHA-256 |
| --- | --- |
| `/private/tmp/tlmc302-pdf/final/page-1.png` | `a720c2abdbf88572720c6284bffabbcaaa226f44b4784aea60ad52c9d1db76a4` |
| `/private/tmp/tlmc302-pdf/final/page-2.png` | `6b0579ef3429e662cc5ba9671348bcaa6eec3a34cfad09b71d9a125fdfbbf137` |
| `/private/tmp/tlmc302-pdf/final/proof.log` | `5273158923a3072b283fcd7bef84cab1d941c45b6394d162e079505a23ed1c60` |
