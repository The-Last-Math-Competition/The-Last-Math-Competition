# 9778 — final independent code and semantic cross-review

**Verdict: PASS within the explicit scope approved by the parent. No defect requiring a frozen-source change was found.** This is a complete mathematical disproof plus a checked conditional analytic core and genuine pointwise integral identities. The actual L² spectral identification is an external substantive mathematical bridge, not claimed to be reconstructed in Lean. The parent explicitly approved that boundary and will supply/review the full operator-theoretic argument in the paper.

Reviewer: graph agent, separate from the quantum author. No subagent was used. No author file, frozen source, or shared progress file was changed. This report is the only new file for the final review.

## Frozen material and checks

Read the complete final `round5/drafts/00000009778/lean/Main.lean`, the exact bilingual source, the completed `round14/quantum/9778-proof-and-review.md`, `9778-status.json`, the actual strict log, the verifier source and log, and the recording script. The earlier independently checked primary reference and semantic analysis are recorded in `9778-initial-review.md`.

The quantum author explicitly confirmed Main frozen at:

`b77533cd819fc46d67762256ad07000b22299cb8e99d551fbc3ceb2b91b66e86`.

I independently recomputed that hash and matched it to the status record. The recorded strict, full Lake build, and verifier exit codes are all zero, with durations 15.468 s, 16.282 s, and 0.468 s. The actual strict log contains all eight expected result audits, each depending only on `propext`, `Classical.choice`, and `Quot.sound`. The verifier reports 33,600 exact algebra checks. No parent fresh-build step is represented as having been performed by this reviewer.

## 1. Positive square root of the actual Gram formula

**PASS.** `gram_formula_positive_root` takes both n≥1 and s≥0 as explicit hypotheses. The first implies n−1/2>0 and 2n−1≠0. Together with π>0, this proves the reference expression is nonnegative. The use of `sq_eq_sq₀` therefore selects the correct nonnegative root rather than allowing the negative root of the squared identity.

The algebraic target is exactly

    s = 1/[π(n−1/2)] = 2/[π(2n−1)].

The input squared identity is 4/((2n−1)²π²). Thus there is no confusion between singular values of V and those of the positive Gram operator V*V, and no missing factor of two or square root. The final two Gram-spectrum theorems repeat nonnegativity and the squared identity for every n≥1, exactly the appropriate conditional inputs from the actual spectral theorem.

## 2. General offsets, poles, and integer renumbering

**PASS.** `reference_second_coefficient` allows every real a and proves the scaled limit −a/π. This is valid even when the totalized formula has a pole at some finite natural index: the proof chooses an integer N strictly larger than max(0,−a), and explicitly proves n≠0 and n+a≠0 for all n≥N before its field algebra. No finite exceptional denominator is silently inverted.

`sequence_second_coefficient` requires only eventual equality with that reference formula. Consequently finite initial values cannot affect the result. Nonzero a is required only in `no_odd_expansion_of_exact_reference`, where it is genuinely necessary: a=0 gives the exact leading term and would not yield a contradiction.

`half_integer_offset_ne_zero` proves (k:ℝ)−1/2≠0 for every k:ℤ by reducing a putative equality to 2k=1 in the integers. It does not accidentally quantify only nonnegative shifts. `integer_reindex_still_no_odd` then handles every sequence eventually having the correctly shifted formula. The statement is conditional on that eventual formula; it does not pretend to define natural-number indexing by potentially truncated negative subtraction.

The zero-based cosine modes use frequency π(m+1/2), whereas the final spectral hypotheses use the one-based index n. These agree under n=m+1. A zero-based singular-value list corresponds to offset +1/2, and the one-based list to −1/2. Both nonzero offsets are covered. The theorem treats ordinary integer reindexing, not a silent half-integer renaming of the asymptotic variable.

## 3. The third-order odd condition is actually necessary

**PASS.** `OddExpansionThroughThree` says there exists a real c such that

    n³[s_n − 1/(πn) − c/n³] → 0.

This is precisely the usual finite Poincaré truncation through the next odd inverse power, with an o(n^−3) remainder. Any complete absolute odd-only expansion beginning with 1/(πn) has this necessary condition. It is not asserted to be equivalent to a whole infinite expansion.

`odd_expansion_forces_zero_second` uses the exact eventual identity

    n²[s_n−1/(πn)]
      = (1/n)·n³[s_n−1/(πn)−c/n³] + c/n,

valid for n≠0, and proves both terms tend to zero. This correctly uses third-order information. It does not make the invalid inference from only s_n−1/(πn)=o(n^−1).

The nonzero reference limit and this forced zero limit contradict uniqueness of limits in ℝ. The final exact coefficient is simplified correctly to 1/(2π). Coefficients c are unrestricted real numbers, so the contradiction is stronger than one limited to Bernoulli/rational coefficient prescriptions. Refuting this necessary parity condition suffices without formalizing a full infinite asymptotic-series API.

The completed author report also correctly distinguishes the false odd-only clause from the true existence of an unrestricted geometric inverse-power expansion. It does not claim that complete asymptotic expansions fail to exist.

## 4. n=0 is harmless totalization

**PASS.** The final Gram conditions and square-root theorem start at n≥1. Conversion to the reference sequence is obtained only eventually, using n≥1. All divisions and cancellations in the generic asymptotic proofs are made only after eventual nonzero-denominator hypotheses have been established.

The values of the auxiliary sequence, reference formula, and odd-condition expression at n=0 may be arbitrary totalized real expressions. They are never identified with an actual zeroth member of the one-based singular-value list and do not enter any limiting argument.

## 5. Genuine integral identities and their quantifiers

**PASS in the advertised pointwise scope.** `volterra` is the actual interval integral from 0 to x on real-valued functions, and `backwardIntegral` is the actual interval integral from x to 1. `genuine_volterra_cosine` and `genuine_gram_cosine` quantify every natural cosine mode and every real x, not merely finitely many sample points or an abstract supplied eigenvector.

For these continuous trigonometric functions the identities hold for all real x with the oriented interval-integral convention, so the unrestricted x quantifier is valid. Restricting to x∈[0,1] gives the intended operator-mode identities. The half-integer frequency is strictly positive and its endpoint cosine is proved zero; these facts justify the divisions and backward-integration boundary term. The two-integral composition therefore has the correct cosine eigenvalue 1/frequency².

No general linear-map structure on all possibly nonintegrable functions is claimed, and the file does not identify its pointwise functions with L² equivalence classes. `cosineMode_nonzero` proves an actual point value is one; it is not falsely used as a complete formal proof of L² eigenvector nonzeroness or completeness.

## 6. Actual operator bridge and the approved formal boundary

The completed author report now supplies the missing substantive mathematics: the triangle indicator is Hilbert–Schmidt; Fubini identifies the Hilbert adjoint; the Gram kernel is 1−max(s,t); an L² eigenvector is upgraded via its canonical representative before using the classical ODE; the mixed boundary conditions are f'(0)=0 and f(1)=0; positivity, the compact self-adjoint spectral theorem, eigenspace classification, trivial kernel, and monotone ordering yield the complete singular-value sequence. I read that argument and found no reversed boundary condition or incomplete-eigenfunction inference.

The final Lean source does not assert that these Hilbert-space steps have been formalized. `referenceFormula` is honestly named and the final theorem explicitly assumes the exact Gram spectral identity for a nonnegative sequence. The pointwise mode identities are supplementary checked analysis, not a substitute for spectral exhaustion and ordering. This accurately implements the boundary the parent approved after the initial review.

The paper should retain that distinction and the indexing normalization. With those disclosures, no unresolved source-semantic, square-root, offset, remainder-order, or quantifier issue blocks the result. Proceed to the parent's fresh independent verification and paper/PDF review without changing the frozen Main on this review's account.
