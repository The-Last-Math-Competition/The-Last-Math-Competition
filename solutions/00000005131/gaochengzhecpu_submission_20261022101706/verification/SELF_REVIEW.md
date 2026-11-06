# Self-review: conjecture 00000005131

Verdict: PASS (development self-review; coordinating adversarial review pending).

Developed by a delegated AI agent with a self-review; the coordinating agent reviews it separately. No external independent review is claimed.

1. **Source reading.** Read both English and Chinese. Both define m as algebraic multiplicity and state the area exponent 2/m, while also mentioning maximal Jordan size in the response clause. The paper openly distinguishes these inconsistent readings. It claims no refutation of a consistently corrected maximal-Jordan-size formulation.
2. **Sharpness interpretation.** A scaling law means positive two-sided comparison or positive leading coefficient. Only the necessary positive lower bounds are encoded, so their negation is stronger than merely finding a smaller displacement along one path. Big-O-only interpretations are explicitly outside the result.
3. **Real objects.** The matrix is the actual zero complex 2 by 2 matrix. Matrix.charpoly is computed as X^2. Polynomial.rootMultiplicity at zero is proved equal to 2. Eigen is exactly the nonzero matrix-vector eigenvector equation, not a numerical table or surrogate invariant.
4. **All perturbations.** Budget E e asserts that every row's sum of entry norms is at most e, exactly the closed induced infinity norm ball. The proof chooses a largest coordinate of an arbitrary nonzero eigenvector and proves every perturbed eigenvalue has modulus at most e. This precludes the common invalid inference from a single scalar-perturbation path to worst-case behavior.
5. **Attainment.** Every point of the disk is realized by the actual matrix zI and nonzero vector (1,1). sharp_response proves both the global bound and exact attainment. Thus the linear response is exact.
6. **Area.** zero_area uses actual MeasureTheory.volume on complex space and Complex.volume_closedBall. The formula is an equality of the finite real Lebesgue area with pi times e squared, for every e >= 0. It is not an assumed geometric surrogate.
7. **Universal propositions.** MultiplicityResponseLaw includes actual polynomial root multiplicity. MultiplicityAreaLaw restricts to matrices with charpoly (X-C a)^n and n>0; that is a legitimate necessary subclass of the universal area assertion, with only one spectral cluster. It retains arbitrary positive constants and an entire small-parameter interval. Reparameterization epsilon=t^n preserves positive asymptotic exponents.
8. **No singular condition-number dodge.** The area contradiction is independent of a choice of left/right eigenvectors or a condition-number formula. A zero or infinite purported coefficient would cease to express the source's asserted sharp scaling and does not rescue the positive scaling claim. The example's semisimple eigenvalue has standard well-behaved perturbation behavior.
9. **Norm scope.** The formal norm is induced infinity, a standard operator norm. The paper separately proves the identical disk using the Euclidean operator norm; that observation is accurately marked paper-only. Norm equivalence preserves exponents, so no epsilon-dependent norm is used.
10. **Axiom audit.** Actual Lean warning-as-error command passed with only propext, Classical.choice, Quot.sound. No new axioms, placeholders or computation oracles are introduced. Main.lean ends with principal theorem axiom reports. Parent will perform the clean build and PDF checks.
11. **Prior work and exclusions.** Parent's complete history/source check cleared ID 5131; blocked_ids.json excludes it, and its draft directory did not exist before setup. Rejected candidates: 3539 (ordinal polynomial root interpretation unclear), 3568 (normalization/translation issue likely technicality), 5050 (classes/asymptotic semantics unclear), 5119 (spectral-angle boundary interpretation unclear). No other draft created.
12. **Remaining review target.** Main risk is source intent: the organizers may have intended m as Jordan block size despite writing algebraic multiplicity twice. The paper and PR text are explicit about this limitation and additionally refute the unqualified area clause. The mathematics and formalization do not hide that risk.


Reviewed artifact hashes:

- Main.lean: `d04f54f3c07625645bd87ab91b80b6ba3d9a2e6f8ab1ab0319b3131483c40e35`
- main.tex: `b5d8b48eb89ed2be618497a22f6238b900a1b6760ab01cad829ae4e8591a4738`
- main.pdf: `ad1e520a9f7fe822987d9e60421cbe20d889762558cbaf9725bf58eb20cd9e09`
- SOURCE.md: `c18d994ee20263259ab6d613157dc3472c71ba0965c651a34dacb33dc3dc2ed4`
