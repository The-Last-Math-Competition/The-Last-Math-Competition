# Conjecture 00000001478: author-stage disproof

## Result and exact scope

The conjecture is false with **cone** and **polynomial map** given their ordinary mathematical meanings. A polynomial map on a cone cannot have a bounded nonsingleton image. In particular it cannot have the complex 2 × 2 × 2 nuclear-norm unit ball as its image.

Both supplied languages assert this necessary representation clause. The adjective “explicit,” the additional description through a generalized inequality involving 4 × 4 symmetric matrices, and the proposed SDP consequence cannot repair the failure of that necessary clause. The disproof does **not** assert that the nuclear norm is otherwise impossible to compute by SDP.

The original English says “the nuclear norm of a tensor is its minimal sum of rank-one tensors”; the Chinese says “张量的核范数为其秩一张量的最小和”. These are compressed descriptions: a sum of tensors alone is a tensor, so a scalar cost must be understood. We spell out the conventional nuclear/projective cost, using Euclidean norms on the complex factors. We also prove the disproof for the literal attained-minimum version of that cost, rather than relying on an unproved identification of infimum and minimum.

No affine normalization slice, bounded spectrahedron, rational map, denominator, or projective image is stated in either version. Such a change would be a different claim. The proof does not infer cone closure from the word “spectrahedral” alone: it both treats every genuine cone and separately proves closure for the ordinary homogeneous 4 × 4 positive-semidefinite linear-pencil construction.

## Exact formal statement

Let V = C² with its Euclidean norm and let T = C^(2×2×2), represented by all arrays `Fin 2 → Fin 2 → Fin 2 → ℂ`. For any finite list of factor triples L = ((a_r,b_r,c_r)) put

- A(L)_(ijk) = Σ_r (a_r)_i (b_r)_j (c_r)_k;
- c(L) = Σ_r ||a_r||₂ ||b_r||₂ ||c_r||₂;
- D(T) = { c(L) : A(L) = T };
- ν(T) = inf D(T);
- B = { T : ν(T) ≤ 1 }.

For every natural number n, every C ⊆ R^n containing 0 and closed under multiplication by every t ≥ 0, and every polynomial map P : R^n → C^(2×2×2) with arbitrary real polynomial real and imaginary coordinates,

**P(C) ≠ B.**

This is exactly `TLMC1478.conjecture00000001478_false`; it has no hypotheses other than the quantified cone and polynomial-map data inside the negated existential. The stronger source class is intentional: ruling out all cones rules out every spectrahedral cone, whatever extra generalized-inequality description is imposed.

The separately proved theorem `minimumNuclearBall_not_polynomial_image_of_cone` replaces B by

B_min = { T : there exists an attained least element r of D(T) with r ≤ 1 }.

Thus the proof also covers a literal minimum reading without assuming global attainment as an axiom or silently identifying two definitions.

The specialized theorem `nuclearBall_not_polynomial_image_of_spectrahedralCone4` quantifies over all n, all real linear maps L : R^n → Mat_(4×4)(R), and all P as above, and proves

P({x : L(x) is positive semidefinite}) ≠ B.

The real PSD predicate includes symmetry. The tensor target and every factor remain complex throughout.

## Genuine definitions and correspondence

`NuclearNorm.lean` uses Mathlib's `EuclideanSpace ℂ (Fin 2)`, not the coordinate supremum norm. `rankOne a b c` is explicitly the array `a i * b j * c k`. Decompositions are arbitrary finite lists of such factors, allowing any number of terms and repeated terms. The scalar cost is the usual product of the three Euclidean factor norms, summed over terms. No desired coordinate bound is built into this definition.

Allowing zero factors in a pure-tensor decomposition is harmless, and this is proved rather than presumed. `termTensor_eq_zero_iff` proves a pure tensor is zero exactly when some factor is zero; `termCost_eq_zero_of_tensor_zero` proves its cost is then zero. `remove_zero_terms` deletes these terms while preserving both the tensor sum and the cost. `mem_decompositionCosts_iff_nonzero_terms` identifies the same cost set with decompositions using only nonzero decomposable tensors, i.e. genuine rank-one terms. The empty sum represents the zero tensor.

`coordinate_expansion` proves the ordinary expansion using all eight coordinates: sum over i,j,k of `(T_ijk e_i) ⊗ e_j ⊗ e_k` equals T. Thus every D(T) is nonempty. Every cost is nonnegative, so each infimum is mathematically legitimate. `nuclearNorm_eq_minimum` proves any exhibited minimum equals the infimum formula. The direct B_min result makes a global minimum-attainment theorem unnecessary for this disproof.

`TensorPolynomialMap` records all eight real-part coordinate polynomials and all eight imaginary-part coordinate polynomials. Its evaluation constructs the resulting complex array. These are ordinary `MvPolynomial` objects, with no custom predicate defining “polynomial” by the desired conclusion. `PolynomialCone.exists_real_imag_polynomials` proves that every complex-coefficient multivariate polynomial on real inputs has real and imaginary parts given by real multivariate polynomials. `complex_polynomials_represented` transfers that fact to the tensor-valued map. This covers complex coefficients as well as real coefficients in the real parameters of a symmetric-matrix cone. A cone in a complex coordinate space can also be expressed in real coordinates; the chosen map class is the standard broad real-coordinate polynomial class.

`IsCone` means explicitly that 0 belongs and every nonnegative real multiple of every member belongs. This is weaker than imposing convexity, addition closure, or a particular matrix description, so impossibility for this class does not strengthen the conjecture to make it false.

`spectrahedralCone4 L` is the preimage of Mathlib's actual `Matrix.PosSemidef` predicate under the real linear pencil L. Positive semidefiniteness means symmetry and vᵀAv ≥ 0 for every real v. `posSemidef_smul_nonneg` derives closure under nonnegative scalar multiplication from the PSD definition. `spectrahedralCone4_isCone` also proves zero membership using L(0)=0. This is a genuine source-instance theorem, not a cone axiom added to the matrix predicate.

## Complete mathematical argument

1. For any a,b,c in C² and any i,j,k, the usual coordinate inequalities give |a_i b_j c_k| ≤ ||a||₂ ||b||₂ ||c||₂. For every finite decomposition of T, the triangle inequality therefore gives |T_ijk| ≤ its scalar cost. Taking the infimum over the nonempty cost set proves |T_ijk| ≤ ν(T). Every T in B consequently satisfies |Re T_000| ≤ 1.

2. The empty decomposition gives ν(0) ≤ 0, and nonnegativity gives ν(0)=0. Let E=e_0⊗e_0⊗e_0. Its one-term cost is 1, while its (0,0,0) coordinate is 1, so the coordinate lower bound gives ν(E)=1. Hence 0 and E both belong to B and have different real (0,0,0) coordinates. Their costs 0 and 1 are attained minima, so both also belong to B_min. Every member of B_min lies in B by the proved infimum/minimum correspondence.

3. A real polynomial q bounded in absolute value for all t≥0 has degree at most zero and is constant. Mathlib's `Polynomial.abs_isBoundedUnder_iff` proves the degree fact from eventual boundedness at +∞; the author theorem constructs this eventual bound from the nonnegative-half-line bound and applies `Polynomial.eq_C_of_degree_le_zero`.

4. For a multivariate real polynomial p and fixed x, substitute X_i = x_i X to obtain the genuine univariate `rayPolynomial p x`. The formal substitution identity proves its evaluation at t equals p(tx). If C is a cone and p is bounded on C, then for x∈C this ray polynomial is bounded for every t≥0. Thus p(x)=p(0). This holds for every x∈C.

5. Suppose P(C)=B. Apply step 4 just to the real (0,0,0) coordinate polynomial of P. It is bounded by 1 on C by step 1, so it has the same value at all points of C. Surjectivity onto B supplies preimages of 0 and E, whose corresponding coordinate values are 0 and 1. This is a contradiction. The same reasoning applies to every set containing 0 and E and contained in B, so it also applies to B_min.

6. Every homogeneous real PSD linear-pencil cone, including the stipulated 4 × 4 case, satisfies `IsCone` by the directly proved scaling and zero properties. The specialized matrix claim follows. Because the original whole claim necessarily contains the already-negated cone-image clause, the whole claim is disproved regardless of its additional SDP assertion.

All sums, inequalities, polynomial substitutions, and exact witness values are verified by Lean. No numerical experimentation, unverified optimization, external computer algebra, auxiliary numerical program, or mathematical assumption is used.

## Verification and project structure

The project is pinned to Lean 4.19.0 and Mathlib v4.19.0 commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The supplied neutral scaffold contained no mathematical sources. The only configuration change was to register the two new subordinate libraries `NuclearNorm` and `PolynomialCone`; the default targets remain `Solution` and `AuthorAudit`. The original manifest and toolchain remain unchanged.

- `NuclearNorm.lean`: the complex tensor definition, actual decomposition costs, coordinate bounds, exact witnesses, zero-term correspondence, and attained-minimum variant.
- `PolynomialCone.lean`: univariate boundedness, genuine ray substitution, cone constancy, coordinatewise corollary, and complex-coefficient correspondence.
- `Solution.lean`: polynomial tensor maps, generic contradiction, literal-minimum result, genuine 4 × 4 PSD instance, and main negation.
- `AuthorAudit.lean`: `#print axioms` for every one of the 54 explicitly declared objects and results, including all author theorems and helper results.

Actual build, strict replay, and axiom logs are retained under `/private/tmp/tlmc1478-author-work/revision-2/logs`, with commands and exit codes in `/private/tmp/tlmc1478-author-work/revision-2/verification-status.json`. All six recorded verification commands returned exit code 0. The final verification consists of the complete default build followed by `lake env lean -DwarningAsError=true` on each of the four source modules. Axiom inspection permits only the standard foundational axioms `propext`, `Classical.choice`, and `Quot.sound`; definitions may require fewer or none. No `sorry`, `admit`, `native_decide`, custom axiom, unsafe proof shortcut, or additional mathematical assumption occurs.

Failed source attempts remain outside the final project in `/private/tmp/tlmc1478-author-work/scratch` and the helper's `polynomial-scratch`, together with actual failed-build logs. Auxiliary scripts are engineering tools for invoking Lean, recording exit codes, inventories, and hashes; they establish no mathematical facts.

## Remaining scope and limitations

The result establishes the negative representation conclusion fully. It does not establish global minimum attainment or all norm axioms, because neither is needed: it works directly from the standard decomposition-cost formula and separately rules out the actual attained-minimum ball. It does not treat a modified statement using an affine section of a cone, a rational map, or some other normalization. It does not settle nuclear-norm SDP computability by other means. These are scope boundaries of the conjecture's disproof, not unproved assumptions used by it.

The original's abbreviated scalar-cost wording is stated above rather than concealed. Both the conventional infimum and literal attained-minimum readings have formal negative results. No tensor dimension, field, factor norm, polynomial-map class, or cone scaling qualification is changed to manufacture the contradiction.

## Source and collaboration provenance

Author-stage primary inputs read in full were `/private/tmp/tlmc1478-author-input/00000001478.md`, the two allowed repository READMEs (`/Users/daniel/The-Last-Math-Competition/README.md` and `README.zh-CN.md`), and the same input directory's `source-identity.json` and `scaffold-provenance.json`. The original hash is `1b480a1a46f403fa9f6bf21c036cc5dedec53ec71dfe38609e8fce34c13bd716`. The neutral `lakefile.toml`, `lake-manifest.json`, and `lean-toolchain` were inspected. The initial independent quantifier/ambiguity record is `/private/tmp/tlmc1478-author-work/INITIAL-SEMANTICS.md`.

Only ordinary pinned Lean/Mathlib standard sources were consulted thereafter, through `/private/tmp/tlmc-standard-library-419`. The actual declarations read or used came from:

- `mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`: Euclidean single vectors, their entries, and their norms.
- `mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean`: Euclidean coordinate norm bounds.
- `mathlib/Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean`: finite-set/list sum conversion.
- `mathlib/Mathlib/LinearAlgebra/Matrix/PosDef.lean`: the genuine PSD predicate and its zero case.
- `mathlib/Mathlib/LinearAlgebra/Matrix/Hermitian.lean`, `mathlib/Mathlib/Data/Matrix/ConjTranspose.lean`, and `mathlib/Mathlib/Data/Matrix/Mul.lean`: symmetry, transpose, scalar multiplication, and quadratic-form identities.
- `mathlib/Mathlib/Analysis/Polynomial/Basic.lean`: bounded polynomial degree criterion.
- `mathlib/Mathlib/Algebra/MvPolynomial/Eval.lean`: evaluation and polynomial induction.
- `mathlib/Mathlib/Algebra/Polynomial/Degree/Definitions.lean` and `Operations.lean`: degree-zero and constant-polynomial identities.
- `mathlib/Mathlib/Data/Complex/Basic.lean`: real and imaginary parts under arithmetic.
- `mathlib/Mathlib/Analysis/Asymptotics/SpecificAsymptotics.lean`: its imports were read only to identify a missing standard compiled dependency.

Discovery-only text searches also examined the ordinary `Analysis` and `LinearAlgebra` trees for projective-norm and coordinate-bound APIs. They returned snippets in `Analysis/NormedSpace/PiTensorProduct/{ProjectiveSeminorm,InjectiveSeminorm}.lean`, `Analysis/Normed/Algebra/Spectrum.lean`, `Analysis/Normed/Lp/lpSpace.lean`, `Analysis/Normed/Group/Constructions.lean`, `Analysis/Normed/Module/FiniteDimension.lean`, and standard `Analysis/CStarAlgebra` files. A separate discarded design search examined `Analysis/Seminorm.lean` and `Analysis/Normed/Group/Seminorm.lean`. None contributed an unproved fact or external problem material. Search expressions and source roles are recorded in `SOURCE-PROVENANCE.md` in the author-work directory.

A fresh helper `/root/author_1478/polynomial_cone` was created with `fork_turns:none`, only this problem's original/rules/provenance, the neutral project, and the permitted standard-library/runtime paths. After the author's independent choice of the cone-ray obstruction, the helper developed `PolynomialCone.lean` and later its complex-coefficient correspondence. The helper's own full consultation and retained-attempt record is `/private/tmp/tlmc1478-author-work/polynomial-scratch/consultation-and-build-log.txt`. The author inspected and independently included every helper result in the full build, strict replay, and axiom audit.

Root provided only engineering help to compile two missing ordinary standard Mathlib modules (`Analysis.Asymptotics.SpecificAsymptotics` and `Analysis.Polynomial.Basic`) while preserving the pinned sources. No earlier proof, screening note, repository solution, other original, unrelated mathematical context, website, thread/app inventory, or symlink-target parent directory was consulted. No proof material was sent to an old-context solving agent.

## Complete theorem inventory

The following inventory lists every proved theorem. All explicitly declared definitions, abbreviations, and the map structure are additionally covered by `AuthorAudit.lean`.

| Module | Theorem |
|---|---|
| `NuclearNorm.lean` | `TLMC1478.termCost_nonneg` |
| `NuclearNorm.lean` | `TLMC1478.decompositionCosts_bddBelow` |
| `NuclearNorm.lean` | `TLMC1478.coordinate_expansion` |
| `NuclearNorm.lean` | `TLMC1478.decompositionCosts_nonempty` |
| `NuclearNorm.lean` | `TLMC1478.norm_termTensor_le` |
| `NuclearNorm.lean` | `TLMC1478.norm_list_sum_coordinate_le` |
| `NuclearNorm.lean` | `TLMC1478.coordinate_le_nuclearNorm` |
| `NuclearNorm.lean` | `TLMC1478.nuclearNorm_nonneg` |
| `NuclearNorm.lean` | `TLMC1478.nuclearNorm_eq_minimum` |
| `NuclearNorm.lean` | `TLMC1478.nuclearNorm_rankOne_le` |
| `NuclearNorm.lean` | `TLMC1478.nuclearNorm_zero` |
| `NuclearNorm.lean` | `TLMC1478.basisTensor_origin` |
| `NuclearNorm.lean` | `TLMC1478.nuclearNorm_basisTensor` |
| `NuclearNorm.lean` | `TLMC1478.zero_mem_nuclearBall` |
| `NuclearNorm.lean` | `TLMC1478.basisTensor_mem_nuclearBall` |
| `NuclearNorm.lean` | `TLMC1478.nuclearBall_coordinate_bound` |
| `NuclearNorm.lean` | `TLMC1478.termTensor_eq_zero_iff` |
| `NuclearNorm.lean` | `TLMC1478.termCost_eq_zero_of_tensor_zero` |
| `NuclearNorm.lean` | `TLMC1478.remove_zero_terms` |
| `NuclearNorm.lean` | `TLMC1478.mem_decompositionCosts_iff_nonzero_terms` |
| `NuclearNorm.lean` | `TLMC1478.minimumNuclearBall_subset` |
| `NuclearNorm.lean` | `TLMC1478.isLeast_cost_of_mem_of_norm_eq` |
| `NuclearNorm.lean` | `TLMC1478.zero_mem_minimumNuclearBall` |
| `NuclearNorm.lean` | `TLMC1478.basisTensor_mem_minimumNuclearBall` |
| `PolynomialCone.lean` | `PolynomialCone.polynomial_eval_eq_eval_zero_of_bounded_nonneg` |
| `PolynomialCone.lean` | `PolynomialCone.eval_rayPolynomial` |
| `PolynomialCone.lean` | `PolynomialCone.eval_eq_eval_zero_of_bounded_on_cone` |
| `PolynomialCone.lean` | `PolynomialCone.polynomial_map_eq_zero_of_bounded_on_cone` |
| `PolynomialCone.lean` | `PolynomialCone.exists_real_imag_polynomials` |
| `Solution.lean` | `TLMC1478.complex_polynomials_represented` |
| `Solution.lean` | `TLMC1478.no_polynomial_cone_image_between` |
| `Solution.lean` | `TLMC1478.nuclearBall_not_polynomial_image_of_cone` |
| `Solution.lean` | `TLMC1478.minimumNuclearBall_not_polynomial_image_of_cone` |
| `Solution.lean` | `TLMC1478.posSemidef_smul_nonneg` |
| `Solution.lean` | `TLMC1478.spectrahedralCone4_isCone` |
| `Solution.lean` | `TLMC1478.nuclearBall_not_polynomial_image_of_spectrahedralCone4` |
| `Solution.lean` | `TLMC1478.conjecture00000001478_false` |

## Revision 2: executable-artifact cleanup

Revision 1 remains immutable in `frozen-project`. A later complete inventory of its compiled module-owned declarations found compiler-generated executable helpers and unsafe specialization placeholders that were absent from the safe mathematical dependency closure. The 54 author declarations and all theorem proofs used only standard foundational axioms, but the broader artifact policy excludes these unnecessary generated artifacts as well.

This revision adds the explicit `noncomputable` modifier to exactly five definitions: `rankOne`, `termTensor`, `nuclearBall`, `minimumNuclearBall`, and `TensorPolynomialMap.eval`. Definition bodies, all mathematical statements and proofs, imports, the explicit 54-declaration audit, and the project configuration remain unchanged. The modifier suppresses executable compilation; it introduces no assumption and changes no mathematical meaning. A mechanical comparison verifies that the complete mathematical source equals revision 1 after removing only these modifiers.

The current same-problem engineering diagnostic metadata under `/private/tmp/tlmc1478-engineering/probe-02` was the only additional consulted material. Its generated-declaration inventory and safe-dependency closure were inspected, as was its verification-only probe source. The revision's exact source diff, receipts, and complete module-owned inventory are retained under `/private/tmp/tlmc1478-author-work/revision-2`. All original mathematical provenance and the initial source interpretation remain unchanged.

Revision 2 verification passed: all six build/strict-replay commands returned zero; the unchanged 54 explicit declarations have only the three standard foundational axioms; a separate complete compiled inventory found 75 module-owned declarations, zero owned axioms, and zero unsafe declarations. The inventory verifier itself is engineering-only and is not imported into the mathematical project.
