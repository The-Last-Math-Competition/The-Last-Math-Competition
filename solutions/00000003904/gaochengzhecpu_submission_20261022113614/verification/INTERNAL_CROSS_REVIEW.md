# Independent cross-review of 3904

**Verdict: PASS for the stated one-variable graded counterexample. No mathematical or Lean-model defect requiring a frozen-source change was found.** The paper must preserve the recorded formalization boundary: the supplied Lean proves the standard splitting-count computation for the actual graded Veronese ring. It does not prove a localization comparison theorem in Lean.

Reviewer: the graph agent, separate from the 3904 author. No subagent was used. No frozen 3904 source, notes, handoff, or log was modified. This review did not repeat the parent's fresh-build step.

## Material read and integrity

Read the complete 353-line `round5/drafts/00000003904/lean/Main.lean`, the complete `round14/other/3904-NOTES.md`, `3904-HANDOFF.json`, `3904-checks.json`, the strict log, and the exact bilingual `round5/source/00000003904.md`.

Independently recomputed SHA256 values match the handoff for:

- Main: `1d17fcda094c2ad77b4830848dd265d8538b1d5d8c0db20708d575dd0a4bcb06`.
- Exact source: `39268746056239c928c816338d6af1b5cb6cbca0e9112fb05f885aa3fa42fbfd`.
- Notes: `fe3db47a3d5f929f6c297c2c3f3f07ae0b8457edc9de84612e49ff5da5f58ec8`.
- Checks record: `5b5093e118cc3b02eeca77ddc53c01afc0f18fee59b08d340929eb04efe8f4ce`.

Both recorded build/strict exit codes are zero, and both actual log hashes match the checks record. All 21 exported axiom reports in the strict log contain only `propext`, `Classical.choice`, and `Quot.sound`.

## 1. Is n=1 a valid instance of the exact source?

**Yes.** Both source languages define the ring by all degree-d monomials and state the asymptotic without imposing n≥2 or any other exclusion of one variable. Taking a polynomial ring in one variable is the direct n=1 specialization under the usual meaning of n. The source does not specify a coefficient field that would exclude F₂; F₂ is an especially clean permitted characteristic-positive field. If “subring generated” is interpreted without an explicit coefficient-field adjoin, there is still no discrepancy over the prime field F₂: a unital generated subring already contains those coefficients.

For n=1 there is exactly one coefficient-one monomial of degree d, namely X^d. Allowing scalar coefficients does not enlarge the generated F₂-algebra. `degree_d_monomials_adjoin` proves the actual equality with the entire scalar-monomial generating set. Thus this is not merely a different abstract polynomial ring assigned the Veronese name.

Every relevant theorem assumes d>0. The unneeded d=0 values are totalized only for Lean. The final asymptotic argument uses eventually positive d, so d=0 cannot affect it. No coprimality condition 2∤d is needed: even when 2 divides d, F₂[X^d] is a polynomial ring on the independent generator X^d.

The unknown c(n) being called a rational function creates no legitimate n=1 exemption. The claimed formula at n=1 requires a finite value c(1). The final Lean theorem excludes every real value of this constant. A pole at n=1 would instead make the asserted formula undefined there; it is not an unstated n≥2 hypothesis in the source.

## 2. Actual ring, Frobenius, and module

**PASS.** At lines 36–46, `veronese d` is the genuine subalgebra `Algebra.adjoin K {X^d}` of `Polynomial (ZMod 2)`. Expansion is the actual polynomial map f(T)↦f(X^d); its range is identified with that subalgebra and its injectivity for d>0 gives an actual algebra equivalence. The identification with all degree-d monomials is separately proved at line 264.

The coefficient Frobenius is proved to be the identity on the actual two-element field, rather than assumed. `expand_pow_two` then identifies the actual q-expansion with the qth-power Frobenius for every q=2^e.

The auxiliary `Push q` module has the actual restriction-of-scalars action along polynomial expansion. More importantly, the final `VPush d e` at lines 137–147 uses `Module.compHom` along Mathlib's actual `iterateFrobenius`, and `vPush_smul` explicitly proves a•m=a^(2^e)m. It is not accidentally the ordinary rank-one module.

The synthesis map is coefficient-based and proved bijective for every positive q. Its injectivity reads coefficient q*n+i; its surjectivity uses the exact quotient/remainder decomposition of each monomial exponent. Transport through the actual Veronese algebra equivalence is linear for the twisted scalar action. The resulting `veroneseFrobeniusEquiv` is a genuine module equivalence from q-tuples to the actual Frobenius module. The theorem at line 190 identifies its basis vectors as the actual polynomials X^(d*i). This includes q=1, e=0.

## 3. Free summands, dimension, and normalization

**PASS.** `freeSummandRanks` at line 213 quantifies actual linear injections with actual linear retractions whose composition is identity. This is the standard split-free-summand condition. Its supremum is not set equal to the desired answer by definition. The upper bound follows from injectivity and the strong rank condition; attainment follows from the actual q-dimensional free equivalence. `freeRank_eq_of_equiv` proves both inequalities, and `veronese_splitting_number` applies it with a genuine finite-module instance derived from the synthesis surjection.

The dimension is computed for the actual ring. `polynomial_dimension` uses the PID prime-ideal bound for the upper bound and the actual polynomial Krull-dimension lower bound for the lower bound. `veronese_dimension` transfers the resulting dimension one through the actual ring equivalence. No dimension-one hypothesis is merely postulated.

The normalizing denominator q at line 287 is consequently q^dim(V_d). The field correction is one because the coefficient/residue field F₂ is perfect, as witnessed by the identity coefficient Frobenius. Thus a_e/q=1 follows from the actual maximal split rank, not just from a basis-cardinality guess or a numerical proxy.

## 4. Graded versus local meaning

**PASS within the stated graded scope; retain this boundary in the paper.** I independently checked the primary reference [Anurag K. Singh, *The F-signature of an affine semigroup ring*](https://arxiv.org/pdf/math/0409143), introduction, page 1. It defines F-signature for local or graded rings through ordinary R-module free-summand counts, normalized by q raised to Krull dimension, under the stated perfect-residue-field/F-finiteness hypotheses. This is the definition implemented here. Its Example 3.2 explicitly treats at least two variables; that example must not be cited as the computation for the present one-variable instance.

The actual ring has the natural positive grading with generator t=X^d. This may be regraded so deg(t)=1. The displayed Frobenius basis 1,t,...,t^(q−1) is homogeneous in the rationally graded Frobenius module, with degrees 0,1/q,...,(q−1)/q after regrading. Hence its complete free decomposition is also a direct sum of graded shifts. Counting only degree-zero unshifted splittings would be a different quantity and is not the standard graded F-signature definition used in the notes.

The Lean file does not package a grading, rational grading shifts, localization at (t), or a formal comparison between global/graded and local Frobenius splitting counts. This is accurately disclosed by the handoff. It is not a defect in the directly computed graded splitting-count result. The paper should not claim those additional structures or comparison theorems were encoded in Lean.

If the paper includes an ordinary mathematical local restatement, the bridge should be explicit: localizing the proved free Frobenius module at the homogeneous maximal ideal (t) preserves its q-element basis, and restriction of scalars commutes here with localization. Concretely, under the standard comparison map a module fraction F_*a/s maps to F_*(a/s^q); every target F_*(b/s) has preimage F_*(b*s^(q−1))/s. Thus the localized ring has the same splitting count q and dimension one, with residue field F₂. This is an explanatory mathematical bridge, not an already-exported Lean theorem. The core disproof need not invoke it at all.

## 5. Actual limiting assertion and original conjunction

**PASS.** The F-signature is defined as `limUnder` of the actual normalized splitting counts; convergence is proved before extracting its value. It is not an arbitrary scalar defined to be one.

The final theorem uses genuine Mathlib `Asymptotics.IsBigO`, permits every real correction c and every remainder r(d)=O(d^−2), and only assumes eventual equality. The reciprocal d^−1 and the remainder tend to zero, so the asserted n=1 expression tends to zero. The actual signature is eventually identically one. Uniqueness of real limits gives the contradiction. This matches asymptotic semantics and refutes a clause of the source conjunction. It does not incorrectly assert that strong F-regularity fails.

## Independent exact sanity check

Without changing any frozen file, independently executed a standard-library integer-bitset polynomial checker over F₂. It exhausts all 4096 polynomials of degree at most 11 for each d=1,...,8 and q∈{1,2,4,8,16}: 163840 cases. Every case checks the residue-class synthesis identity, commutation of d-expansion with qth Frobenius expansion, and the transported synthesis in F₂[X^d]. All passed, including e=0 and characteristic dividing d. This is a finite consistency check only; the unrestricted claims are proved by Lean.

## Recommendation

Proceed with the parent's fresh independent build, paper/PDF review, and one-problem submission. Preserve the precise wording “standard graded F-signature computed from actual Frobenius splitting counts.” If local wording is retained, label its explicit localization explanation as a mathematical bridge outside the supplied Lean formalization. No frozen source edit is requested by this review.
