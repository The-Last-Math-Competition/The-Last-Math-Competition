# Independent semantic review of frozen submission 00000001473

## Verdict and boundary

PASS for mathematics, formalization meaning, and correspondence to the supplied conjecture under the stated qualification scope. No mathematical correction or formalization correction is requested.

This is not a certificate that the independent engineering review or the final LaTeX/PDF review has passed. Independent rebuild/execution belongs to the separately assigned engineering review. The final report and PDF were not provided for this review and remain to be reviewed in full when supplied.

I read the entire frozen `Proximity.lean` (420 lines), `Audit.lean` (36 lines), and `lakefile.lean` (8 lines), together with the entire `ARGUMENT.md`, `PROVENANCE.md`, and project README. I also inspected the frozen author theorem/axiom printout and the relevant stock Mathlib norm/extreme-point definitions. All 80 entries of the frozen manifest were independently checked for both byte length and SHA-256 digest. The successful verification is recorded in `frozen-input-verification.json`.

No author files were changed. I did not inspect other submissions, selector material, agent rosters, app histories, or author work in progress. I did not perform any external search, communication, or repository edit. The original isolated inputs and initial independent mathematical assessment remain separately preserved in this reviewer workspace.

## Frozen identities

| Artifact | SHA-256 |
| --- | --- |
| Author FREEZE.json | 6883face1dac5f4217a7e06a73c963341671a01fc50fe0ee29014d7f2fe32542 |
| Proximity.lean | 940f2f162a82f7a58f36bb235482565328048bb4fe0baf7aa7fa304fb7921e2c |
| Audit.lean | 12ebd6e1a70d0e111ccc57d388acea4aaba19b9b51f3dcc176b55059325d461c |
| lakefile.lean | ca65574d6cf86ad76c618c7885288487261f7ba59a19478ade18e0e97dddbc1a |
| ARGUMENT.md | 86716003a1f0afc8f4e3f6cbd0a7d7d4c3ecb805e955b6cc64a4a1d1b5915c20 |
| PROVENANCE.md | 49dccc7ba9830783e5406bb82a3ca7ea55b145815f763909cb02cfe14e18de70 |
| Original conjecture | bdceacf9b92330afb3ee49161d60a121e65ad4724d70bf332b76f7c843ba89d5 |

The supplied Lean 4.19.0 toolchain and Lake manifest are byte-identical in the frozen project and original-input copies. The stock Mathlib checkout inspected for semantics has HEAD `c44e0c8ee63ca166450922a373c7409c5d26b00b`; the two inspected stock source files have no tracked changes against that revision. This source-semantic check is not a claim to have independently rebuilt every dependency.

## Definition audit

`Row` and `ILP` (lines 11–21) describe ordinary finite pure integer linear programs. Every coefficient, right-hand side, optional finite bound, objective coefficient, and objective constant is integral. `Fin n` indexes exactly n decision coordinates. All constraints are finite lists.

`Row.eval`, `feasible`, and `intFeasible` (lines 23–35) are faithful. Real feasibility tests every equality row with equality, every inequality row with <=, and every present lower/upper bound. Integer feasibility is that identical predicate applied to the coordinatewise integer-to-real embedding. It neither drops a real constraint nor introduces a different integer constraint. `none` means no finite bound, rather than silently assigning a large omitted finite value.

`objective`, `realOptimal`, and `integerOptimal` (lines 37–45) are faithful. The objective is the dot product plus the stated constant. Each optimum is required to be feasible and to have objective no greater than every feasible competitor's objective. The integer version quantifies over all integer vectors. The unique versions (lines 47–51) require equality with every other global optimum. There is no restricted candidate set or optimization oracle.

`vertex` (lines 53–57) is the ordinary extreme-point condition, including membership in the feasible set: every representation of x as t*y+(1-t)*z with feasible y,z and 0<t<1 has y=x and z=x. The stock definition `Set.extremePoints` in `Mathlib/Analysis/Convex/Extreme.lean` uses membership in an open segment and equality of both endpoints to x. Over the reals, the positive weights a,b with a+b=1 defining that open segment correspond exactly to t=a, b=1-t. Thus the local predicate has the usual meaning, rather than a weakened surrogate. For the linear feasible polyhedra at issue, this is the usual notion of a vertex.

`Row.data`, `ILP.data`, and `delta` (lines 59–67) include every finite input category. Each row contributes all coefficients and its right-hand side; both row lists are included. Present lower and upper bounds are included, followed by the entire objective vector and constant. Applying `Int.natAbs` and taking the finite maximum starting at 0 gives the actual maximal input magnitude. The list always includes the constant, so there is no empty-input subtlety. No solution coordinate, derived equation coefficient, or determinant is passed off as an omitted input datum.

## Four actual representations

| Form and source lines | Actual coordinates/domains | Actual rows | n | Delta | Norm gap | Comparison |
| --- | --- | --- | --- | --- | --- | --- |
| `mixedFree`, 69–76 | x,y,z integral/free | y=10x; z=10y; -2x<=-1 | 3 | 10 | 50 | 50>30 |
| `inequalityFree`, 78–87 | x,y,z integral/free | -2x<=-1 and two opposite inequalities for each linking equality | 3 | 10 | 50 | 50>30 |
| `inequalityNonnegative`, 89–91 | x,y,z integral with lower bounds 0 | Same five inequalities | 3 | 10 | 50 | 50>30 |
| `equalityNonnegative`, 93–101 | x,y,z,s integral with lower bounds 0 | y=10x; z=10y; 2x-s=1 | 4 | 10 | 50 | 50>40 |

Every form minimizes x, has objective constant 0, and has no finite upper bounds. The real relaxation changes every integral coordinate to a real one and retains all rows and domain bounds. All input magnitudes are at most 10, and an actual coefficient -10 occurs. The value 100 arises only after composing the two coefficient-10 equalities and in derived optima; it is not an input equality coefficient or a finite bound in any of these four forms.

The definitions of the rays and points (lines 103–112) describe the actual feasible sets and proposed optima. The four feasibility equivalences (lines 114–152) prove both directions from the actual rows and bounds. In the nonnegative inequality form, the lower bounds are implied by the rows. In the equality form, nonnegativity of s forces x>=1/2; the converse also establishes every coordinate's nonnegativity. The exact equality form therefore has no accidental extra feasible points and excludes no original feasible points under the slack extension.

The four objective lemmas (lines 154–163) reduce each actual finite objective to the first coordinate. These are proven identities, not assumptions retained in a final theorem.

## Optimization, uniqueness, vertex, and norm

The generic lemmas `optimum3` and `optimum4` (lines 166–249) use a feasible-set equivalence and first-coordinate objective identity. Each actual certificate later supplies already-proved instances of both hypotheses. Real feasibility is parametrized by t>=1/2 and integer feasibility by integral t>=1. The real and integer candidate points satisfy every constraint. Comparison with arbitrary feasible points gives global minimality. Comparing any alleged other optimum to the candidate forces its first coordinate to 1/2 or 1; the remaining coordinates are then fixed. The cast arguments correctly transfer strict positivity and order between integers and reals. Thus both minima are attained and unique.

The vertex lemma (lines 251–274) uses only the stated unique real minimum and the actual first-coordinate objective identity. Every feasible endpoint has first coordinate at least the optimum's. A strict convex combination equal to the optimum must have both endpoint first coordinates equal to the optimum's. Each endpoint is consequently an optimum, and uniqueness forces equality of the full vectors. This argument is valid; it does not assume an unstated rank property or infer a vertex merely from feasibility.

The norm used in lines 276–294 is the existing Mathlib norm on `Fin n -> Real`. The inspected stock construction in `Mathlib/Analysis/Normed/Group/Constructions.lean` defines the finite product norm as the supremum of the coordinate norms. Its additive lemmas `pi_norm_le_iff_of_nonneg` and `norm_le_pi_norm` are exactly the upper- and lower-bound facts used here. On Real, `Real.norm_eq_abs` is the absolute value. No custom norm instance or Euclidean-norm replacement is introduced.

`distance3` checks every coordinate difference is at most 50 and obtains a matching lower bound from coordinate 2. The differences are (1/2,5,50). `distance4` repeats the same argument in the four-coordinate ambient space, where the differences are (1/2,5,50,1). Consequently both norms are exactly 50, rather than merely lower bounds.

The four Delta theorems (lines 296–299) are decidable calculations of the data lists of the four actual programs. Using `decide` here does not introduce an axiom or external computation premise. The actual data listed above independently confirm each result.

## Certificates and final negation

`Certificate` (lines 301–305) includes unique integer and real optima, the relaxed vertex property, exact Delta=10, exact norm=50, and the strict inequality n*Delta<norm. Each of the four actual certificate theorems (lines 307–335) proves every conjunct for its own dimension and data. The implicit n is determined by its program's type; no three-coordinate n is reused for the four-coordinate program.

`UniversalUpperBound` (lines 337–341) is the advertised bound over finite integral-data pure ILPs and actual global optima. Its universal quantification over choices of optima could be stronger than a reading of proximity that asks for some nearby optimum, but the witnesses have unique optima, so this possible distinction cannot save the original bound. The separately defined `UniqueVertexUpperBound` makes that robustness explicit.

`not_universalUpperBound` (lines 349–353) instantiates the universal bound with the three-coordinate program and contradicts the actual certificate's strict reverse inequality. `not_uniqueVertexUpperBound` (lines 355–359) does the same with the four-coordinate equality/nonnegative program, supplying uniqueness and the vertex property. Both final theorems have no mathematical hypotheses. They do not merely prove a conditional counterexample whose assumptions remain unestablished.

`not_source_conjunction` (lines 361–366) correctly derives the falsity of the conjunction of the universal bound with any sharpness proposition. The proposition parameter supplies no premise or oracle. This theorem does not assert that the standalone existential sharpness statement is false. The argument and provenance consistently state that limitation.

## Representation equivalence and remaining lines

The definitions and lemmas at lines 369–418 explicitly implement the slack map and projection. The integer extension has last coordinate 2x-1 and commutes with the integer embedding. The real feasible-set equivalence, integer extension equivalence, feasible projection, both inverse identities on their proper domains, and objective preservation are all correct. The three-coordinate equivalence theorem proves both required feasible-set conversions and both objective identities. Integer equivalence of the three-coordinate forms follows immediately by evaluating the real equivalence on integer casts.

Projection of an integer four-vector is automatically integral; no divisibility obstruction is hidden in the inverse direction. Each form also has its own direct optimum proof, so the certificates do not rely on an unproven general theorem that representation changes preserve proximity. No arbitrary padding or scaling invariance is claimed.

The namespace/section boundaries and imports contain no extra premises, renamed arithmetic operations, replacement norms, custom axioms, or other semantic devices. `Audit.lean` only imports the proof and prints/checks definitions, theorem types, and axiom dependencies. `lakefile.lean` specifies the ordinary package/library and pinned Mathlib requirement with warnings as errors. The frozen printed types agree with the source. The frozen author's axiom printout reports only `propext`, `Classical.choice`, and `Quot.sound`; independent reproduction is properly left to engineering.

## Argument, provenance, and source fidelity

Every mathematical claim in `ARGUMENT.md` is supported by the reviewed argument and matching definitions/theorems. In particular, the document distinguishes finitely many variables/rows from boundedness of the feasible region, accounts for all finite bound and objective data, counts the added slack coordinate, and computes each norm in the appropriate ambient coordinates.

The original English and Chinese statements impose no compactness, full-dimensionality, determinant-based Delta, or special matrix condition. The source does not itself define n formally; the report transparently adopts the supplied qualification of actual decision-coordinate count. Both optima are unique and attained and the relaxed point is a vertex, so none of those common extra conditions creates a gap. Falsifying the bound on this ordinary integral-data subclass suffices even if the intended overall class is broader.

The named literature wording does not justify silently changing Delta from maximum input magnitude to a determinant parameter. The report correctly avoids that substitution and does not claim to settle a different literature theorem. It also avoids claiming that every possible encoding would retain the violation.

`PROVENANCE.md` accurately describes the visible formalization scope, declared dependency pins, separation between proof and supporting computation, and remaining report/publication responsibilities. Historical and behavioral statements about what the author did or did not inspect are author attestations; I cannot independently establish the entire author's access history without inspecting prohibited histories. I checked the frozen artifacts and source identities, not private behavioral history. This does not affect the mathematical correctness assessment.

## Completion state

No semantic defects found. This frozen proof and argument are suitable for the final report-matching review once that report/PDF is supplied. Independent engineering execution and full final-report/PDF review remain separate required checks, so this document alone is not a complete competition-rule submission approval.
