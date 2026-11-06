# Statement Alignment: Conjecture 00000000918

## Exact Printed Assertion

Both full languages are preserved unchanged in `source.md`. Fixed organizer
commit: b355e42906e6eaf52bc7e9d005e0ef02d8aa7400. Git blob:
dadc2ef65f6a57feb3def12febafd66299b1f918. Raw UTF-8 SHA-256:
326b3e1b5e32b83188a2648a49b823f81b6d8ae7a0a6af46d08a71338998676f.
Only CRLF-to-LF normalization is used for current-organizer working-file
comparison; the submitted source.md retains the original raw Git bytes.

The source defines quasi-traces by the abbreviated phrase subadditive weakly
continuous trace functionals, then asserts for a nuclear algebra a quasitrace
simplex with factor-trace extreme points, dimension one and closed extreme set.
Neither language specifies simple algebras, factors, faithful states, a fixed
trace ray or a chosen segment. The factor-trace phrase applies to extreme
POINTS, not a restriction on the underlying algebra. We do not silently add
any of those premises.

## The Necessary Clause, Not A New Conjecture

Under the standard nuclear C*-algebra/quasitrace interpretation, dimension of
the simplex is REAL affine dimension. It is not complex algebra dimension,
dimension of a factor representation, or a pointwise trace scaling parameter.
A universal dimension-one claim entails its restriction to finite-dimensional
commutative unital nuclear algebras. `FiniteCommutativeDimensionOneClause`
states exactly that necessary restriction using actual CPAP and the full
normalized weak 2-quasitrace predicate. The closed theorem
`source_necessary_clause_false` negates it with no assumed witness membership.

The counterexample is A=Complex^3 with pointwise algebra/star and the actual
Pi supremum norm. Its three coordinate traces have a full finite-set/epsilon
CPAP witness, genuine compatible M2 quasitraces, weak continuity and affine
independence. The whole normalized space containing them therefore has
affine-direction finrank >=2, not1. The whole unnormalized space also is not
one-dimensional. Thus either common normalization convention leaves the
necessary printed clause false.

This refutes the original conjunction by one false necessary component.
It does NOT refute the simplex, factor-extreme or closed-extreme components
separately, compute exact dimension2 for the whole set, or classify all traces.
The three coordinate points and their triangle are witnesses inside the full
space, not the definition of that space or a claimed complete classification.

## Formal Object And Definition Dictionary

1. Actual algebra: `A := Fin 3 -> Complex`, actual CommCStarAlgebra and complex
   finite-dimensionality. No Euclidean l2-norm replacement. The spectral order
   used for operator matrices is the canonical order of this same C*-algebra,
   not a new norm or a different algebra.
2. Nuclearity: `HasCPAP` quantifies over every finite subset and every positive
   error, with actual finite-dimensional C*-algebra intermediates, completely
   positive maps at all matrix sizes, norm contractions and norm approximation.
   F=A with identity maps gives zero error. Standard CPAP characterization is
   the stated mathematical nuclearity convention. Lean proves CPAP itself;
   it does not formally prove its equivalence to tensor-norm nuclearity.
3. Quasitrace predicates: `OneQuasitrace` explicitly requires positive cyclic
   star-square values, real/selfadjoint values on selfadjoint elements, the
   selfadjoint real/imaginary decomposition identity, and complex linearity
   on closed unital abelian StarSubalgebras. `TwoQuasitrace` additionally
   supplies an actual OneQuasitrace on the operator-norm M2(A) with corner
   compatibility. Normalization tau(1)=1 is imposed on the BASE functional,
   not incorrectly on the compatible matrix extension.
4. Definition boundary: a general equivalence of this closed/unital test
   formulation with every nonunital/nonclosed-subalgebra axiom presentation
   is NOT claimed. The globally complex-linear trace witnesses satisfy the
   stronger restriction laws on any abelian subalgebra directly. They are
   genuine standard examples, so the dimension obstruction does not depend
   on inventing three functions or a nonstandard Boolean quasitrace test.
   No global Haagerup exact-algebra theorem is assumed.
5. Matrix witness: Q_i(X)=Matrix.trace of the entrywise coordinate-evaluated
   matrix, equal to tau_i(X00)+tau_i(X11), with four star-square normSq terms.
   It is positive, star-preserving, complex-linear and tracial. For the actual
   Matrix.single(0,0,a) corner, Q_i(corner(a))=tau_i(a). Its value on the matrix
   IDENTITY is2, not1; this unnormalized trace is the required convention.
6. Topology: sigma(A,A*) is represented by `WeakSpace Complex A`. Actual
   dual-evaluation continuity proves weak continuity; this is not a confusion
   with WeakDual's weak-star state topology or an unsupported norm-to-weak
   implication. Broader von Neumann sigma-weak dictionary equivalences are
   not new formal results here; the finite-dimensional witnesses require none.
7. Full space: `normalizedTwoQuasitraces`, `weakTwoQuasitraces` and the
   unbundled normalized predicate quantify ALL functionals satisfying their
   laws, never just three points. For commutative A the top closed abelian
   subalgebra forces global linearity. Finite dimension gives continuous
   linearity; uniqueness identifies every unbundled functional in the exact
   full set. `unbundled_space_eq_linear_image` identifies it with an injective
   REAL-linear image of the dual-space set, not an arbitrary bijection that
   might distort affine geometry.
8. Dimension: continuous complex dual finite-dimensionality over Real is
   proved before finrank monotonicity. Coordinate evaluation on projection
   vectors proves real linear, hence affine, independence. The actual
   affineSpan direction contains the two independent differences. There is
   no use of infinite-dimensional finrank=0 to obtain the obstruction.

## Checkpoint Evidence, Not Release Acceptance

The independent research-core PASS binds the unchanged research core
9ae2ed20de6efcb857cace6223892c95f2dc670e7b69ed2a62907ab401c548c7.
It completed68 actual theorem and38 definition/generated-field type/code/axiom
audits; the earlier auxiliary `pp.width` failure remains recorded, with only
that owned audit tool repaired. No failed run is relabelled successful.
These are core records, not final assembled-package/PDF approval.

At the author metadata checkpoint, package reproduction is pending; later
actual results belong in the hash-bound review/validation records. The
3-page compiled PDF and12 author diagnostic tests are separate evidence,
not substitutes for the all-input Lean proofs or full reproduction. The
reproducer protocol audits all nine physical dependency sources and rebuilds
only the own project from an empty build. Shared official caches/toolchain
remain trust inputs; no full-dependency-clean, Linux, bootstrap, OS sandbox,
CI, human endorsement or upstream acceptance is claimed.
