# Three Coordinate Quasitraces on C^3 Refute the Universal Dimension-One Clause

Conjecture: 00000000918. Solver: idealistichacker. AI-assisted mathematics,
implementation and documentation. Mathematical verdict: **disproved**, by
refuting the necessary universal real-affine-dimension-one clause only.
No assertion that the factor-trace or closed-extreme-set clauses are false.

## Source And Precise Conclusion

`source.md` is the exact original bilingual UTF-8 Git blob from organizer
commit `b355e42906e6eaf52bc7e9d005e0ef02d8aa7400`, blob
`dadc2ef65f6a57feb3def12febafd66299b1f918`, raw SHA-256
`326b3e1b5e32b83188a2648a49b823f81b6d8ae7a0a6af46d08a71338998676f`.
Comparison with the organizer working file permits CRLF-to-LF normalization
only, without trimming or other textual rewriting. Neither language assumes
a simple/factor algebra or restricts the space to a chosen trace ray or segment.
The source's factor-trace language concerns extreme points, not a restriction
that the underlying algebra itself be a factor.

Take the actual unital commutative C*-algebra `A := Fin 3 -> Complex` with
pointwise operations, coordinate conjugation and the Pi **supremum norm**.
It is not EuclideanSpace with its l2 norm. The three coordinate evaluations
are genuine positive, normalized, weakly continuous 2-quasitraces. They are
affinely independent over Real. Consequently the full normalized weak
2-quasitrace space has real affine-span direction dimension at least two,
and in particular not one. The full space without normalization also has
dimension different from one.

The closed Lean conclusion is
`Quasitrace918.source_necessary_clause_false :
  Not Quasitrace918.FiniteCommutativeDimensionOneClause`.
This quantified clause already restricts the printed universal claim to
finite-dimensional commutative CPAP C*-algebras, where the counterexample
lives. Falsifying that necessary restriction refutes the original conjunction;
it does not claim a classification of quasitraces on every nuclear algebra.
Only a lower bound >=2/not1 for the full space is claimed, not exact dimension
two, identification of the entire space with a triangle, or an extreme-point
classification. See `statement-alignment.md` for the definition dictionaries.

## Genuine Formal Bridges

The five mathematical modules, in dependency order, are:

1. `NuclearCPAP`: finite-set/positive-epsilon CPAP quantifiers, an actual
   finite-dimensional C*-algebra F and two actual completely positive
   contractions. F=A and id/id give zero approximation error. Identity
   amplification preserves actual matrix positivity at every size. `HasCPAP`
   is not an abbreviation for finite-dimensionality. The standard CPAP
   characterization of nuclearity is the disclosed mathematical dictionary;
   Lean does not reprove the tensor-norm/CPAP equivalence.
2. `TraceTriangle`: actual sup-norm C^3, bundled continuous complex-linear
   coordinate maps, positivity/unit/tracial/star and contraction laws.
   `WeakSpace Complex A` is the actual sigma(A,A*) topology, not an unrelated
   weak-star topology on the state dual. Real finite-dimensionality of the
   continuous complex dual is proved BEFORE finrank monotonicity. Evaluating
   at coordinate projections proves actual real affine independence, not
   merely a hard-coded Boolean or an unattached determinant.
3. `MatrixExtensions`: actual operator-norm `CStarMatrix (Fin 2) (Fin 2) A`,
   with the canonical spectral order on the same base algebra. The extension
   Q_i(X)=tau_i(X00)+tau_i(X11) is the actual unnormalized `Matrix.trace`
   after entrywise evaluation. It is positive, complex-linear, star-preserving
   and tracial; its star-square is a sum of four squared absolute values.
   Q_i(corner(a))=tau_i(a), and **Q_i(1_2)=2**, not1. Raw Matrix entrywise
   sup norm is not substituted for the C*-matrix operator norm.
4. `QuasiTraceModel`: explicit positive/cyclic star-square, selfadjoint-value,
   selfadjoint real/imaginary decomposition and closed unital abelian
   StarSubalgebra-linearity laws, plus a compatible genuine M2 extension.
   Globally complex-linear positive star-preserving trace witnesses satisfy
   these laws. Their linear restrictions also work on nonunital/nonclosed
   abelian subalgebras. No general equivalence between every conceivable
   quasitrace axiom system is asserted. On this commutative A, the whole top
   closed abelian subalgebra forces any packaged OneQuasitrace to be globally
   linear; finite dimension proves continuity and a UNIQUE continuous-dual
   representation. Additivity implies the source's subadditivity with equality
   where its real/positive order interpretation is meaningful.
5. `Main`: coordinate membership in the FULL normalized and unnormalized
   weak 2-quasitrace predicates, not a set defined as three displayed points.
   The unbundled normalized functional space is exactly the image under an
   injective REAL-linear coefficient map from the dual-space set, preserving
   its natural affine geometry rather than using an arbitrary bijection.
   Actual CPAP and all membership premises are discharged in the closed
   counterexample and necessary-clause negation.

`Check.lean` imports Main and contains exactly the sorted 68 theorem
#check/#print axioms pairs. `CheckDefinitions.lean` independently contains
the sorted 38 definition/instance/generated-constructor-and-field pairs.
Both names lists exactly match `submission.json`. Allowed axiom names are
only `propext`, `Classical.choice`, `Quot.sound`; syntactic universe arguments
on these same names do not expand the allowlist.

## Reproduction Interface And Checkpoint Evidence

Lean is pinned to `leanprover/lean4:v4.33.1`; Mathlib to
`0df444a360eaa60ab8c11dca51a86af692955474`. The lock fixes all nine complete
Git dependency records, not just Mathlib. The exact default roots are
NuclearCPAP, TraceTriangle, MatrixExtensions, QuasiTraceModel, Main, Check,
CheckDefinitions, with warnings as errors.

The public reproduction interface is:

Use ordinary Python mode. `-O`/`-OO` are rejected before source or path IO,
and child optimization flags are removed so diagnostic assertions execute.

```text
python reproduce.py --lake <installed4.33.1lake> --repo <organizercheckout>
python reproduce.py --lake <installed4.33.1lake> --repo <organizercheckout> --skip-update
```

Default mode may prepare pinned public dependencies online. Explicit
`--skip-update` instead requires existing exact offline physical checkouts;
it never waives source, dependency, build or audit gates. The required protocol
resolves all nine physical checkout boundaries, checks origin/source URL,
exact locked HEAD, complete index against the HEAD tree, every tracked raw
byte and path safety BEFORE and AFTER reproduction. Only exact canonical
own-project `.lake/build` is cleared; authored module outputs are not reused.
The project is rebuilt from an empty own build through Main, and the two
query entries must emit all68 theorem and38 definition actual types/axioms.

Three individually pinned tracked symlink-text entries may be inert ordinary
Windows files with exact expected blob bytes/OIDs. These are narrow source
representation exceptions, never executable links or a general gitlink/submodule
waiver. Real symlinks, junctions and reparse aliases remain rejected. Unknown
link modes/paths, redirected .git metadata, index/tree differences, or tracked
byte changes cannot be accepted from a clean Git status alone.

Independent exact Gaussian-rational diagnostics exercise C^3/M2 operations,
positive star-squares, cyclic traces even on noncommuting matrices, corner
compatibility, extension identity value2 and an affine minor. The 12 author
diagnostic tests previously ran successfully; finite diagnostics are not
generic Lean proofs or assembled-package validation. Reproduction also runs
the package's unit and safety regressions. This is an analysis counterexample,
not an algorithmic catalogue: no successful #eval computation is a gate here.

**Author checkpoint: package reproduction pending.** Later actual outcomes
belong in the hash-bound independent review and validation records for the
final assembled content. The metadata task does not manufacture their result.
The independent research-core review records PASS for the five frozen sources,
all68 theorem and38 definition/field type/code/axiom audits. It retained the
earlier owned auxiliary failure (`unknown pp.width`) and repaired only that
query tool; successful mathematical sources were not rewritten or rebuilt.
That core PASS is not final package/PDF five-gate review or coordinator validation.

Research-core freeze:
`9ae2ed20de6efcb857cace6223892c95f2dc670e7b69ed2a62907ab401c548c7`.
It is not the final coordinator submission content hash. The actual included
`main.pdf` has three pages, 58094 bytes, SHA-256
`14ddb1f0e3f1522ba518a1d9f791f900ff037d3ad30069533a20aca8dab8ba0d`;
`main.tex` SHA-256 is
`a55dbc94ec6a2f54dee3bc603cc015d0cd9ee24d1b18cf6263713057bcf981cd`.
Author deterministic builds/visual checks do not substitute for independent
final PDF regeneration, byte comparison and page-by-page review.

## Limitations And AI Disclosure

The proof uses the standard nuclear C*-algebra/CPAP and complex quasitrace
conventions described in the manuscript; those dictionaries are not new
formal tensor-nuclearity or general quasitrace-classification theorems.
No exact dimension of the whole space, affine homeomorphism to a simplex,
factor-trace or closed-extreme-set classification, or simplicity/factor
restriction is asserted. The ordinary traces are nonfaithful but legitimate
normalized quasitraces; the printed source imposes no faithfulness condition.

Installed official dependency caches and the fixed compiler remain shared
trust inputs. Own-project clean reproduction is not a full-dependency-clean
rebuild, empty-machine bootstrap, Linux execution, hosted CI or OS sandbox.
Author and independent AI checks are not human endorsement; shared tooling
and cache correlation are disclosed. No upstream acceptance, first-solve
credit, human/expert endorsement, affiliation, score, rank or award is claimed.
