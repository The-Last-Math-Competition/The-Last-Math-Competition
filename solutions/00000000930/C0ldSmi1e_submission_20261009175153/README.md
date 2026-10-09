# Conjecture 00000000930: disproof

The ordinary unweighted Bergman shift has exactly two closed complex reducing
subspaces: the zero space and the whole Bergman space. Thus its reducing-subspace
lattice does not have continuum cardinality. This refutes an explicit necessary
clause of the conjecture; no unspecified Blaschke-product indexing is substituted.

The report source is `proof.tex`. The full Lean project is in `lean/`.
The matching five-page report is `proof.pdf`.

## Build and inspect

With Lean managed by elan, run from `lean/`:

```sh
lake build
```

The project pins Lean 4.19.0 and Mathlib commit
`c44e0c8ee63ca166450922a373c7409c5d26b00b` (v4.19.0), with the inherited
dependency revisions recorded in `lake-manifest.json`. Warnings are errors.
The default target includes all nine proof-project source modules under `lean/`
and prints the semantic definitions, theorem signatures, and axiom audit.

The two final declarations are:

```lean
Bergman930.reducing_cardinality :
  Cardinal.mk Bergman930.ReducingSubspace = 2

Bergman930.not_continuum :
  Cardinal.mk Bergman930.ReducingSubspace ≠ Cardinal.continuum
```

## Source fidelity

`ORIGINAL.md` is the exact bilingual problem supplied to the independent author.
Its SHA-256 is
`0772dbdb34f4b8cc17757d7ebd387d5b7bc31c59ae456e1473f40fcd28e0111d`.

The space consists of actual holomorphic functions on the open complex unit
disk that are square integrable for ordinary planar area `dx dy`. Zero extension
outside the disk makes their representation unique. No coefficient-space
replacement is assumed. A proved injective map identifies these functions with
a closed subspace of genuine area-L², and the project proves the integral
inner-product identity and completeness of that subspace. Multiplication by z
is proved to be a contraction and transported through this exact identification.

`IsReducing` quantifies over all complex submodules in that inherited L² geometry,
requiring relative closedness and invariance of the subspace and its orthogonal
complement. `isReducing_iff_adjoint` proves equivalence to invariance under the
operator and its Hilbert-space adjoint. The two-element classification and its
Boolean bijection are theorems about that full subtype, not its definition.

The direct proof is local division in A²: `(f-f(w))/(z-w)` remains holomorphic
and square integrable. Every complex-linear map commuting with M_z therefore
acts pointwise by its value on 1. For an idempotent, that holomorphic multiplier
is identically 0 or identically 1. Hilbert-space orthogonal decomposition applies
to every closed reducing subspace because completeness is proved, not assumed.

## Validation and trust boundary

`validation/author-fresh-build.log` preserves exact author verification commands,
working directories, import search paths, raw output, and exit codes. The fresh
build elaborated every owned module into a new output directory, with warnings
as errors. All 16 inspected declarations have only the standard axiom dependencies
`propext`, `Classical.choice`, and `Quot.sound`.

The local verification trusted existing compiled objects of the pinned standard
libraries. Three missing standard Mathlib objects were freshly compiled from their
unchanged pinned sources: `RemovableSingularity`, `UniformLimitsDeriv`, and
`LocallyUniformLimit`. Every owned module was freshly compiled. The final project
uses canonical Mathlib imports and contains no renamed library copies, precompiled
objects, dependency cache, unused exploratory source, or numerical computations.
Absolute local paths occur in forensic logs only; they are not project dependencies.

A normal `lake build` also completed successfully (exit 0) in a separate local
copy of this exact project, using private copies of the same pinned dependencies.
Its raw output is `validation/author-lake-build.log`. The build compiled the three
previously missing standard modules and all nine owned modules with the canonical
import graph; it emitted no warnings.

`validation/source-audit.txt` records the source scan and build/axiom audit.
`SHA256SUMS.json` records the final submission files, including the report source and PDF.


## Independent pre-submission review

`validation/semantic-review.md` records independent mathematical report/source
scrutiny, with its precise file bindings and scope. `validation/engineering-review.txt`
records the independent fresh Lake build and transitive dependency audit.
To rerun the additional positive audit from `lean/`, after `lake build`, run:

```sh
lake env lean -DwarningAsError=true ../validation/EngineeringAudit.lean
```

This separate verification module checks all 59 explicit mathematical declarations
and their dependencies, and checks the concrete final theorem signatures. It adds
no axiom or premise to the proof. Its successful output is in
`validation/engineering-audit.log`. The deliberate failing control used to test the
checker stayed outside this submission. No auxiliary numerical programs are needed.

The report and matching PDF were compiled and every page visually checked.
These are local pre-submission checks; acceptance remains the maintainers' decision.
