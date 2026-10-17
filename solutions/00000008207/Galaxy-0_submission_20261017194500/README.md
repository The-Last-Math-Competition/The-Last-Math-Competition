# TLMC 00000008207: a six-element inverse-monoid counterexample

Let M={0,1,2,3,4,5}, with multiplication min and identity 5. This is an inverse monoid with trivial unit group. Its irreducible unital representations over any field are exactly the six one-dimensional threshold characters χ_t(a)=1 iff t≤a. They are pairwise inequivalent and all restrict to the same trivial unit-group representation. The restriction fiber therefore has cardinality 6, which is not a power of two.

If the representation convention additionally requires the absorbing monoid zero to act as zero, exactly five classes remain. This also refutes the power-of-two law. The Rees-chain parameter need not be interpreted: neither cardinality is 2^k for any natural k.

## Reproduce

Requirements: an installed Lean 4.31.0 toolchain, Python 3 standard library; optionally pdfLaTeX to rebuild the paper. No Mathlib or other Lean dependencies are used.

    ./VERIFY.sh /absolute/path/to/lean-4.31.0/bin
    ./build_pdf.sh

On a minimal TeX image with a prebuilt pdflatex.fmt, its directory can be passed as the first build_pdf.sh argument. The helper uses already installed TeX/font sources and does not install software.

## Actual formal objects

- Monoid.lean proves the six-element min operation's associativity, identity, unique inverses and exact unit set, and classifies multiplicative field-valued characters.
- Representation.lean defines arbitrary finite-dimensional coordinate vector spaces K^n, linear unital monoid actions, actual subspaces and invariance, and irreducibility. It proves central idempotents are zero or identity, irreducible dimension is one, and all irreducibles are threshold characters.
- Main.lean defines two-sided linear intertwining isomorphisms, the restriction condition on every unit, and the quotient of the actual restriction fiber by representation equivalence. It proves explicit bijective enumerations by Fin 6 and, in the zero-preserving case, Fin 5. It proves cardinality uniqueness and then excludes every power-of-two cardinality.

Main theorems:

- TLMC8207.conjecture8207_false
- TLMC8207.contracted_conjecture8207_false

## Formal boundary and mathematical scope

Lean quantifies over every field and represents finite-dimensional vector spaces in coordinates, K^n. No classification is assumed. The code does not construct a complex-number library, an arbitrary-carrier vector-space library, or the choice of coordinates for an abstract finite-dimensional vector space.

The handwritten proof handles arbitrary algebraic irreducible representations as well: the span of the orbit of any nonzero vector under a finite monoid is a nonzero finite-dimensional invariant subspace, hence the whole space. Choosing a basis then gives the coordinate model. This finite-orbit reduction and abstract coordinatization are explained in the paper, not claimed as separately formalized Lean results.

Only the power-of-two restriction-fiber conjunct is refuted. No claim is made about the source's centralizer-image description or its smallest-example assertion. The representation convention is ordinary unital linear representations in End(V), not maps forced to take all monoid elements to invertible operators. Both ordinary and zero-preserving conventions are covered.

## Validation

- Lean 4.31.0 build and strict warning-free elaboration pass.
- Independent leanchecker replay passes for Monoid, Representation and Main.
- Audit.lean audits all 47 authored theorems; only standard propext, Classical.choice and Quot.sound occur.
- No admitted proofs, native_decide, custom axioms, external oracle or kernel bypass.
- verify.py independently checks all monoid inverse/unit equations and exhausts scalar characters over F2/F3/F5. It also enumerates all 96 two-dimensional F2 representations and checks each has a proper invariant line.
- Three-page PDF compiled from the included LaTeX and visually inspected.

This elementary counterexample is self-contained. A standard supporting reference is Ganyushkin, Mazorchuk and Steinberg, “On the irreducible representations of a finite semigroup,” arXiv:0712.2076v2, Corollary 9. It is not used as a Lean axiom.

The source statement is in source.md. Eligibility details are in ELIGIBILITY.md. Verification output is in logs/. SHA256SUMS covers the delivered files.
