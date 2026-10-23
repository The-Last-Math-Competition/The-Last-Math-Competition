# Counterexample to 00000002761

An explicit homogeneous degree-eight polynomial in the actual free associative algebra over `Q` is central and not an identity for `M₃(Q)`. Every evaluation is scalar; the displayed matrix-unit substitution evaluates it to `2 I₃`. Its support is nonempty, all words have length eight, and its constant coefficient is zero.

The construction starts from an explicit cubic weak identity on trace-zero matrices, differentiates its marked words, and uses the trace pairing to obtain a scalar-valued polynomial. Substituting an actual commutator for the trace-zero variable gives a polynomial in six unrestricted matrix variables. The weak identity is established on the actual matrix-unit basis and extended by genuine multilinearity and conjugation.

The degree is computed from coefficient support in the monoid algebra of the free monoid, connected by the canonical equivalence and evaluation bridge to Mathlib's native `FreeAlgebra`. The minimum ranges over every positive-degree central polynomial with any finite number of variables. The explicit witness proves this nonempty degree set has minimum at most eight, contrary to the proposed value `3² = 9`. The proof does not claim the exact minimum or address the undefined moduli and generation clauses.

The accompanying submission contains the complete bilingual conjecture, LaTeX and rendered PDF, pinned Lean project, exhaustive namespace axiom checks, original build and fresh-kernel receipts, actual process-affinity samples, and a SHA256 manifest. The formula is independently derived; no unread historical formula is cited as its source.
