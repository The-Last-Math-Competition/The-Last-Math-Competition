# Disproof of conjecture 00000008551

The geometric partition lattice Pi_3 has characteristic polynomial
(t-1)(t-2). Its distinct consecutive roots 1 and 2 are both positive.
The triangle K_3 has chromatic polynomial t(t-1)(t-2), so the same
obstruction holds for the associated graph normalization.

## Reading and limitation

Both source languages say roots alternate in sign. The undefined phrase
"intersection-disjoint maps" does not specify a separate counting rule.
We cover the standard geometric-lattice characteristic polynomial and
the graph chromatic polynomial of the associated bond lattice. Stanley's
author-hosted EC1 manuscript, equation (3.39) and Exercise 3.108(b)-(c),
provides the standard definitions and bridge. A different intended
polynomial would need its own definition. Coefficient alternation is a
true different statement and is not refuted. The separate modulus
clauses, including the extra Chinese clause, are not needed.

## Formalization

Main.lean constructs a finite bounded modular atomistic lattice and
proves its order isomorphism with Setoid (Fin 3), the full partition
lattice. Rank is verified at every cover. The supplied Mobius function
satisfies the defining bottom-row recurrence, and its uniqueness is
proved. The characteristic polynomial is the finite sum from the
actual lattice, Mobius function and rank; its real roots are exactly 1,2.

`RootSignClause` quantifies over all finite bounded atomistic
upper-semimodular lattices and valid rank/Mobius functions. It asserts
the weak necessary condition that consecutive distinct nonzero real
roots have negative product. `disprove_root_sign_clause` negates it.

Mathlib's actual K_3 Coloring type is equated with embeddings from Fin 3
to Fin q. The cardinality and polynomial-count identity hold for every
natural q. `disprove_graph_root_sign_clause` negates the universal
graph root-sign claim for polynomials that count actual proper colorings.

The paper-only bridge says that every nonempty subset of K_3 is
connected, hence its bond lattice is all partitions. The general
graph/bond-lattice polynomial identity is cited for context, not used
as an unproved Lean premise. Both explicit polynomial claims are proved
in Lean.

## Reproduction

With Lean 4.19.0 and the public-Git pinned dependencies available:

```text
cd lean
lake build
lake env lean -DwarningAsError=true Main.lean
```

Compile main.tex using Tectonic or a compatible LaTeX engine. No
supplementary numerical computation is necessary. The package pins
Mathlib c44e0c8ee63ca166450922a373c7409c5d26b00b.

## Verification and review

The author ran strict Lean with warnings treated as errors. Axiom
reports contain only propext, Classical.choice and Quot.sound. There is
no sorry, admit, native_decide, custom axiom or opaque declaration.
Fresh build, native compiler check, PDF compilation and page inspection
are performed and recorded separately by the coordinator before release.

Developed by a delegated AI agent with a self-review; the coordinating
agent reviews it separately. No independent or external review is
claimed. The source snapshot contains no prior PR or solution for 8551;
the coordinator repeats duplication checks before publication.
