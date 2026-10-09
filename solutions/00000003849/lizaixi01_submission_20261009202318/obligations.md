# Formalizer obligations before implementation

Task: dev-author-3849; source ID 00000003849, expected SHA256 64d52ffcf021985f7d91e01a777f2ab9eacc31312122f1655c50d0bde49052d9. Original claim: a crystal is isomorphic to its arrow-reversal dual iff its weight set is centrally symmetric, with a polynomial-time criterion. Neither language requires connectedness, irreducibility, or weight multiplicity symmetry.

## O1. Faithful A2 root/weight data and crystal axioms

Role: establish actual admissibility rather than a finite weight proxy. Use weight lattice Z x Z in the fundamental-weight basis; roots alpha0=(2,-1), alpha1=(-1,2), and simple coroots the coordinate projections. State and prove `A2.cartan_entries`, `A2.reflection_involutive`, and finite-root reflection closure; then `structure Crystal (V : Type)` with actual weights, partial raising/lowering operators, integer epsilon/phi, inverse, both raising/lowering weight and string relations, and the coroot/string relation. This is the finite-type specialization of the standard Kashiwara axioms (no minus-infinity string values); the explicit witness will be seminormal and nonempty.

Checked dependency evidence: prior scout successfully elaborated Fintype/Fin/Prod, integer-pair arithmetic, Option partial maps and Equiv injectivity using pinned Lean 4.33/mathlib. Final acceptance method: elaboration, printed transitive axioms, and source-semantic check of this specialization. No admission predicate is assumed.

## O2. Actual dual and crystal isomorphisms

Role: formalize the original B-dual object and its isomorphism, not a weight-only stand-in. Exact planned declarations: `def Crystal.dual (C : Crystal V) : Crystal V`, with wt negated, e/f exchanged, epsilon/phi exchanged and all axioms proved; `structure Crystal.Iso (C : Crystal V) (D : Crystal U)` extends `V ≃ U` and preserves wt/e/f/epsilon/phi; `theorem Crystal.Iso.dual_weight_negation (g : C.Iso C.dual) : ∀v, C.wt (g v) = -C.wt v`. Provide the reverse-direction bridge used for `C.dual.Iso C` as in the source order.

Checked dependencies: Equiv, Option.map, additive negation identities. Acceptance: inspect actual Iso fields and dual proof, no unproved bridge hypothesis, no axioms or sorry.

## O3. Actual nine-vertex admissible witness and standard components

Role: instantiate O1 concretely. Exact planned declarations: `def standard : Crystal (Fin 3)` with the fundamental chain; `def disjointUnion (C : Crystal V) (D : Crystal U) : Crystal (Sum V U)` or an equivalent component-tag construction; `def witness : Crystal (Fin 3 × Fin 3)` with first two tags standard, last tag standard.dual. Prove raising/lowering and finite string axioms with explicit finite kernel reduction, and prove the component inclusions commute with wt/e/f/epsilon/phi. Prove actual string-length seminormality or an exact equivalent characterization for strings of maximum length one. Do not claim normality unless separately established or provide precise standard-component correspondence.

Checked dependencies: scout actual e/f and weight/string calculations, finite decidability. Acceptance: no premise standing in for normality; component correspondence and numerical root data inspected against the standard A2 fundamental crystal.

## O4. Set-range central symmetry and original sufficient-direction refutation

Role: formalize the exact weight **set** condition and actual crystal non-isomorphism. Planned declarations: `def CentrallySymmetric (s : Set A2.Weight) : Prop := ∃c, ∀w, w ∈ s ↔ (c+c-w) ∈ s`; `theorem witness_centrallySymmetric : CentrallySymmetric (Set.range witness.wt)` with c=0; `theorem witness_not_selfDual : ¬ Nonempty (witness.dual.Iso witness)`; and a universal sufficient-direction predicate over nonempty finite-type A2 crystals together with `theorem original_sufficient_direction_false : ¬ SufficientDirection`. A finite subtype count/equivalence contradiction derives from two vertices of weight (1,0) and one of weight (-1,0), and O2 provides the real crystal bridge.

Checked dependencies: successful scout no_weight_negating_equiv; Set.range needs direct finite witness lifting. Acceptance: actual Set.range, quantification over genuine nonempty crystals, explicit admissible counterexample, no false premise. Disclose no polynomial-time claim is established; an iff conjunct is already false.

## O5. Portable package and source/PDF correspondence

Role: deliver reviewable frozen semantic artifacts. Outputs: pinned `lean-toolchain`, `lakefile.toml`, `lake-manifest.json`, `dependencies.lock.json`, `Main.lean`, source Lean, `SourceCorrespondence.md`, `proof.tex`, actual compiler `proof.pdf`, strict formalizer `result.json`, read/build/PDF/validation logs. Dependencies use pinned official revisions; shared package sources and cache remain read-only. Preparation uses subprocess-local LEAN_PATH, direct official lean.exe, and only local build outputs. Manager makes clean private dependency copies and owns deterministic/fresh/PDF gate.

Acceptance: schema and relative-path checks; local preparation builds and axiom audit; Tectonic 0.17 with existing cache, rendered PDF inspection; final source-faithful independent review and manager acceptance. Preserve all failed build logs. No external submissions or other-agent access.
