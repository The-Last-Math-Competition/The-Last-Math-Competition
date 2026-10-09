# Source correspondence: 00000003849

The exact English/Chinese source is `sources/00000003849.md`. Its independently verified SHA256 is `64d52ffcf021985f7d91e01a777f2ab9eacc31312122f1655c50d0bde49052d9`. The source is unchanged. The initial scout result and its finite-map probe are prior evidence only; the present package proves all relevant crystal structures and bridges itself.

## Outcome and scope

The package supplies an admissible finite type-A2 Kashiwara crystal whose **weight set** is centrally symmetric about zero but which is not isomorphic to its contragredient dual. It refutes the sufficient direction of the original iff, hence the iff and its conjunction with the algorithmic clause. It establishes no polynomial-time complexity result.

Both languages say weight set, not multiset or character, and neither requires connectedness or irreducibility. Finite crystals are valid examples of the unqualified source domain, so refuting the criterion already on nonempty finite-type A2 crystals refutes the wider statement. Restricting to this subclass is only for the counterexample; no stronger assumption is used to make a universal theorem vacuous. The concrete vertex type has nine elements and inhabited instances.

## Fixed crystal/duality conventions

We use standard fixed-color, weight-preserving crystal isomorphisms. The source calls arrow reversal the dual crystal. To remain a crystal for the same root datum, the standard contragredient convention also negates weights and exchanges epsilon/phi. `Crystal.dual` implements those changes and proves every crystal axiom. A convention that reverses arrows while leaving weights unchanged would not satisfy the same weight-change axioms; it is not silently used.

`Crystal.Iso` extends a genuine equivalence and has five actual preservation fields: wt, e, f, epsilon, phi. It therefore includes the usual labeled directed crystal graph information. Color permutation or an unlabeled directed-graph equivalence is not the standard crystal isomorphism used here. `Iso.from_dual_weight_negation` and `Iso.to_dual_weight_negation` derive their equations from those concrete fields, with no assumed bridge.

The reference conventions can be checked against [Marberg's Lecture 5](https://www.math.hkust.edu.hk/~emarberg/teaching/2020/Math6150I/lectures/05_Math6150I_Spring2020.pdf), Definitions 2.1 and 3.4 and Section 4. No reference theorem is imported as an axiom.

## Actual A2 data and admissibility

`A2.Weight` is the free abelian lattice Z x Z in fundamental-weight coordinates. Simple roots are (2,-1) and (-1,2); simple coroot pairings are the first and second coordinates. `cartan_entries` proves the A2 matrix. `rootVector` and `corootVector` enumerate all six corresponding roots/coroots. Lean proves their distinctness, pairing value 2, simple reflection formulas and involutions, and simultaneous root/coroot reflection closure (`paired_reflections_closed`). The pairing is the standard dot product of the two Z² lattices; `pairing_fundamental_basis` checks its coordinate basis values. These data identify a real A2 Cartan/root lattice, not an arbitrary weighted graph with chosen root labels.

`Crystal` implements the finite-type specialization of the standard abstract Kashiwara axioms: epsilon/phi are integers, so no minus-infinity value occurs. All ordinary crystal identities for those values are represented explicitly: e/f partial inverses; raising and lowering weight changes; both raising and lowering string changes; and phi = epsilon + coroot pairing. `Option.none` is the distinguished nonvertex. This subclass embeds in the standard definition with integer-or-minus-infinity string values; no minus-infinity clause has an unproved case in this construction.

`Witness.crystal` supplies every axiom with a checked proof. `iteratePartial` iterates the actual e/f operators with none absorbing. `Witness.seminormal` proves for **every natural n**, not just a test horizon, that the n-th operator iterate is nonzero exactly when n does not exceed the corresponding epsilon/phi. Thus the example has genuine exact string lengths, not flags substituted for them.

## Precise standard-component correspondence

The standard three-vertex component is defined with arrows p0 --color 0--> p1 --color 1--> p2 and weights (1,0),(-1,1),(0,-1). All other lowering arrows are absent, all raising arrows are their reverses, and string lengths are 0/1 according to those actual arrows. This is the usual fundamental graph B(omega1), with Lean colors 0,1 corresponding to mathematical colors 1,2.

For an explicit conventional correspondence, `gl3Basis` gives the three GL3 standard weights e1,e2,e3, and `restrictWeight(u)=(u1-u2,u2-u3)` maps them to the stated A2 weights. `gl3_roots_restrict` maps the conventional GL3 simple roots to the chosen A2 roots; `central_direction_killed` checks the central direction; `Standard.standard_weight_correspondence` checks the vertex weights. The arrow graph is exactly the standard GL3 graph under the same vertex identification. The component's highest weight is proved to be (1,0); its actual dual has highest weight (0,1), giving the usual dual fundamental graph B(omega2).

The witness tags components by c in Fin3 and positions by p in Fin3. `Witness.component 0` and `component 1` equal `Standard.crystal`; `component 2` equals its actual `dual`. `component_weight` and `component_operators` prove the exact inclusion identities for wt/e/f/epsilon/phi. Accordingly, the witness is a genuine disjoint union of two standard fundamental components and one dual fundamental component. No normality or representation-theoretic classification hypothesis is assumed. The package proves abstract crystal admissibility and seminormality directly; the traditional fundamental-component names are supported by the explicit graph/weight correspondence above. It does not purport to formalize quantum-group modules or a general classification theorem.

## Original-clause map

| Source clause/object | Lean object or theorem | Status |
| --- | --- | --- |
| Crystal B | `Crystal`, `Witness.crystal` | Explicit data and all finite-type Kashiwara axioms proved. |
| Arrow reversal giving dual | `Crystal.dual` | Generic actual dual construction with wt negated, e/f and epsilon/phi exchanged; all axioms derived. |
| B-dual isomorphic to B | `Crystal.Iso`, `Witness.not_selfDual` | Actual weight/color/operator/string preserving isomorphism excluded. Reverse direction also excluded. |
| Weight set | `Set.range Witness.crystal.wt` | A genuine set range, never a multiset proxy. |
| Centrally symmetric in weight lattice | `CentrallySymmetric`, `witness_centrallySymmetric` | Actual reflection c+c-w condition with c=0 proved on the set range. If the source allows half-lattice centres, centre zero still qualifies. |
| Iff criterion | `DualityCriterion`, `original_iff_false` | Its universal statement is refuted in an admissible finite A2 subclass. |
| Sufficient direction | `SufficientDirection`, `original_sufficient_direction_false` | Explicitly false via the nine-vertex crystal. |
| Equivalence classes invariant under reversal | Actual `Iso` for the witness | Its dual equivalence class differs; no separate quotient construction is necessary for an isomorphism counterexample. |
| Polynomial-time verification | No complexity declaration | Not established or substituted; the necessary iff conjunct is already false. |

## Proof bridge and set/multiplicity distinction

The set support is {±(1,0), ±(-1,1), ±(0,-1)}. Its zero-centred symmetry is first proved at the vertex level and then lifted to `Set.range` in both directions, including negation involutivity. Symmetry of a set forgets how many vertices realize each weight.

`firstPositive=(0,0)` and `secondPositive=(1,0)` are distinct and both have weight (1,0). `negative_weight_unique` proves that `(2,0)` is the unique vertex of weight (-1,0). A weight-negating equivalence must send both positive vertices to that one negative vertex and contradict injectivity. `Witness.not_selfDual` applies the actual dual-isomorphism bridge to this proved obstruction, rather than assuming the bridge. `original_iff_false` applies any alleged universal iff to this concrete nonempty crystal and reaches that contradiction.

## Portable preparation and acceptance boundary

`package/lean-toolchain` pins official Lean 4.33.0. `lakefile.toml` and the git `lake-manifest.json` pin mathlib revision `db584cd6d46c92f209a44c0f1c829460d327499d` and all eight unchanged dependencies, also recorded in `dependencies.lock.json`. `Main.lean` imports the formal source. `Audit.lean` prints concrete interfaces and all relevant transitive axiom dependencies.

Worker preparation used only subprocess-local LEAN_PATH pointing to fixed read-only shared package oleans plus this package's own output directory. Source, Main and Audit compiled successfully with no final warning. All final printed axiom dependencies are limited to propext, Classical.choice, Quot.sound. The earlier unused-simp warning was corrected and its original log retained. Worker preparation is not locally_verified status or manager acceptance.

The genuine `proof.pdf` is compiled from `proof.tex` using existing Tectonic 0.17 and a private byte copy of the existing cache, preserving the rule that writes stay in this assigned output directory. Missing cached booktabs, one nested-script font and size10 caused saved failures; the final source uses cached 11pt fonts with unnested equivalent notation and ordinary table rules. The final compiler returns zero with no TeX layout warning; its stderr still has a nonfatal Fontconfig default-config notice. Poppler rendered all three pages successfully, and native visual inspection found clear formulas, aligned table/headers and no missing glyphs, clipping or overlap. Compiler and rendering logs are retained. The PDF follows the source construction, actual dual bridge and original-clause limitations.

The independent source-semantic review and manager-owned clean deterministic/fresh/PDF gate remain the next required checks. The final result recommends gate/review priority only and makes no acceptance assertion. No further mathematical/formalization obligation is knowingly left in this counterexample route; source interpretation and admissibility are reviewable from the frozen files above.
