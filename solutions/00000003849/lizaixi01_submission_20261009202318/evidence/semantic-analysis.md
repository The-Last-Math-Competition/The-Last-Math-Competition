# Independent complete-package review: 00000003849

Reviewer: `/root/crystal_review_3849`.
Review of exact author result SHA256: `01b891b70e27c271abcffed1e3f4fafa07d3081f7223c97eb76a77a06a446a4a`.
Target: `CrystalCounterexample.original_iff_false`.
Verdict: **source-bound semantic pass** for the counterexample, under the ordinary fixed-Cartan-type Kashiwara crystal and crystal-isomorphism conventions.

This is an independent semantic/PDF review. It is not a build receipt, fresh Lean replay, promotion, or local-verification assertion. No package/dependency/state files were edited, no heavy build/gate/ledger operation was run, and no subagent was used.

## Source first and byte binding

I read the complete exact English and Chinese original before reading the candidate self-evaluation, and saved `source-first-checklist.md` first. The independently recomputed source hash is `64d52ffcf021985f7d91e01a777f2ab9eacc31312122f1655c50d0bde49052d9`; `original.md` is an exact byte copy. Both language versions assert the iff about a weight **set**, followed by polynomial-time verifiability. Neither specifies connectedness, irreducibility, normality, a single highest-weight component, a Cartan type, a symmetry center, or an input encoding. The Chinese version adds no limiting hypothesis absent from the English version.

I read the frozen formal source, Main, Audit, root original, all four toolchain/dependency configuration files, obligations, source correspondence, TeX, and every page of the delivered PDF. I independently hashed all twelve manifest-required semantic files and the original, verified all twelve author semantic-file seals against their actual files, and checked the exact author result seal. They all match. `semantic-seals.json` contains the complete exact required map and author checks.

The manager's manifest-v2 changes the submission-folder metadata only. I compared its `expected_source_hashes`, `expected_types`, theorem list and package path with the first manifest: the mathematical contract and bytes are unchanged. The selected target occurs in its checked-theorem list. No inference of mathematical truth is taken from that target name or the author's prior compiler/audit claims.

## Definition and domain attacks

**Potential toy-graph substitution.** `Crystal` has an actual weight map into an actual A2 weight lattice, two colored partial e/f maps using `Option.none` for the nonvertex, integer epsilon/phi maps, the partial-inverse equivalence, both raising/lowering weight and string changes, and the coroot/string equation. The integer-valued specialization embeds into the usual extended-integer definition; the minus-infinity case is absent, rather than assumed false for a witness requiring it. The witness is inhabited with exactly nine concrete vertices. The last universal predicates include both Nonempty and Fintype, so this counterexample is not an empty-domain argument.

I independently checked the defining formulas on all nine vertices, both colors, all inverse-operator pairs, and both directions of every actual edge: 288 exact integer/partial-map assertions pass. `independent-enumeration.json` gives the actual vertex/weight/operator/string data. This is corroboration of the concrete object, not a replacement for the inspected Lean statements and bridges.

**Potential fake A2/root lattice.** The root pair coordinates `(2,-1)` and `(-1,2)`, and simple coroot projections, are the genuine simply connected A2 datum. An independent realization in the real SL3 plane is

`(a,b) -> ((2a+b)/3,(-a+b)/3,(-a-2b)/3)`.

The two roots map to `e1-e2` and `e2-e3`; all six listed roots have squared length 2. The coroot coordinate pair `(r,s)` maps to `r(e1-e2)+s(e2-e3)`. The physical inner-product pairing is exactly `ar+bs`, including all listed root/coroot pairs. Thus the two coordinate copies in `A2.pairing` use dual bases; one must not interpret the weight and coroot pairs as vectors in the same fundamental-weight basis with the ordinary Euclidean metric. The report's phrase “coweight lattice” is best read as the chosen lattice dual to the weight lattice, in simple-coroot coordinates; the explicit coordinates and pairing, rather than that loose terminology, determine the sound root datum. No substantive conclusion depends on identifying a maximal fundamental-coweight lattice with that chosen dual lattice.

The Lean proofs cover Cartan entries, nonzero roots, six distinct paired roots/coroots, pairing 2, and simultaneous reflection closure. Their explicit coordinate definitions agree with the realization above. The GL3 restriction map and central-direction kernel are actually defined and proved; they are not an imported classification axiom.

**Potential disconnected-domain exclusion.** The ordinary definition of a crystal does not require a connected graph. The source does not add that restriction. This particular object is a disjoint union of established fundamental components, which remains a crystal; in Lean it is instantiated directly with every required axiom. The author has not silently replaced a connected original problem with a disconnected one. A conjecture explicitly restricted to connected highest-weight crystals would be a different conjecture and is outside this result.

**Potential seminormality shortcut.** The package checks every one-step endpoint and that applying a fixed-color operator twice is absent. `iteratePartial` uses the actual operators with absorbing none. `Witness.seminormal` treats n=0, n=1, and every n>=2 using a generic absorbing-iteration lemma and string bounds. This is an all-natural-number theorem for exact string lengths, not bounded testing. The independent enumeration confirms the same finite facts and explains the unlimited-n reduction. No additional normality or representation-classification premise is needed for admissibility in the unqualified source domain.

## Actual component, dual and isomorphism correspondence

The standard component has exactly `p0 --0--> p1 --1--> p2`, weights `(1,0),(-1,1),(0,-1)`, reversed raising arrows and the exact corresponding 0/1 string lengths. The GL3 standard weights restrict to these three weights, and both GL3 roots restrict to the actual declared A2 roots. Under the plane realization above these are `e1,e2,e3` with the common central part removed. This identifies the ordinary fundamental A2 component, including its actual arrows and weights, without requiring an unformalized classification theorem.

`Witness.component 0` and `1` reduce to `Standard.crystal`; component `2` reduces to the actually constructed `Standard.crystal.dual`. `component_weight` and `component_operators` establish the concrete inclusion identities for all five maps. The tag/position type is a genuine disjoint union with no vertex identifications between the duplicate components. The third component's arrows are `2 --1--> 1 --0--> 0` in Lean's zero-based colors, with negated weights. Its highest weight is `(0,1)`. Therefore the written `S ⊔ S ⊔ S^vee` description agrees exactly with the formal object.

**Potential reversal-weight mismatch.** `Crystal.dual` reverses e/f, negates weights, swaps epsilon/phi, and derives every structure axiom from those of its argument. I inspected the inverse, raising, lowering and string-equation proofs: they use the original genuine relations plus negation, not an assumed dual-admissibility bridge. Negating the weight is the standard dual convention necessary for reversal to satisfy the same root weight-change equations. Reversing arrows while keeping weight labels unchanged would not be a crystal of this same datum.

**Potential stronger custom isomorphism.** `Crystal.Iso` extends an actual equivalence and preserves weights, each fixed-color operator and both strings. These are the ordinary crystal-isomorphism obligations. For seminormal fixed-root crystals the strings also follow from the operators. Non-isomorphism here uses only the bijection and weight-preservation fields, which are necessary for every ordinary crystal isomorphism, so adding the remaining ordinary fields does not manufacture the obstruction.

`Iso.from_dual_weight_negation` derives `wt(g(v))=-wt(v)` directly from actual dual weight preservation. The reverse direction derives the same equation by a proved double-negation calculation. Neither bridge is a hypothesis added to the final statement. The same underlying vertex type for the dual is a chosen identity identification of the usual copied vertex set, not an assumption of self-duality.

An extra independent attack covers fixed-color arrow reversal even without weight labels: B has two two-edge paths whose successive lowering colors are 0 then 1; its reversed graph has only one. A fixed-color graph isomorphism would preserve that count. This also rules out a mislabeled graph-isomorphism interpretation. If one erases all colors or permits a Dynkin-color permutation, the resulting relation is different from ordinary crystal isomorphism; the source gives no such altered convention. The word “equivalence classes” is read consistently with its actual isomorphism symbol, not as a newly defined quotient identifying every object with its reversal by fiat.

## Set symmetry, non-isomorphism and complete original scope

The actual set range is exactly the six weights `±(1,0), ±(-1,1), ±(0,-1)`. Lean proves a negated-weight witness for every vertex and then proves both membership directions in the **Set.range** using negation involutivity. The symmetry center is 0, a lattice point. Thus it qualifies whether “centrally symmetric” means symmetry about zero, an arbitrary lattice center, or an arbitrary affine center. No center-convention repair is used.

Literal support symmetry forgets multiplicity: the vertices `(0,0)` and `(1,0)` are distinct and both have weight `(1,0)`, while `(2,0)` is the unique vertex of weight `(-1,0)`. The formal theorem `negative_weight_unique` gives an iff for every vertex. Any weight-negating equivalence sends both positives to the unique negative, and its actual injectivity contradicts their explicit inequality. `not_selfDual` and its reverse apply the inspected genuine dual-isomorphism bridges to that exact contradiction. These theorems quantify over every possible crystal isomorphism; no selected map is merely shown to fail.

`SufficientDirection` and `DualityCriterion` are the sufficient direction and iff universalized over a concrete admissible finite A2 subclass. The final Lean proofs specialize any claimed universal statement to the actual witness, use its proven symmetry, and contradict its proven lack of isomorphism. They do not purport to define the whole unrestricted domain in Lean. A concrete member of the original domain refutes the unrestricted universal assertion, so this finite specialization is logically sufficient.

The polynomial-time clause is expressly unproved in the report and PDF. This leaves no obligation for this **refutation**: the full conjecture contains the false iff as a necessary conjunct. The package does not make any complexity claim, substitute an easier computational predicate, or present the failed mathematical criterion as true. Likewise, no quotient-type construction of equivalence classes is needed to establish that the witness's ordinary isomorphism class changes under reversal.

## Reports, Lean source and delivered PDF

The substantive formulas in `SourceCorrespondence.md` and `proof.tex`, and the table/lemma/theorem in the delivered PDF, agree with the actual Lean object. The obligations file is a preimplementation plan; its alternative declaration names or proposed Sum-based implementation are explicitly planned alternatives, while the final correspondence names the actual tag-based implementation. Main imports the formal source. Audit checks the substantive interfaces and asks for transitive axiom output. Reading those commands and absence of admission syntax is not a fresh mechanical audit; the manager remains responsible for actual build/type/axiom/replay evidence.

The toolchain and both dependency manifests use the same Lean 4.33.0 and mathlib revision; the lock contains the eight dependency revisions plus mathlib. I checked the sealed configuration content but did not clone, mutate, or rebuild dependencies. The PDF's preparation-build claims are author-reported historical claims, not grounds for my semantic pass.

I independently rendered the actual frozen PDF with existing Poppler at 135 dpi and inspected all three complete pages using native `view_image` at original resolution. Page 1: title, root/axiom formulas and component introduction are legible. Page 2: every component-table row, dual formula, support, multiplicity lemma, and non-isomorphism theorem is legible and correct; no overlaps or clipped arrows. Page 3: names, version/revision, acceptance limitation and reference are legible; the wrapped URL is intact. Headers, margins and page numbering are consistent; the page-1-to-page-2 sentence continuation is ordinary pagination. No visual defects were found. `pdf-visual.json` binds these observations and every rendered page hash to the exact delivered PDF SHA256.

## Independently consulted mathematical source

I fetched and read [E. Marberg's original HKUST Lecture 5](https://www.math.hkust.edu.hk/~emarberg/teaching/2020/Math6150I/lectures/05_Math6150I_Spring2020.pdf), using Definition 2.1, the component discussion, the standard GL(n) example, Definition 3.4 and Section 4 to check admissibility and conventions. I also inspected the complete primary page containing the standard GL(n) graph as a native image. The reference supplies the extended-integer crystal axioms, allows disconnected crystals, and specifies the dual and usual preserving bijections. The counterexample calculations and all Lean bridges were independently checked above. The exact downloaded reference hash and locations are in `reference-provenance.json`; its byte copy is `marberg-lecture-5.pdf`.

## Disposition

No required mathematical bridge, admissibility condition, semantic seal, full-conjecture refutation obligation, or delivered-PDF defect remains in this package under the stated ordinary conventions. The source leaves some conventions informal; center ambiguity is avoided by this zero-centered example, and the fixed-color/contragredient interpretation follows ordinary crystal usage rather than a hidden additional hypothesis. The pass is for the original unqualified weight-set conjecture, not for a revised connected, multiset, uncolored-graph or color-permuting claim. Proceed to the manager's separately owned mechanical and fresh-replay acceptance checks on these exact bytes.
