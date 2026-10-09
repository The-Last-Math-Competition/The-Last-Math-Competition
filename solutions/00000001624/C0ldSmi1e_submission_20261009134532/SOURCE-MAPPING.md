# Source-to-formalization mapping

The exact English and Chinese source is retained in `source/ORIGINAL.md`; its SHA-256 is
`53acb6877d3ac08f6469e5f63d03a4de0e22fe4a402699415ee499682705a77a`.

The source asks for a potential with a spectrum that is simultaneously a positive-measure
Cantor set and has no gaps, with an additional singular-measure condition. The obstruction
uses only the three geometric spectral properties. It applies to every real spectrum,
independently of the operator, potential, quasiperiodicity, or spectral measure.

* A real Cantor set is a nonempty compact perfect nowhere-dense subset of the real line.
  `IsRealCantor S` expresses nonemptiness, compactness, Mathlib's `Perfect S`, and
  `interior S = ∅`. `Perfect S` includes closedness, so empty interior here is precisely
  nowhere density. The proof actually applies to every closed set with empty interior;
  compactness and perfection are not extra assumptions on the obstruction.
* “positive-measure” / “正测度” is `0 < MeasureTheory.volume S`: positive Lebesgue measure.
* A bounded internal gap is `(a,b)` with real finite endpoints `a < b`, both endpoints in
  `S`, and the entire open interval disjoint from `S`. This is `IsGap S a b`.
  `IsGap.component` proves that for every `c ∈ (a,b)`, the full connected component of
  `ℝ \ S` through `c` equals `(a,b)`. Thus a gap is not merely a small omitted interval or
  an exterior half-line. `hasNoGaps_iff_ordConnected` proves the standard alternative
  characterization for closed real sets: no internal gaps iff the set contains every
  point between any two of its points.
* “with no gaps” / “且无隙” is `HasNoGaps S := ¬ ∃ a b, IsGap S a b`, absence of every
  internal spectral gap. This differs from having no gap at one chosen reference energy,
  which does not forbid gaps elsewhere. No particular reference energy or restricted
  family of gaps is supplied in either source language. The result does not purport to
  settle a rewritten source with one of those different requirements.
* In `no_source_potential`, `Potential` is an arbitrary type and `spectrum : Potential →
  Set ℝ` is an arbitrary assignment. The two predicates `quasiperiodic` and
  `singularSpectralMeasure` are arbitrary predicates on that type. This universal
  abstraction does not replace either concept by a special weak model: every choice of
  genuine potentials and genuine predicates is an instance, and even allowing both
  predicates to be true of every object does not create a witness. The proof rejects the
  necessary geometric conditions before any other condition matters.
* The Chinese “特征测度奇异” and English “spectral measure is singular” are not assigned
  competing technical meanings in the argument. Any intended extra condition can be
  represented by the unrestricted predicate. The spectral-set contradiction persists.

Stable principal signatures:

```lean
theorem exists_gap_of_positive_volume {S : Set ℝ} (hclosed : IsClosed S)
    (hi : interior S = ∅) (hm : 0 < volume S) : ∃ a b, IsGap S a b

theorem no_source_spectrum :
    ¬ ∃ S : Set ℝ, IsRealCantor S ∧ 0 < volume S ∧ HasNoGaps S

theorem no_source_potential {Potential : Type*}
    (spectrum : Potential → Set ℝ)
    (quasiperiodic singularSpectralMeasure : Potential → Prop) :
    ¬ ∃ V : Potential, quasiperiodic V ∧ IsRealCantor (spectrum V) ∧
      0 < volume (spectrum V) ∧ HasNoGaps (spectrum V) ∧ singularSpectralMeasure V
```

The source's “explicit construction” cannot occur because the required spectrum itself
cannot exist. The conclusion concerns the literal standard real spectral-gap reading in
both supplied languages. The source supplies no alternative definition of “gapless”; a
meaning concerning a selected energy would be a different claim and is not disproved here.
