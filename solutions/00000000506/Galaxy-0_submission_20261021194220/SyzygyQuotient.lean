import BettiSupport

namespace TLMC506

def syzygyOf (p : Poly) : Syzygy := ⟨koszul p, koszul_syzygy p⟩
def syzygyParameter (s : Syzygy) : Poly := dropY s.val.1

@[simp] theorem syzygyParameter_of (p : Poly) : syzygyParameter (syzygyOf p) = p := by
  apply Poly.ext; intros; rfl

@[simp] theorem syzygyOf_parameter (s : Syzygy) : syzygyOf (syzygyParameter s) = s := by
  apply Subtype.ext
  exact (syzygy_parametrization s.property).symm

def syzygyAdd (s t : Syzygy) : Syzygy :=
  syzygyOf (add (syzygyParameter s) (syzygyParameter t))
def syzygyScale (c : Bool) (s : Syzygy) : Syzygy :=
  syzygyOf (scale c (syzygyParameter s))
def syzygyZero : Syzygy := syzygyOf zero

theorem syzygyAdd_val (s t : Syzygy) :
    (syzygyAdd s t).val = pairAdd s.val t.val := by
  change koszul (add (syzygyParameter s) (syzygyParameter t)) = pairAdd s.val t.val
  rw [koszul_add]
  have hs := congrArg Subtype.val (syzygyOf_parameter s)
  have ht := congrArg Subtype.val (syzygyOf_parameter t)
  change koszul (syzygyParameter s) = s.val at hs
  change koszul (syzygyParameter t) = t.val at ht
  rw [hs, ht]

theorem syzygyScale_val (c : Bool) (s : Syzygy) :
    (syzygyScale c s).val = pairScale c s.val := by
  change koszul (scale c (syzygyParameter s)) = pairScale c s.val
  rw [koszul_scale]
  exact congrArg (pairScale c) (congrArg Subtype.val (syzygyOf_parameter s))

def syzygyResidue (s : Syzygy) : Bool := (syzygyParameter s).coeff 0 0

/-- The quotient relation is actual difference (equal to sum in F₂) in mK. -/
def SyzygyResidueEq (s t : Syzygy) : Prop :=
  InMaximalTimesSyzygy (pairAdd s.val t.val)

theorem syzygy_residue_eq_iff (s t : Syzygy) :
    SyzygyResidueEq s t ↔ syzygyResidue s = syzygyResidue t := by
  unfold SyzygyResidueEq
  rw [syzygy_parametrization s.property, syzygy_parametrization t.property,
    ← koszul_add, koszul_in_maximal_iff]
  exact xor_eq_false_iff _ _

def syzygySetoid : Setoid Syzygy where
  r := SyzygyResidueEq
  iseqv := ⟨
    fun s => (syzygy_residue_eq_iff s s).mpr rfl,
    fun {s t} h => (syzygy_residue_eq_iff t s).mpr ((syzygy_residue_eq_iff s t).mp h).symm,
    fun {s t u} hst htu => (syzygy_residue_eq_iff s u).mpr
      (((syzygy_residue_eq_iff s t).mp hst).trans ((syzygy_residue_eq_iff t u).mp htu))⟩

abbrev SyzygyQuotient := Quotient syzygySetoid
def syzygyClass (s : Syzygy) : SyzygyQuotient := Quotient.mk syzygySetoid s

def quotientResidue : SyzygyQuotient → Bool := Quotient.lift syzygyResidue
  (fun s t h => (syzygy_residue_eq_iff s t).mp h)

def residueClass (c : Bool) : SyzygyQuotient := syzygyClass (syzygyOf (constant c))

@[simp] theorem quotientResidue_class (s : Syzygy) :
    quotientResidue (syzygyClass s) = syzygyResidue s := rfl

@[simp] theorem quotientResidue_residueClass (c : Bool) :
    quotientResidue (residueClass c) = c := by
  simp [residueClass, syzygyResidue]

theorem residueClass_quotientResidue (q : SyzygyQuotient) :
    residueClass (quotientResidue q) = q := by
  refine Quotient.inductionOn q ?_
  intro s
  apply Quotient.sound
  apply (syzygy_residue_eq_iff _ _).mpr
  simp [syzygyResidue]
  rfl

theorem quotientResidue_injective {q r : SyzygyQuotient}
    (h : quotientResidue q = quotientResidue r) : q = r := by
  rw [← residueClass_quotientResidue q, ← residueClass_quotientResidue r, h]

/-- Addition and scalar multiplication on K/mK, transported through the proved
residue bijection; the following theorems identify them with the actual module
operations on representatives. -/
def quotientAdd (q r : SyzygyQuotient) : SyzygyQuotient :=
  residueClass (quotientResidue q ^^ quotientResidue r)
def quotientScale (c : Bool) (q : SyzygyQuotient) : SyzygyQuotient :=
  residueClass (c && quotientResidue q)
def quotientZero : SyzygyQuotient := residueClass false
def quotientGenerator : SyzygyQuotient := residueClass true

theorem quotientAdd_class (s t : Syzygy) :
    quotientAdd (syzygyClass s) (syzygyClass t) = syzygyClass (syzygyAdd s t) := by
  apply quotientResidue_injective
  simp [quotientAdd, syzygyResidue, syzygyAdd]

theorem quotientScale_class (c : Bool) (s : Syzygy) :
    quotientScale c (syzygyClass s) = syzygyClass (syzygyScale c s) := by
  apply quotientResidue_injective
  simp [quotientScale, syzygyResidue, syzygyScale]

theorem quotient_class_zero_iff (s : Syzygy) :
    syzygyClass s = quotientZero ↔ InMaximalTimesSyzygy s.val := by
  rw [syzygy_parametrization s.property, koszul_in_maximal_iff]
  constructor
  · intro h
    exact congrArg quotientResidue h
  · intro h
    apply quotientResidue_injective
    exact h

theorem quotient_basis (q : SyzygyQuotient) :
    ∃ c : Bool, quotientScale c quotientGenerator = q ∧
      ∀ c', quotientScale c' quotientGenerator = q → c' = c := by
  refine ⟨quotientResidue q, ?_, ?_⟩
  · apply quotientResidue_injective
    simp [quotientScale, quotientGenerator]
  · intro c' h
    have hh := congrArg quotientResidue h
    simpa [quotientScale, quotientGenerator] using hh

theorem quotient_generator_nonzero : quotientGenerator ≠ quotientZero := by
  intro h
  have hh := congrArg quotientResidue h
  change true = false at hh
  cases hh

theorem first_betti_support_quotient_iff (d : Nat) :
    FirstBettiSupport d ↔ ∃ s : Syzygy,
      PresentationHomogeneous s.val d ∧ syzygyClass s ≠ quotientZero := by
  constructor
  · rintro ⟨v, hv, hd, hn⟩
    exact ⟨⟨v,hv⟩, hd, fun h => hn ((quotient_class_zero_iff _).mp h)⟩
  · rintro ⟨s, hd, hn⟩
    exact ⟨s.val,s.property,hd,fun h => hn ((quotient_class_zero_iff _).mpr h)⟩

end TLMC506
