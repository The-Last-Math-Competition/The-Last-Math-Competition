import Std

namespace C617

inductive Sign where
  | positive | negative
  deriving DecidableEq

def Sign.flip : Sign → Sign
  | .positive => .negative
  | .negative => .positive

abbrev Braid := List Sign
abbrev Strand := Fin 2

def positiveWord (n : Nat) : Braid := List.replicate n .positive
def mirror (braid : Braid) : Braid := braid.map Sign.flip

def trefoil : Braid := positiveWord 3
def hopf : Braid := positiveWord 2

def swapStrands (i : Strand) : Strand := if i = 0 then 1 else 0

/-- Both signs of the two-strand crossing interchange the two endpoints. -/
def endpoint (braid : Braid) (i : Strand) : Strand :=
  braid.foldl (fun strand _ => swapStrands strand) i

/-- The component count of the closure of the two-strand permutation. -/
def components (endpointMap : Strand → Strand) : Nat := if endpointMap 0 = 0 then 2 else 1

theorem components_of_closures :
    components (endpoint trefoil) = 1 ∧ components (endpoint (mirror trefoil)) = 1 ∧
    components (endpoint hopf) = 2 ∧ components (endpoint (mirror hopf)) = 2 := by decide

/-- The oriented smoothing of a braid-oriented crossing leaves both strand indices fixed. -/
def smoothedEndpoint (braid : Braid) (i : Strand) : Strand :=
  braid.foldl (fun strand _ => strand) i

def negativeCount (braid : Braid) : Nat := braid.countP fun s => decide (s = .negative)

def trefoilS : Int :=
  (trefoil.length : Int) - (components (smoothedEndpoint trefoil) : Int) + 1

def canonicalLevels (s : Int) : List Int := [s - 1, s - 1]
def associatedLevels (s : Int) : List Int := [s - 1, s + 1]

abbrev Orientations := Bool × Bool

/-- `true` indicates reversal relative to the reference orientation. -/
def orientations : List Orientations := [(false, false), (true, true), (false, true), (true, false)]

theorem orientations_exhaustive (a b : Bool) : (a, b) ∈ orientations := by
  cases a <;> cases b <;> decide

/-- Each Hopf crossing joins the two components and flips under exactly one reversal. -/
def reorientedHopf (braid : Braid) (orientation : Orientations) : Braid :=
  braid.map fun s => if orientation.1 = orientation.2 then s else s.flip

def homologicalDegree (braid : Braid) (orientation : Orientations) : Int :=
  (negativeCount (reorientedHopf braid orientation) : Int) - (negativeCount braid : Int)

def homologicalDegrees (braid : Braid) : List Int := orientations.map (homologicalDegree braid)

theorem hopf_degree_lists :
    homologicalDegrees hopf = [0, 0, 2, 2] ∧
    homologicalDegrees (mirror hopf) = [0, 0, -2, -2] := by decide

abbrev Rational := Std.Internal.Rat

def mean (levels : List Int) : Rational := Std.Internal.mkRat levels.sum levels.length

theorem trefoil_filtration_means :
    mean (canonicalLevels trefoilS) = 1 ∧ mean (canonicalLevels (-trefoilS)) = -3 ∧
    mean (associatedLevels trefoilS) = 2 ∧ mean (associatedLevels (-trefoilS)) = -2 := by decide

theorem hopf_homological_means :
    mean (homologicalDegrees hopf) = 1 ∧ mean (homologicalDegrees (mirror hopf)) = -1 := by decide

/-- Coefficients of the standard Alexander representative in increasing powers. -/
def trefoilAlexander : List Int := [1, -1, 1]

def polynomialAt (t : Int) : List Int → Int
  | [] => 0
  | c :: rest => c + t * polynomialAt t rest

def alexanderDet (coeffs : List Int) : Nat := (polynomialAt (-1) coeffs).natAbs
def oneEntrySeifertDet (twist : Int) : Nat := (twist + twist).natAbs

theorem determinant_values :
    alexanderDet trefoilAlexander = 3 ∧ alexanderDet trefoilAlexander.reverse = 3 ∧
    oneEntrySeifertDet 1 = 2 ∧ oneEntrySeifertDet (-1) = 2 := by decide

def RecoveredFromDet (a b : Nat) (first second : Rational) : Prop :=
  ∃ f : Nat → Rational, f a = first ∧ f b = second

private theorem equal_det_obstruction {a b : Nat} {first second : Rational}
    (same : a = b) (different : first ≠ second) : ¬ RecoveredFromDet a b first second := by
  rintro ⟨f, firstEq, secondEq⟩
  exact different (firstEq.symm.trans ((congrArg f same).trans secondEq))

theorem no_determinant_mean_formula :
    (¬ RecoveredFromDet (alexanderDet trefoilAlexander) (alexanderDet trefoilAlexander.reverse)
      (mean (canonicalLevels trefoilS)) (mean (canonicalLevels (-trefoilS)))) ∧
    (¬ RecoveredFromDet (alexanderDet trefoilAlexander) (alexanderDet trefoilAlexander.reverse)
      (mean (associatedLevels trefoilS)) (mean (associatedLevels (-trefoilS)))) ∧
    (¬ RecoveredFromDet (oneEntrySeifertDet 1) (oneEntrySeifertDet (-1))
      (mean (homologicalDegrees hopf)) (mean (homologicalDegrees (mirror hopf)))) := by
  exact ⟨equal_det_obstruction (by decide) (by decide),
    equal_det_obstruction (by decide) (by decide),
    equal_det_obstruction (by decide) (by decide)⟩

#print axioms components_of_closures
#print axioms hopf_degree_lists
#print axioms no_determinant_mean_formula

end C617
