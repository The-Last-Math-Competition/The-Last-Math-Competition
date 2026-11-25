import Std

/-! Finite calculations for the two rationally represented rank-three
matroids. Integer point coordinates are lifted to `(x,y,1)` over `ℚ` in
the report. Labels here start at zero. -/

namespace Bergman

abbrev Point := Int × Int
abbrev Label := Fin 6
abbrev Configuration := Vector Point 6

def configurationM : Configuration := #v[(0, 0), (1, 0), (2, 0), (3, 0), (0, 1), (5, 2)]
def configurationN : Configuration := #v[(0, 0), (2, 0), (0, 2), (1, 0), (1, 1), (0, 1)]

/-- Determinant of the three lifted columns, calculated by subtracting
the first column from each of the other two. -/
def determinant (configuration : Configuration) (i j k : Label) : Int :=
  let (xi, yi) := configuration.get i
  let (xj, yj) := configuration.get j
  let (xk, yk) := configuration.get k
  (xj - xi) * (yk - yi) - (yj - yi) * (xk - xi)

def labels : List Label := List.finRange 6

def pairs : List (Label × Label) :=
  labels.flatMap fun i => (labels.filter fun j => decide (i < j)).map (i, ·)

def pairClosure (configuration : Configuration) (pair : Label × Label) : List Label :=
  labels.filter fun k => determinant configuration pair.1 pair.2 k == 0

def lines (configuration : Configuration) : List (List Label) :=
  (pairs.map (pairClosure configuration)).eraseDups

/-- Nonproportional lifted columns and a nonzero triple determinant
certify simplicity and rank three. -/
def SimpleRankThree (configuration : Configuration) : Prop :=
  (∀ i j : Label, i < j → configuration.get i ≠ configuration.get j) ∧
    (∃ i j k : Label, determinant configuration i j k ≠ 0)

theorem configurationM_simple : SimpleRankThree configurationM := by
  exact ⟨by decide, 0, 1, 4, by decide⟩

theorem configurationN_simple : SimpleRankThree configurationN := by
  exact ⟨by decide, 0, 1, 2, by decide⟩

theorem pair_enumeration : ∀ i j : Label, (i, j) ∈ pairs ↔ i < j := by decide

theorem linesM : lines configurationM =
    [[0, 1, 2, 3], [0, 4], [0, 5], [1, 4], [1, 5], [2, 4], [2, 5],
      [3, 4], [3, 5], [4, 5]] := by decide

theorem linesN : lines configurationN =
    [[0, 1, 3], [0, 2, 5], [0, 4], [1, 2, 4], [1, 5], [2, 3],
      [3, 4], [3, 5], [4, 5]] := by decide

/-- Rank-three characteristic coefficients in descending degree order.
The lines contribute their points minus one by the Möbius recurrence. -/
def characteristicCoefficients (configuration : Configuration) : List Int :=
  let lineMobius := ((lines configuration).map fun line => (line.length : Int) - 1).sum
  let pointCount : Int := labels.length
  [1, -pointCount, lineMobius, -(1 - pointCount + lineMobius)]

def fineFaceCounts (configuration : Configuration) : Int × Int :=
  let flats := lines configuration
  (labels.length + flats.length, (flats.map fun line => (line.length : Int)).sum)

def fineH (configuration : Configuration) : List Int :=
  let (vertices, edges) := fineFaceCounts configuration
  [1, vertices - 2, edges - vertices + 1]

def linesThrough (configuration : Configuration) (point : Label) : Nat :=
  ((lines configuration).filter fun line => line.contains point).length

/-- These are the finite incidence conditions used with the flacet
criterion to count all singleton vertices and the long-line vertices. -/
def CoarseIncidence (configuration : Configuration) : Prop :=
  (lines configuration).all (fun line => decide (line.length < 5)) = true ∧
    ∀ i : Label, 3 ≤ linesThrough configuration i

def coarseHOne (configuration : Configuration) : Int :=
  let longLines := (lines configuration).filter fun line => decide (3 ≤ line.length)
  (labels.length : Int) + longLines.length - 2

theorem coefficients_and_h :
    characteristicCoefficients configurationM = [1, -6, 12, -7] ∧
    characteristicCoefficients configurationN = [1, -6, 12, -7] ∧
    fineH configurationM = [1, 14, 7] ∧
    fineH configurationN = [1, 13, 7] := by decide

theorem coarse_incidence_and_hone :
    CoarseIncidence configurationM ∧ CoarseIncidence configurationN ∧
    coarseHOne configurationM = 5 ∧ coarseHOne configurationN = 7 := by
  unfold CoarseIncidence
  decide

theorem no_coefficient_rule :
    ¬ ∃ rule : List Int → List Int, ∀ c, SimpleRankThree c →
      rule (characteristicCoefficients c) = fineH c := by
  rintro ⟨rule, spec⟩
  obtain ⟨coeffM, coeffN, hM, hN⟩ := coefficients_and_h
  have equalCoeffs := coeffM.trans coeffN.symm
  have equalH := (spec configurationM configurationM_simple).symm.trans
    ((congrArg rule equalCoeffs).trans (spec configurationN configurationN_simple))
  rw [hM, hN] at equalH
  exact (by decide : ([1, 14, 7] : List Int) ≠ [1, 13, 7]) equalH

#print axioms pair_enumeration
#print axioms linesM
#print axioms linesN
#print axioms no_coefficient_rule
#print axioms coarse_incidence_and_hone

end Bergman
