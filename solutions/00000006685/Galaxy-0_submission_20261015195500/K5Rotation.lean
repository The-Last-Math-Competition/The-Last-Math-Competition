import Std
import FacialBound

/-!
A kernel-checked obstruction to a spherical rotation system on K₅.
The six local cyclic orders are checked finitely; the global obstruction
is the symbolic dart-counting inequality 3F ≤ 20.
No topological embedding theorem is assumed or proved in this file.
-/
namespace K5Rotation

abbrev Vertex := Fin 5
abbrev Port := Fin 4
abbrev Dart := Fin 20
abbrev LocalRotation := Fin 6
abbrev RotationSystem := Vertex → LocalRotation

def source (d : Dart) : Vertex := ⟨d.val / 4, by omega⟩
def port (d : Dart) : Port := ⟨d.val % 4, Nat.mod_lt _ (by decide)⟩
def neighbor (v : Vertex) (p : Port) : Vertex :=
  if h : p.val < v.val then ⟨p.val, by omega⟩
  else ⟨p.val + 1, by omega⟩
def target (d : Dart) : Vertex := neighbor (source d) (port d)
def dart (v : Vertex) (p : Port) : Dart := ⟨4 * v.val + p.val, by omega⟩

/-- Reverse an ordered edge. This table is verified against its endpoints below. -/
def reverse (d : Dart) : Dart :=
  (#[4, 8, 12, 16, 0, 9, 13, 17, 1, 5, 14, 18, 2, 6, 10, 19, 3, 7, 11, 15] : Array Dart)[d]

/-- All cyclic orders of four labeled ports, with port zero first. -/
def nextPort (r : LocalRotation) (p : Port) : Port :=
  ((#v[ (#v[1, 2, 3, 0] : Vector Port 4), #v[1, 3, 0, 2],
      #v[2, 3, 1, 0], #v[2, 0, 3, 1],
      #v[3, 2, 0, 1], #v[3, 0, 1, 2] ] : Vector (Vector Port 4) 6).get r).get p

def rotate (R : RotationSystem) (d : Dart) : Dart :=
  dart (source d) (nextPort (R (source d)) (port d))

/-- The facial permutation: reverse the dart, then take the next dart
in the cyclic order at its new source. -/
def faceStep (R : RotationSystem) (d : Dart) : Dart := rotate R (reverse d)

theorem faceStep_eq (R : RotationSystem) (d : Dart) :
    faceStep R d = rotate R (reverse d) := rfl

theorem darts_have_distinct_endpoints : ∀ d : Dart, source d ≠ target d := by decide +kernel
theorem every_ordered_edge_has_a_dart :
    ∀ v w : Vertex, v ≠ w → ∃ p : Port, target (dart v p) = w := by decide +kernel
theorem source_reverse : ∀ d : Dart, source (reverse d) = target d := by decide +kernel
theorem target_reverse : ∀ d : Dart, target (reverse d) = source d := by decide +kernel
theorem reverse_reverse : ∀ d : Dart, reverse (reverse d) = d := by decide +kernel

/-- A genuine four-cycle, stated without reference to the six-element encoding. -/
def IsFourCycle (f : Port → Port) : Prop :=
  (∀ p, f (f (f (f p))) = p) ∧ (∀ p, f p ≠ p) ∧ (∀ p, f (f p) ≠ p)

instance (f : Port → Port) : Decidable (IsFourCycle f) := inferInstanceAs
  (Decidable ((∀ p, f (f (f (f p))) = p) ∧ (∀ p, f p ≠ p) ∧ (∀ p, f (f p) ≠ p)))

theorem nextPort_is_four_cycle : ∀ r : LocalRotation, IsFourCycle (nextPort r) := by decide +kernel

def fourFunction (a b c d : Port) (p : Port) : Port :=
  if p = 0 then a else if p = 1 then b else if p = 2 then c else d

theorem fourFunction_eta (f : Port → Port) : fourFunction (f 0) (f 1) (f 2) (f 3) = f := by
  funext p
  have hp : ∀ q : Port, q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 := by decide
  have hp := hp p
  rcases hp with rfl | rfl | rfl | rfl <;> rfl

theorem four_cycle_classification_table : ∀ a b c d : Port,
    IsFourCycle (fourFunction a b c d) →
    ∃ r : LocalRotation, ∀ p : Port, nextPort r p = fourFunction a b c d p := by decide +kernel

theorem all_four_cycles_represented (f : Port → Port) (h : IsFourCycle f) :
    ∃ r : LocalRotation, nextPort r = f := by
  have H := four_cycle_classification_table (f 0) (f 1) (f 2) (f 3)
  rw [fourFunction_eta] at H
  obtain ⟨r, hr⟩ := H h
  exact ⟨r, funext hr⟩


def fiveFunction (a b c d e : LocalRotation) (v : Vertex) : LocalRotation :=
  (#v[a, b, c, d, e] : Vector LocalRotation 5).get v

theorem fiveFunction_eta (R : RotationSystem) :
    fiveFunction (R 0) (R 1) (R 2) (R 3) (R 4) = R := by
  funext v
  have hv : ∀ w : Vertex, w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 3 ∨ w = 4 := by decide
  rcases hv v with rfl | rfl | rfl | rfl | rfl <;> rfl


/-- The finite encoding loses no possible family of cyclic orders. -/
theorem all_rotation_systems_represented (ρ : Vertex → Port → Port)
    (h : ∀ v, IsFourCycle (ρ v)) :
    ∃ R : RotationSystem, ∀ v, nextPort (R v) = ρ v := by
  obtain ⟨r₀, h₀⟩ := all_four_cycles_represented (ρ 0) (h 0)
  obtain ⟨r₁, h₁⟩ := all_four_cycles_represented (ρ 1) (h 1)
  obtain ⟨r₂, h₂⟩ := all_four_cycles_represented (ρ 2) (h 2)
  obtain ⟨r₃, h₃⟩ := all_four_cycles_represented (ρ 3) (h 3)
  obtain ⟨r₄, h₄⟩ := all_four_cycles_represented (ρ 4) (h 4)
  refine ⟨fiveFunction r₀ r₁ r₂ r₃ r₄, ?_⟩
  intro v
  have hv : ∀ w : Vertex, w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 3 ∨ w = 4 := by decide
  rcases hv v with rfl | rfl | rfl | rfl | rfl
  · exact h₀
  · exact h₁
  · exact h₂
  · exact h₃
  · exact h₄

theorem source_dart : ∀ v : Vertex, ∀ p : Port, source (dart v p) = v := by decide +kernel
theorem port_dart : ∀ v : Vertex, ∀ p : Port, port (dart v p) = p := by decide +kernel
theorem dart_source_port : ∀ d : Dart, dart (source d) (port d) = d := by decide +kernel

theorem rotate_four (R : RotationSystem) (d : Dart) :
    rotate R (rotate R (rotate R (rotate R d))) = d := by
  simp only [rotate, source_dart, port_dart]
  rw [(nextPort_is_four_cycle (R (source d))).1, dart_source_port]

def facePrev (R : RotationSystem) (d : Dart) : Dart :=
  reverse (rotate R (rotate R (rotate R d)))

theorem facePrev_faceStep (R : RotationSystem) (d : Dart) :
    facePrev R (faceStep R d) = d := by
  simp only [facePrev, faceStep_eq]
  rw [rotate_four, reverse_reverse]

theorem faceStep_facePrev (R : RotationSystem) (d : Dart) :
    faceStep R (facePrev R d) = d := by
  simp only [facePrev, faceStep_eq]
  rw [reverse_reverse, rotate_four]

theorem faceStep_injective (R : RotationSystem) : Function.Injective (faceStep R) :=
  Function.LeftInverse.injective (facePrev_faceStep R)

theorem faceStep_surjective (R : RotationSystem) : Function.Surjective (faceStep R) :=
  Function.RightInverse.surjective (faceStep_facePrev R)


theorem dart_eq_of_endpoints : ∀ d e : Dart,
    source d = source e → target d = target e → d = e := by decide +kernel

theorem rotate_ne (R : RotationSystem) (d : Dart) : rotate R d ≠ d := by
  intro h
  have hp := congrArg port h
  simp only [rotate, port_dart] at hp
  exact (nextPort_is_four_cycle (R (source d))).2.1 (port d) hp

theorem source_faceStep (R : RotationSystem) (d : Dart) :
    source (faceStep R d) = target d := by
  simp only [faceStep_eq, rotate, source_dart, source_reverse]

theorem faceStep_ne (R : RotationSystem) (d : Dart) : faceStep R d ≠ d := by
  intro h
  have hs := congrArg source h
  rw [source_faceStep] at hs
  exact darts_have_distinct_endpoints d hs.symm

theorem faceStep_twice_ne (R : RotationSystem) (d : Dart) :
    faceStep R (faceStep R d) ≠ d := by
  intro h
  have hs := congrArg source h
  rw [source_faceStep] at hs
  have he : faceStep R d = reverse d := by
    apply dart_eq_of_endpoints
    · rw [source_faceStep, source_reverse]
    · rw [target_reverse]; exact hs
  rw [faceStep_eq] at he
  exact rotate_ne R (reverse d) he


/-- The facial cycles are nonempty closed successor walks, partitioning all
20 darts exactly once. The definition is independent of any face bound. -/
abbrev FacialDecomposition (R : RotationSystem) := FacialBound.Decomposition (faceStep R)

def faceCount {R : RotationSystem} (D : FacialDecomposition R) : Nat := D.faces.length

/-- Euler's spherical face requirement fails by the ordinary face-degree
bound: each face has at least three darts, but only twenty darts exist. -/
theorem faceCount_le_six (R : RotationSystem) (D : FacialDecomposition R) :
    faceCount D ≤ 6 := by
  exact FacialBound.twenty_dart_bound (faceStep R) (faceStep_ne R) (faceStep_twice_ne R) D

theorem no_seven_faces (R : RotationSystem) (D : FacialDecomposition R) :
    faceCount D ≠ 7 := by
  have h := faceCount_le_six R D
  omega

/-- No rotation system of K₅ has a facial decomposition satisfying
V−E+F=2, the Euler equation for a connected spherical embedding. -/
theorem no_spherical_euler_equation (R : RotationSystem) (D : FacialDecomposition R) :
    (5 : Int) - 10 + Int.ofNat (faceCount D) ≠ 2 := by
  have h := no_seven_faces R D
  change -5 + (faceCount D : Int) ≠ 2
  omega

end K5Rotation

