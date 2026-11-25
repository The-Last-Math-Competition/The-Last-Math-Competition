import Std

namespace Conjecture255

structure Weierstrass where
  a1 : Int
  a2 : Int
  a3 : Int
  a4 : Int
  a6 : Int

namespace Weierstrass

def b2 (w : Weierstrass) : Int := w.a1 ^ 2 + 4 * w.a2
def b4 (w : Weierstrass) : Int := 2 * w.a4 + w.a1 * w.a3
def b6 (w : Weierstrass) : Int := w.a3 ^ 2 + 4 * w.a6
def b8 (w : Weierstrass) : Int :=
  w.a1 ^ 2 * w.a6 + 4 * w.a2 * w.a6 - w.a1 * w.a3 * w.a4 +
    w.a2 * w.a3 ^ 2 - w.a4 ^ 2

def c4 (w : Weierstrass) : Int := w.b2 ^ 2 - 24 * w.b4

def discriminant (w : Weierstrass) : Int :=
  -(w.b2 ^ 2 * w.b8) - 8 * w.b4 ^ 3 - 27 * w.b6 ^ 2 + 9 * w.b2 * w.b4 * w.b6

end Weierstrass

/-- y² + y = x³ - x. -/
def curve : Weierstrass := ⟨0, 0, 1, -1, 0⟩

theorem weierstrass_invariants : curve.discriminant = 37 ∧ curve.c4 = 48 := by decide

theorem discriminant_prime_support {p : Nat} (nontrivial : 2 ≤ p)
    (divides : p ∣ curve.discriminant.natAbs) : p = 37 := by
  rw [weierstrass_invariants.1] at divides
  change p ∣ 37 at divides
  have bound : p ≤ 37 := Nat.le_of_dvd (by decide) divides
  have check : ((List.range 38).all fun d =>
      !(decide (2 ≤ d ∧ d < 37 ∧ 37 % d = 0))) = true := by decide
  have excluded := (List.all_eq_true.mp check) p (List.mem_range.mpr (by omega))
  by_cases equal : p = 37
  · exact equal
  · have bad : 2 ≤ p ∧ p < 37 ∧ 37 % p = 0 :=
      ⟨nontrivial, by omega, Nat.mod_eq_zero_of_dvd divides⟩
    simp [bad] at excluded

abbrev F37 := Fin 37

private theorem residue_mem {n : Nat} (r : Fin n) : r ∈ List.finRange n := by
  have bound : r.val < (List.finRange n).length := by
    rw [List.length_finRange]
    exact r.isLt
  have entry : (List.finRange n)[r.val]'bound = r := by
    apply Fin.ext
    simp
  rw [← entry]
  exact List.getElem_mem _

def completedSquare (x : F37) : F37 := 4 * x * x * x - 4 * x + 1

def factoredAt37 (x : F37) : F37 := 4 * (x - 5) * (x - 5) * (x + 10)

theorem factorization_at_37 (x : F37) : completedSquare x = factoredAt37 x := by
  have check : ((List.finRange 37).all fun r => completedSquare r == factoredAt37 r) =
      true := by decide
  exact eq_of_beq ((List.all_eq_true.mp check) x (residue_mem x))

def tangentCoefficient : F37 := 4 * (5 + 10)

theorem tangent_coefficient : tangentCoefficient = 23 := by decide

theorem tangent_euler_criterion : (23 : Nat) ^ 18 % 37 = 36 := by decide

def translatedAtNode (u : F37) : F37 := (u * u) * (4 * u + tangentCoefficient)

theorem translated_equation_at_node (u : F37) :
    completedSquare (u + 5) = translatedAtNode u := by
  have check : ((List.finRange 37).all fun r => completedSquare (r + 5) == translatedAtNode r) =
      true := by decide
  exact eq_of_beq ((List.all_eq_true.mp check) u (residue_mem u))

def squaresMod37 : List F37 := (List.finRange 37).map fun r => r * r

theorem tangent_is_nonsquare (r : F37) : r * r ≠ tangentCoefficient := by
  have excluded : tangentCoefficient ∉ squaresMod37 := by decide
  intro equal
  exact excluded (List.mem_map.mpr ⟨r, residue_mem r, equal⟩)

inductive SemistableReduction where
  | good
  | splitMultiplicative
  | nonsplitMultiplicative

def localSign : SemistableReduction → Int
  | .good => 1
  | .splitMultiplicative => -1
  | .nonsplitMultiplicative => 1

/-- A multiplicative node splits exactly when the tangent coefficient
    is a square in its residue field. -/
def at37 : SemistableReduction :=
  if squaresMod37.contains tangentCoefficient then .splitMultiplicative
  else .nonsplitMultiplicative

def globalSign (finiteBadPlaces : List SemistableReduction) : Int :=
  -((finiteBadPlaces.map localSign).foldr (· * ·) 1)

def curveRootNumber : Int := globalSign [at37]

theorem negative_root_number : at37 = .nonsplitMultiplicative ∧ curveRootNumber = -1 :=
  ⟨rfl, by decide⟩

private theorem even_if_square_even {n : Nat} (squareEven : (n * n) % 2 = 0) :
    n % 2 = 0 := by
  have residues : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases residues with even | odd
  · exact even
  · rw [Nat.mul_mod, odd] at squareEven
    contradiction

private theorem twice_square_even (n : Nat) : (2 * (n * n)) % 2 = 0 := by
  rw [Nat.mul_mod]
  simp

private theorem square_of_double (n : Nat) : (2 * n) * (2 * n) = 4 * (n * n) := by
  calc
    (2 * n) * (2 * n) = (2 * 2) * (n * n) := by ac_rfl
    _ = 4 * (n * n) := rfl

theorem positive_square_not_twice_square (a b : Nat) (positive : 0 < a) :
    a * a ≠ 2 * (b * b) := by
  induction a using Nat.strongRecOn generalizing b with
  | ind a ih =>
    intro equal
    have aEven : a % 2 = 0 := by
      apply even_if_square_even
      rw [equal]
      exact twice_square_even b
    have halfA : 2 * (a / 2) = a := by
      simpa only [aEven, Nat.zero_add] using Nat.mod_add_div a 2
    have bSquared : b * b = 2 * ((a / 2) * (a / 2)) := by
      have fourA : 4 * ((a / 2) * (a / 2)) = 2 * (b * b) := by
        rw [← square_of_double, halfA, equal]
      omega
    have bEven : b % 2 = 0 := by
      apply even_if_square_even
      rw [bSquared]
      exact twice_square_even (a / 2)
    have halfB : 2 * (b / 2) = b := by
      simpa only [bEven, Nat.zero_add] using Nat.mod_add_div b 2
    have fourB : b * b = 4 * ((b / 2) * (b / 2)) := by
      rw [← square_of_double, halfB]
    rw [fourB] at bSquared
    have decreased : (a / 2) * (a / 2) = 2 * ((b / 2) * (b / 2)) := by omega
    have smaller : a / 2 < a := Nat.div_lt_self positive (by decide)
    exact ih (a / 2) smaller (b / 2) (by omega) decreased

/-- An absent order represents an infinite group. The finite group order is positive. -/
def ConjecturedSha (sign : Int) (order : Option Nat) : Prop :=
  ∃ n, order = some n ∧ 0 < n ∧
    (sign = 1 → ∃ a : Nat, n = a * a) ∧
    (sign = -1 → ∃ b : Nat, n = 2 * (b * b))

theorem conjectured_finiteness_and_order_impossible (order : Option Nat)
    (finiteCasselsSquare : ∀ n, order = some n → ∃ a : Nat, n = a * a) :
    ¬ ConjecturedSha curveRootNumber order := by
  intro ⟨n, finite, positive, _, negativePrediction⟩
  obtain ⟨a, square⟩ := finiteCasselsSquare n finite
  obtain ⟨b, twiceSquare⟩ := negativePrediction negative_root_number.2
  have positiveA : 0 < a := by
    by_cases zero : a = 0
    · simp [zero] at square
      omega
    · omega
  exact positive_square_not_twice_square a b positiveA (square.symm.trans twiceSquare)

end Conjecture255

#print axioms Conjecture255.weierstrass_invariants
#print axioms Conjecture255.discriminant_prime_support
#print axioms Conjecture255.factorization_at_37
#print axioms Conjecture255.translated_equation_at_node
#print axioms Conjecture255.tangent_is_nonsquare
#print axioms Conjecture255.tangent_euler_criterion
#print axioms Conjecture255.negative_root_number
#print axioms Conjecture255.positive_square_not_twice_square
#print axioms Conjecture255.conjectured_finiteness_and_order_impossible
