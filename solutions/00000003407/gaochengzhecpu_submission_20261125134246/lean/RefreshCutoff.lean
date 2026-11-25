import Std

namespace C3407

abbrev Polynomial := List Int

def add : Polynomial → Polynomial → Polynomial
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => (a + b) :: add p q

def neg (p : Polynomial) : Polynomial := p.map Int.neg

def mul : Polynomial → Polynomial → Polynomial
  | [], _ => []
  | _, [] => []
  | a :: p, b :: q => add ((b :: q).map fun x => a * x) (0 :: mul p (b :: q))

/-- Entry `(i,j)` of `x I - r(I-J/r)` in ascending coefficient order. -/
def characteristicEntry (r : Nat) (i j : Fin r) : Polynomial :=
  if i = j then [1 - (r : Int), 1] else [1]

def determinantTwo (a : Fin 2 → Fin 2 → Polynomial) : Polynomial :=
  add (mul (a 0 0) (a 1 1)) (neg (mul (a 0 1) (a 1 0)))

def determinantThree (a : Fin 3 → Fin 3 → Polynomial) : Polynomial :=
  let prod (i j k : Fin 3) := mul (mul (a 0 i) (a 1 j)) (a 2 k)
  let even := add (prod 0 1 2) (add (prod 1 2 0) (prod 2 0 1))
  let odd := add (prod 0 2 1) (add (prod 1 0 2) (prod 2 1 0))
  add even (neg odd)

theorem two_state_characteristic_polynomial :
    determinantTwo (characteristicEntry 2) = mul [0, 1] [-2, 1] := by decide

theorem three_state_characteristic_polynomial :
    determinantThree (characteristicEntry 3) = mul [0, 1] (mul [-3, 1] [-3, 1]) := by decide

/-- Here `ρ = s / D`. These are the transition weights with denominator `2D`. -/
def weightsTwo (D s : Int) : List Int := [D + s, D - s]

/-- The corresponding weights with denominator `3D`. -/
def weightsThree (D s : Int) : List Int := [D + 2 * s, D - s, D - s]

theorem normalizations (D s : Int) :
    (weightsTwo D s).sum = 2 * D ∧ (weightsThree D s).sum = 3 * D := by
  constructor <;> simp [weightsTwo, weightsThree] <;> omega

def squared (weights : List Int) : List Int := weights.map fun w => w * w

theorem two_state_second_moment (D s : Int) :
    (squared (weightsTwo D s)).sum = 2 * (D * D + s * s) := by
  simp only [squared, weightsTwo, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Int.add_mul, Int.mul_add, Int.sub_mul, Int.mul_sub]
  omega

theorem three_state_second_moment (D s : Int) :
    (squared (weightsThree D s)).sum = 3 * (D * D + 2 * (s * s)) := by
  have right : D * (2 * s) = 2 * (D * s) := by ac_rfl
  have left : (2 * s) * D = 2 * (s * D) := by ac_rfl
  have square : (2 * s) * (2 * s) = 4 * (s * s) := by
    calc
      (2 * s) * (2 * s) = (2 * 2) * (s * s) := by ac_rfl
      _ = 4 * (s * s) := rfl
  simp only [squared, weightsThree, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Int.add_mul, Int.mul_add, Int.sub_mul, Int.mul_sub, right, left, square]
  omega

/-- Enumerate the product weight once for each ordered word of length `n`. -/
def productWeights (weights : List Int) : Nat → List Int
  | 0 => [1]
  | n + 1 => weights.flatMap fun w => (productWeights weights n).map (fun rest => w * rest)

private theorem sum_scaled (w : Int) (xs : List Int) :
    (xs.map fun x => w * x).sum = w * xs.sum := by
  induction xs with
  | nil => simp
  | cons x rest ih => simp [ih, Int.mul_add]

private theorem sum_append (xs ys : List Int) : (xs ++ ys).sum = xs.sum + ys.sum := by
  induction xs with
  | nil => simp
  | cons x rest ih => simp [ih, Int.add_assoc]

private theorem sum_product_pair (xs ys : List Int) :
    (xs.flatMap fun x => ys.map fun y => x * y).sum = xs.sum * ys.sum := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
    simp only [List.flatMap_cons, sum_append, sum_scaled, ih, List.sum_cons, Int.add_mul]

theorem sum_product_weights (weights : List Int) (n : Nat) :
    (productWeights weights n).sum = weights.sum ^ n := by
  induction n with
  | zero => simp [productWeights]
  | succ n ih =>
    rw [productWeights, sum_product_pair, ih, Int.pow_succ]
    exact Int.mul_comm _ _

theorem product_second_moments (D s : Int) (n : Nat) :
    (productWeights (squared (weightsTwo D s)) n).sum = (2 * (D * D + s * s)) ^ n ∧
    (productWeights (squared (weightsThree D s)) n).sum =
      (3 * (D * D + 2 * (s * s))) ^ n := by
  constructor
  · rw [sum_product_weights, two_state_second_moment]
  · rw [sum_product_weights, three_state_second_moment]

/-- Difference of the means of the match count, with a common integer denominator. -/
theorem count_mean_differences (n D s : Int) :
    n * (D + s) - n * D = n * s ∧ n * (D + 2 * s) - n * D = 2 * (n * s) := by
  have factor : n * (2 * s) = 2 * (n * s) := by ac_rfl
  constructor <;> simp only [Int.mul_add, factor] <;> omega

theorem bernoulli_variance_bound (D s : Int) : 4 * s * (D - s) ≤ D * D := by
  have right : D * (2 * s) = 2 * (s * D) := by ac_rfl
  have left : (2 * s) * D = 2 * (s * D) := by ac_rfl
  have square : (2 * s) * (2 * s) = 4 * (s * s) := by
    calc
      (2 * s) * (2 * s) = (2 * 2) * (s * s) := by ac_rfl
      _ = 4 * (s * s) := rfl
  have expansion : (D - 2 * s) * (D - 2 * s) =
      D * D - (2 * (s * D)) - (2 * (s * D) - 4 * (s * s)) := by
    simp only [Int.sub_mul, Int.mul_sub, right, left, square]
  have nonnegative : 0 ≤ (D - 2 * s) * (D - 2 * s) := by
    by_cases nonneg : 0 ≤ D - 2 * s
    · exact Int.mul_nonneg nonneg nonneg
    · have nonpos : D - 2 * s ≤ 0 := by omega
      exact Int.mul_nonneg_of_nonpos_of_nonpos nonpos nonpos
  rw [expansion] at nonnegative
  rw [Int.mul_assoc]
  simp only [Int.mul_sub]
  omega

#print axioms two_state_characteristic_polynomial
#print axioms three_state_characteristic_polynomial
#print axioms product_second_moments
#print axioms count_mean_differences
#print axioms bernoulli_variance_bound

end C3407
