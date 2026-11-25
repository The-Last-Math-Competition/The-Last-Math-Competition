import Std

namespace TorusGenerators

abbrev Generator := Fin 4
abbrev Monomial := Fin 16

def has (m : Monomial) (i : Generator) : Bool := m.val.testBit i.val

def letters (m : Monomial) : List Generator := (List.finRange 4).filter (has m)

def degree (m : Monomial) : Nat := (letters m).length

def single (i : Generator) : Monomial := Fin.ofNat' 16 (2 ^ i.val)

def allowed (m : Monomial) : Bool := !(has m 2 && has m 3)

def exteriorProduct (p q : Monomial) : Option (Int × Monomial) :=
  let union := Fin.ofNat' 16 (p.val ||| q.val)
  if p.val &&& q.val != 0 || !allowed union then none
  else
    let crossings := (letters p).foldl (fun sum i =>
      sum + (letters q).countP (· < i)) 0
    some (if crossings % 2 = 0 then 1 else -1, union)

def wordProduct (word : List Generator) : Option (Int × Monomial) :=
  word.foldl (fun current i => do
    let (sign, m) ← current
    let (stepSign, next) ← exteriorProduct m (single i)
    pure (sign*stepSign, next)) (some (1, 0))

theorem generation_in_degree_one :
    (∀ i : Generator, degree (single i) = 1) ∧
    (∀ m : Monomial, allowed m = true → wordProduct (letters m) = some (1, m)) := by
  decide

theorem one_particle_words_use_only_a_b : ∀ m : Monomial,
    m.val < 4 → allowed m = true ∧ (letters m).all (· < 2) = true := by decide

theorem small_exterior_products :
    exteriorProduct (single 0) (single 1) = some (1, 3) ∧
    exteriorProduct (single 1) (single 0) = some (-1, 3) ∧
    exteriorProduct (single 0) (single 0) = none ∧
    exteriorProduct (single 1) (single 1) = none ∧
    exteriorProduct (single 2) (single 3) = none ∧ degree 3 = 2 := by decide

theorem one_particle_degree_one_count :
    ((List.finRange 16).filter (fun m => m.val < 4 && degree m = 1)).length = 2 := by decide

theorem one_degree_one_vector_cannot_generate_both (x y c d : Int)
    (h₁ : c*x = 1) (h₂ : c*y = 0) (h₃ : d*y = 1) : False := by
  have hc : c ≠ 0 := by
    intro h
    simp [h] at h₁
  have hy := (Int.mul_eq_zero.mp h₂).resolve_left hc
  simp [hy] at h₃

structure Coefficients where
  a : Int
  b : Int
  c : Int
  d : Int

def deckOnDegreeOne (x : Coefficients) : Coefficients :=
  ⟨x.a, x.b, x.a-x.c, x.b-x.d⟩

def fromEigenbasis (x : Coefficients) : Coefficients :=
  ⟨2*x.a, 2*x.b, x.a+x.c, x.b+x.d⟩

def doubledEigenbasisCoordinates (x : Coefficients) : Coefficients :=
  ⟨x.a, x.b, 2*x.c-x.a, 2*x.d-x.b⟩

def scale (k : Int) (x : Coefficients) : Coefficients :=
  ⟨k*x.a, k*x.b, k*x.c, k*x.d⟩

def signsOnDegreeOne (x : Coefficients) : Coefficients :=
  ⟨x.a, x.b, -x.c, -x.d⟩

theorem deck_involution (x : Coefficients) :
    deckOnDegreeOne (deckOnDegreeOne x) = x := by
  cases x
  simp only [deckOnDegreeOne, Coefficients.mk.injEq, true_and]
  exact ⟨by omega, by omega⟩

theorem eigenbasis_theorems (x : Coefficients) :
    deckOnDegreeOne (fromEigenbasis x) = fromEigenbasis (signsOnDegreeOne x) ∧
    doubledEigenbasisCoordinates (fromEigenbasis x) = scale 2 x ∧
    fromEigenbasis (doubledEigenbasisCoordinates x) = scale 2 x := by
  cases x
  simp only [deckOnDegreeOne, fromEigenbasis, signsOnDegreeOne,
    doubledEigenbasisCoordinates, scale, Coefficients.mk.injEq, true_and]
  exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩

def monomialSign (m : Monomial) : Int :=
  if has m 2 != has m 3 then -1 else 1

theorem invariant_monomial_basis : ∀ m : Monomial,
    allowed m = true ∧ monomialSign m = 1 ↔ m.val < 4 := by decide

theorem anti_invariant_complement : ∀ m : Monomial,
    allowed m = true → 4 ≤ m.val → monomialSign m = -1 := by decide

theorem invariant_elements_supported_on_a_b (x : Monomial → Int)
    (support : ∀ m, allowed m = false → x m = 0)
    (invariant : ∀ m, monomialSign m * x m = x m) (m : Monomial) (hm : 4 ≤ m.val) :
    x m = 0 := by
  cases he : allowed m
  · exact support m he
  · have h := invariant m
    rw [anti_invariant_complement m he hm] at h
    omega

theorem invariant_basis_generation : ∀ m : Monomial,
    allowed m = true ∧ monomialSign m = 1 →
      (letters m).all (· < 2) = true ∧ wordProduct (letters m) = some (1, m) := by
  intro m h
  have h' := (invariant_monomial_basis m).mp h
  exact ⟨(one_particle_words_use_only_a_b m h').2, generation_in_degree_one.2 m h.1⟩

theorem claimed_numbers_fail_at_one : 2 < 1 + 2 ∧ (1 : Nat) < 2 := by decide

#print axioms generation_in_degree_one
#print axioms small_exterior_products
#print axioms one_degree_one_vector_cannot_generate_both
#print axioms eigenbasis_theorems
#print axioms invariant_elements_supported_on_a_b
#print axioms invariant_basis_generation
#print axioms claimed_numbers_fail_at_one

end TorusGenerators
