import Std

namespace Conjecture1061

-- `Fin 5` uses arithmetic modulo 5.
abbrev F5 := Fin 5

-- Coefficients are listed in ascending order of degree.
def quintic (c : F5) : List F5 := [c, 4, 0, 0, 0, 1]

def evalPoly (coeffs : List F5) (x : F5) : F5 :=
  coeffs.foldr (fun coeff tail => coeff + x * tail) 0

def derivative (coeffs : List F5) : List F5 :=
  (coeffs.zipIdx.map (fun (coeff, i) => coeff * (Fin.ofNat' 5 i))).drop 1

theorem quintic_derivative (c : F5) : derivative (quintic c) = [4, 0, 0, 0, 0] := by
  rfl

-- The resultant with the constant polynomial a is the product of a over
-- the roots of the monic first polynomial, counted with multiplicity.
def resultantWithConstant (degree : Nat) (a : F5) : F5 :=
  (List.replicate degree a).foldr (· * ·) 1

-- Since the derivative is constant, its constant coefficient suffices for
-- the monic discriminant formula (-1)^(d(d-1)/2) Res(f,f').
def discriminant (c : F5) : F5 :=
  let coeffs := quintic c
  let degree := coeffs.length - 1
  resultantWithConstant (degree * (degree - 1) / 2) 4 *
    resultantWithConstant degree ((derivative coeffs).headD 0)

theorem discriminant_eq_four (c : F5) : discriminant c = 4 := by
  unfold discriminant
  have degree : (quintic c).length - 1 = 5 := rfl
  simp only [degree, quintic_derivative]
  decide

def squaresAbove (a : F5) : Nat :=
  ((List.finRange 5).filter fun y => y * y == a).length

def quadraticCharacter (a : F5) : Int :=
  if a = 0 then 0 else if squaresAbove a > 0 then 1 else -1

theorem quadraticCharacter_four : quadraticCharacter 4 = 1 := by
  decide

def affineCount (c : F5) : Nat :=
  ((List.finRange 5).map fun x => squaresAbove (evalPoly (quintic c) x)).sum

-- In the chart u = 1/x, v = y/x³, the equation is
-- v² = u - u⁵ + c u⁶, so the fibre u = 0 has equation v² = 0.
def pointCount (c : F5) : Nat := affineCount c + squaresAbove 0

theorem affineCount_zero : affineCount 0 = 5 := by
  decide

theorem affineCount_four : affineCount 4 = 10 := by
  decide

theorem infinityCount : squaresAbove 0 = 1 := by
  decide

theorem pointCount_zero : pointCount 0 = 6 := by
  decide

theorem pointCount_four : pointCount 4 = 11 := by
  decide

theorem no_projective_parity_from_discriminant_sign :
    ¬ ∃ predict : Int → Nat, ∀ c : F5,
      pointCount c % 2 = predict (quadraticCharacter (discriminant c)) := by
  rintro ⟨predict, h⟩
  have h₀ := h 0
  have h₁ := h 4
  rw [discriminant_eq_four, quadraticCharacter_four, pointCount_zero] at h₀
  rw [discriminant_eq_four, quadraticCharacter_four, pointCount_four] at h₁
  have hParity : 6 % 2 = 11 % 2 := h₀.trans h₁.symm
  exact (by decide : 6 % 2 ≠ 11 % 2) hParity

theorem no_affine_parity_from_discriminant_sign :
    ¬ ∃ predict : Int → Nat, ∀ c : F5,
      affineCount c % 2 = predict (quadraticCharacter (discriminant c)) := by
  rintro ⟨predict, h⟩
  have h₀ := h 0
  have h₁ := h 4
  rw [discriminant_eq_four, quadraticCharacter_four, affineCount_zero] at h₀
  rw [discriminant_eq_four, quadraticCharacter_four, affineCount_four] at h₁
  have hParity : 5 % 2 = 10 % 2 := h₀.trans h₁.symm
  exact (by decide : 5 % 2 ≠ 10 % 2) hParity

end Conjecture1061

#print axioms Conjecture1061.no_projective_parity_from_discriminant_sign
#print axioms Conjecture1061.no_affine_parity_from_discriminant_sign
