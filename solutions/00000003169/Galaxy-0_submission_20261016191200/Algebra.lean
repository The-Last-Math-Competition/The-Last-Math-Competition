import Std
open Lean.Grind
namespace TLMC3169
abbrev Exponent := Nat × Nat
abbrev Term := Exponent × Nat
abbrev SparsePolynomial := List Term
-- Each entry is ((x exponent, y exponent), nonnegative integer coefficient).
def fPoly : SparsePolynomial := [((0,0),1),((1,0),1),((0,1),1)]
def gPoly : SparsePolynomial := [((0,0),4),((1,0),1),((0,1),2),
  ((3,0),1),((2,1),3),((1,2),3),((0,3),1)]
def support (p : SparsePolynomial) : List Exponent :=
  (p.filter (fun t => t.2 != 0)).map Prod.fst
def eval {R : Type} [CommRing R] (p : SparsePolynomial) (x y : R) : R :=
  (p.map (fun t => (@NatCast.natCast R (Semiring.natCast (α := R)) t.2)*x^t.1.1*y^t.1.2)).foldr (·+·) 0
def dx (p : SparsePolynomial) : SparsePolynomial :=
  p.map fun t => ((t.1.1-1,t.1.2),t.2*t.1.1)
def dy (p : SparsePolynomial) : SparsePolynomial :=
  p.map fun t => ((t.1.1,t.1.2-1),t.2*t.1.2)
theorem f_support : support fPoly = [(0,0),(1,0),(0,1)] := by decide
theorem g_support : support gPoly = [(0,0),(1,0),(0,1),(3,0),(2,1),(1,2),(0,3)] := by decide
theorem coefficients_positive :
  fPoly.all (fun t => 0 < t.2) = true ∧ gPoly.all (fun t => 0 < t.2) = true := by decide
section Algebra
variable {R : Type} [CommRing R]
theorem eval_f (x y : R) : eval fPoly x y = x+y+1 := by
  simp only [eval, fPoly, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
  grind
theorem eval_g (x y : R) : eval gPoly x y = (x+y)^3+x+2*y+4 := by
  simp only [eval, gPoly, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
  grind
def quotientFactor (x y : R) : R := (x+y)^2-(x+y)+2
theorem ideal_identity_y (x y : R) :
  eval gPoly x y - quotientFactor x y * eval fPoly x y = y+2 := by
  simp only [eval_f,eval_g,quotientFactor]
  grind
theorem ideal_identity_x (x y : R) :
  (1+quotientFactor x y)*eval fPoly x y - eval gPoly x y = x-1 := by
  simp only [eval_f,eval_g,quotientFactor]
  grind
theorem reverse_identity_f (x y : R) : eval fPoly x y = (x-1)+(y+2) := by
  rw [eval_f]
  grind
theorem reverse_identity_g (x y : R) : eval gPoly x y =
  quotientFactor x y*(x-1)+(quotientFactor x y+1)*(y+2) := by
  simp only [eval_g,quotientFactor]
  grind
def CommonZero (x y : R) : Prop := eval fPoly x y=0 ∧ eval gPoly x y=0
theorem roots_exact (x y : R) : CommonZero x y ↔ x=1 ∧ y= -2 := by
  unfold CommonZero
  simp only [eval_f,eval_g]
  grind
theorem exactly_one_root : ∃ p : R × R, CommonZero p.1 p.2 ∧
  ∀ q : R × R, CommonZero q.1 q.2 → q=p := by
  refine ⟨(1,-2),(roots_exact 1 (-2)).mpr ⟨rfl,rfl⟩,?_⟩
  intro q hq
  have h := (roots_exact q.1 q.2).mp hq
  exact Prod.ext h.1 h.2
-- Derivatives are computed from the sparse exponent representation.
theorem partials (x y : R) :
  eval (dx fPoly) x y=1 ∧ eval (dy fPoly) x y=1 ∧
  eval (dx gPoly) x y=3*(x+y)^2+1 ∧ eval (dy gPoly) x y=3*(x+y)^2+2 := by
  simp only [dx,dy,fPoly,gPoly,eval,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil]
  grind
def jacobianDet (x y : R) : R :=
  eval (dx fPoly) x y*eval (dy gPoly) x y - eval (dy fPoly) x y*eval (dx gPoly) x y
theorem jacobian_one (x y : R) : jacobianDet x y=1 := by
  have := partials x y
  unfold jacobianDet
  grind
end Algebra
section CharZero
variable {R : Type} [CommRing R] [IsCharP R 0]
theorem root_in_torus : (1 : R) ≠ 0 ∧ (-2 : R) ≠ 0 := by grind
-- Coefficients really remain nonzero after interpreting over characteristic zero.
theorem actual_coefficients_nonzero :
  (1:R) ≠ 0 ∧ (2:R) ≠ 0 ∧ (3:R) ≠ 0 ∧ (4:R) ≠ 0 := by grind
theorem simple_root_certificate : CommonZero (1:R) (-2:R) ∧
  jacobianDet (1:R) (-2:R) ≠ 0 := by
  constructor
  · exact (roots_exact _ _).mpr ⟨rfl,rfl⟩
  · rw [jacobian_one]
    grind
end CharZero
end TLMC3169
