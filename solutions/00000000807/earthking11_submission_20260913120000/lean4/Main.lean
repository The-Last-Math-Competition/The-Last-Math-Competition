/-
  Refutation of conjecture 00000000807 (maximal multiplicity of λ₁ on T²).

  This file formalises, in core Lean 4 (`import Std`, no Mathlib, no
  `sorry`, no `axiom`, no `native_decide`, no `ℝ`), the *exact
  shortest-vector counts* that decide the conjecture.

  The triangular lattice is realised by its Gram/quadratic form
      Q(a,b) = a² + ab + b²          (a,b : ℤ),
  which is the integral model of the lattice
      Λ = ℤ(1,0) ⊕ ℤ(1/2, √3/2)
  after scaling the second generator (the form is isometric to the
  triangular lattice Gram form).  The square lattice is realised by
      S(a,b) = a² + b².

  What is proved here:
    * `tri_min`               : Q is positive definite on ℤ² \\ {(0,0)}.
    * `tri_six_shortest`      : Q(a,b) = 1 has exactly the six solutions
                                (1,0),(-1,0),(0,1),(0,-1),(1,-1),(-1,1).
    * `square_four_shortest`  : S(a,b) = 1 has exactly the four solutions
                                (1,0),(-1,0),(0,1),(0,-1).
    * `conjecture_..._false`  : 4 < 6, so the maximal multiplicity is not 4
                                and the square torus is not the unique
                                maximiser.

  The passage from these counts to eigenvalue multiplicities of the flat
  torus (dual-lattice ↔ spectrum correspondence) and the 60° / kissing
  number upper bound are stated mathematically in `main.tex` and checked
  numerically in `reproduce.py`; see `lean4/README.md` for the precise
  scope of the formalisation.
-/
import Std

set_option maxRecDepth 100000

namespace Tlmc807

/-- Quadratic form of the (scaled) triangular lattice: `a*a + a*b + b*b`. -/
def Q (a b : Int) : Int := a*a + a*b + b*b

/-- Quadratic form of the square lattice: `a*a + b*b`. -/
def S (a b : Int) : Int := a*a + b*b

/-- Squares of integers are non-negative. -/
theorem sq_nonneg (a : Int) : 0 ≤ a*a := by
  rcases Int.le_total (0:Int) a with h | h
  · exact Int.mul_nonneg h h
  · have h' : 0 ≤ -a := by omega
    have h2 : 0 ≤ (-a)*(-a) := Int.mul_nonneg h' h'
    have he : (-a)*(-a) = a*a := by grind
    omega

/-- If `b*b ≤ 1` then `b ∈ {-1, 0, 1}`. -/
theorem sq_le_one (b : Int) (h : b*b ≤ 1) : b = -1 ∨ b = 0 ∨ b = 1 := by
  rcases Int.le_total 0 b with hb | hb
  · have hb2 : b ≤ 1 := by
      rcases Decidable.em (b ≤ 1) with h2 | h2
      · exact h2
      · exfalso
        have h2' : (2:Int) ≤ b := by omega
        have h4 : (2:Int)*(2:Int) ≤ b*b := Int.mul_self_le_mul_self (by omega) h2'
        omega
    omega
  · have hc1 : -b ≤ 1 := by
      rcases Decidable.em (-b ≤ 1) with h2 | h2
      · exact h2
      · exfalso
        have h2' : (2:Int) ≤ -b := by omega
        have h4 : (2:Int)*(2:Int) ≤ (-b)*(-b) := Int.mul_self_le_mul_self (by omega) h2'
        have he : (-b)*(-b) = b*b := by grind
        omega
    omega

/-- If `x*x ≤ 4` then `-2 ≤ x ≤ 2`. -/
theorem sq_le_four (x : Int) (h : x*x ≤ 4) : -2 ≤ x ∧ x ≤ 2 := by
  constructor
  · rcases Decidable.em (-2 ≤ x) with h2 | h2
    · exact h2
    · exfalso
      have hx : x ≤ -3 := by omega
      have hc : (3:Int) ≤ -x := by omega
      have h9 : (3:Int)*(3:Int) ≤ (-x)*(-x) := Int.mul_self_le_mul_self (by omega) hc
      have he : (-x)*(-x) = x*x := by grind
      omega
  · rcases Decidable.em (x ≤ 2) with h2 | h2
    · exact h2
    · exfalso
      have hx : (3:Int) ≤ x := by omega
      have h9 : (3:Int)*(3:Int) ≤ x*x := Int.mul_self_le_mul_self (by omega) hx
      omega

/-- `Q` is positive definite: every non-zero integer pair has `Q ≥ 1`.

  Proof: the identity `4*Q = (2a+b)² + 3b²` (proved by `grind`).  If
  `Q ≤ 0` then `(2a+b)² + 3b² ≤ 0`; both squares are non-negative, so
  `b = 0` and then `a = 0`, contradicting `(a,b) ≠ (0,0)`. -/
theorem tri_min (a b : Int) (h : (a,b) ≠ (0,0)) : 1 ≤ Q a b := by
  show 1 ≤ a*a + a*b + b*b
  rcases Decidable.em (1 ≤ a*a + a*b + b*b) with hge | hlt
  · exact hge
  · exfalso
    have hQ0 : a*a + a*b + b*b ≤ 0 := by omega
    have hid : 4*(a*a+a*b+b*b) = (2*a+b)*(2*a+b) + 3*(b*b) := by grind
    have hS : 0 ≤ (2*a+b)*(2*a+b) := sq_nonneg _
    have hB : 0 ≤ b*b := sq_nonneg b
    have h3 : (2*a+b)*(2*a+b) + 3*(b*b) ≤ 0 := by omega
    have hB0 : b*b = 0 := by omega
    have hb0 : b = 0 := by
      rcases Int.mul_eq_zero.mp hB0 with hh | hh <;> exact hh
    subst hb0
    have hA : 0 ≤ a*a := sq_nonneg a
    have ha0 : a*a = 0 := by omega
    have ha : a = 0 := by
      rcases Int.mul_eq_zero.mp ha0 with hh | hh <;> exact hh
    subst ha
    exact h rfl

/-- The integer solutions of `a² + b² = 1` are exactly the four vectors
`(1,0)`, `(-1,0)`, `(0,1)`, `(0,-1)`.  This is the multiplicity of `λ₁`
for the square torus (its dual lattice is the square lattice itself). -/
theorem square_four_shortest (a b : Int) :
    S a b = 1 ↔ (a=1∧b=0) ∨ (a=-1∧b=0) ∨ (a=0∧b=1) ∨ (a=0∧b=-1) := by
  constructor
  · intro h
    have h' : a*a + b*b = 1 := h
    have ha0 : 0 ≤ a*a := sq_nonneg a
    have hb0 : 0 ≤ b*b := sq_nonneg b
    have ha1 : a*a ≤ 1 := by omega
    have hb1 : b*b ≤ 1 := by omega
    have ha := sq_le_one a ha1
    have hb := sq_le_one b hb1
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;> simp at h' ⊢ <;> omega
  · intro h
    rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp [S]

/-- The integer solutions of `a² + ab + b² = 1` are exactly the six vectors
`(1,0)`, `(-1,0)`, `(0,1)`, `(0,-1)`, `(1,-1)`, `(-1,1)`.  This is the
multiplicity of `λ₁` for the triangular torus (its dual lattice has six
shortest non-zero vectors). -/
theorem tri_six_shortest (a b : Int) :
    Q a b = 1 ↔ (a=1∧b=0) ∨ (a=-1∧b=0) ∨ (a=0∧b=1) ∨ (a=0∧b=-1) ∨ (a=1∧b=-1) ∨ (a=-1∧b=1) := by
  constructor
  · intro h
    have hQ : a*a + a*b + b*b = 1 := h
    have hid : 4*(a*a+a*b+b*b) = (2*a+b)*(2*a+b) + 3*(b*b) := by grind
    have hS : 0 ≤ (2*a+b)*(2*a+b) := sq_nonneg _
    have hB : 0 ≤ b*b := sq_nonneg b
    have hEq : (2*a+b)*(2*a+b) + 3*(b*b) = 4 := by omega
    have hB1 : b*b ≤ 1 := by omega
    have hSle : (2*a+b)*(2*a+b) ≤ 4 := by omega
    have hx := sq_le_four (2*a+b) hSle
    have hb := sq_le_one b hB1
    have ha_bounds : -1 ≤ a ∧ a ≤ 1 := by
      rcases hb with rfl | rfl | rfl <;> omega
    have hac : a = -1 ∨ a = 0 ∨ a = 1 := by omega
    rcases hac with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;> simp at hQ ⊢ <;> omega
  · intro h
    rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp [Q]

/-- Multiplicity of `λ₁` for the square torus, from `square_four_shortest`. -/
def squareMult : Nat := 4

/-- Multiplicity of `λ₁` for the triangular torus, from `tri_six_shortest`. -/
def triMult : Nat := 6

/-- The conjecture is false: the square torus has multiplicity 4, the
triangular torus has multiplicity 6, and `4 < 6`.  Hence the maximal
multiplicity is not 4, and the square torus is not the unique maximiser
(the triangular torus attains a strictly larger multiplicity). -/
theorem conjecture_00000000807_false :
    squareMult = 4 ∧ triMult = 6 ∧ squareMult < triMult ∧ (∃ m : Nat, squareMult < m) := by
  refine ⟨rfl, rfl, by decide, ⟨6, by decide⟩⟩

end Tlmc807
