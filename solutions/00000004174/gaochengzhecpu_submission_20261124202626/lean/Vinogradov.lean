import Std

namespace Vinogradov

structure Triple where
  a : Int
  b : Int
  c : Int
  deriving DecidableEq

def Triple.at (x : Triple) (i : Fin 3) : Int :=
  match i.val with
  | 0 => x.a
  | 1 => x.b
  | _ => x.c

def linear (x : Triple) : Int := x.a + x.b + x.c
def quadratic (x : Triple) : Int := x.a*x.a + x.b*x.b + x.c*x.c

def bounded (X : Nat) (x : Triple) : Prop :=
  ∀ i, 1 ≤ x.at i ∧ x.at i ≤ (X : Int)

def injective {α β : Type} (f : α → β) : Prop :=
  ∀ ⦃a b⦄, f a = f b → a = b

def diagonal (x y : Triple) : Prop :=
  ∃ σ : Fin 3 → Fin 3, injective σ ∧ ∀ i, y.at i = x.at (σ i)

def equations (x y : Triple) : Prop :=
  linear x = linear y ∧ quadratic x = quadratic y

def congruences (m : Int) (x y : Triple) : Prop :=
  linear x % m = linear y % m ∧ quadratic x % m = quadratic y % m

def OffDiagonal (X : Nat) :=
  {p : Triple × Triple // bounded X p.1 ∧ bounded X p.2 ∧ equations p.1 p.2 ∧
    (∀ m, congruences m p.1 p.2) ∧ ¬ diagonal p.1 p.2}

abbrev Box (M : Nat) := Fin M × Fin M × Fin M

private theorem fin3 (i : Fin 3) : i = 0 ∨ i = 1 ∨ i = 2 := by
  simp only [Fin.ext_iff]
  have := i.isLt
  omega

def left (M : Nat) (p : Box M) : Triple :=
  ⟨3*((M : Int)+p.1.val), 3*((M : Int)+p.2.1.val), 3*(3*(M : Int)+p.2.2.val)⟩

def right (M : Nat) (p : Box M) : Triple :=
  let a : Int := (M : Int) + p.1.val
  let b : Int := (M : Int) + p.2.1.val
  let c : Int := 3*(M : Int) + p.2.2.val
  ⟨2*a-b+2*c, -a+2*b+2*c, 2*a+2*b-c⟩

theorem left_bounded (M : Nat) (p : Box M) : bounded (12*M) (left M p) := by
  have h₁ := p.1.isLt
  have h₂ := p.2.1.isLt
  have h₃ := p.2.2.isLt
  intro i
  rcases fin3 i with rfl | rfl | rfl <;> simp [Triple.at, left] <;> omega

theorem right_bounded (M : Nat) (p : Box M) : bounded (12*M) (right M p) := by
  have h₁ := p.1.isLt
  have h₂ := p.2.1.isLt
  have h₃ := p.2.2.isLt
  intro i
  rcases fin3 i with rfl | rfl | rfl <;> simp [Triple.at, right] <;> omega

private theorem square_sub (x t : Int) : (x-t)*(x-t) = x*x-2*(t*x)+t*t := by
  simp only [Int.sub_mul, Int.mul_sub]
  rw [Int.mul_comm x t]
  omega

private theorem square_add (x t : Int) : (x+2*t)*(x+2*t) = x*x+4*(t*x)+4*(t*t) := by
  simp only [Int.add_mul, Int.mul_add]
  rw [show x*(2*t)=2*(t*x) by ac_rfl, show (2*t)*x=2*(t*x) by ac_rfl,
    show (2*t)*(2*t) = 4*(t*t) by
      rw [show (4:Int)=2*2 by decide]; ac_rfl]
  omega

/-- The reflection in the plane perpendicular to `(1, 1, -2)` at the
    integral input `(3a, 3b, 3c)` preserves both power sums. -/
theorem reflection_equations (a b c : Int) :
    equations ⟨3*a,3*b,3*c⟩ ⟨2*a-b+2*c,-a+2*b+2*c,2*a+2*b-c⟩ := by
  let t := a+b-2*c
  have h₀ : 2*a-b+2*c = 3*a-t := by dsimp [t]; omega
  have h₁ : -a+2*b+2*c = 3*b-t := by dsimp [t]; omega
  have h₂ : 2*a+2*b-c = 3*c+2*t := by dsimp [t]; omega
  constructor
  · simp only [linear, h₀, h₁, h₂]; omega
  · have ht : 3*a + 3*b - 2*(3*c) = 3*t := by dsimp [t]; omega
    have ht' := congrArg (t * ·) ht
    simp only [Int.mul_sub, Int.mul_add] at ht'
    rw [show t*(2*(3*c)) = 2*(t*(3*c)) by ac_rfl,
      show t*(3*t) = 3*(t*t) by ac_rfl] at ht'
    simp only [quadratic, h₀, h₁, h₂, square_sub, square_add]
    omega

theorem same_power_sums (M : Nat) (p : Box M) : equations (left M p) (right M p) :=
  reflection_equations _ _ _

theorem not_diagonal (M : Nat) (p : Box M) : ¬ diagonal (left M p) (right M p) := by
  rintro ⟨σ, hinj, hσ⟩
  have h₁ := p.1.isLt
  have h₂ := p.2.1.isLt
  have h₃ := p.2.2.isLt
  have pos₀ : σ 0 = 2 := by
    have h := hσ 0
    rcases fin3 (σ 0) with h0 | h1 | h2
    · rw [h0] at h; simp [Triple.at, left, right] at h; omega
    · rw [h1] at h; simp [Triple.at, left, right] at h; omega
    · exact h2
  have pos₁ : σ 1 = 2 := by
    have h := hσ 1
    rcases fin3 (σ 1) with h0 | h1 | h2
    · rw [h0] at h; simp [Triple.at, left, right] at h; omega
    · rw [h1] at h; simp [Triple.at, left, right] at h; omega
    · exact h2
  exact (by decide : (0 : Fin 3) ≠ 1) (hinj (pos₀.trans pos₁.symm))

def family (M : Nat) (p : Box M) : OffDiagonal (12*M) :=
  ⟨(left M p, right M p), left_bounded M p, right_bounded M p, same_power_sums M p,
    fun m => ⟨congrArg (· % m) (same_power_sums M p).1,
      congrArg (· % m) (same_power_sums M p).2⟩, not_diagonal M p⟩

theorem family_injective (M : Nat) : injective (family M) := by
  intro p q h
  have hleft : left M p = left M q := congrArg (fun s => s.val.1) h
  have ha := congrArg Triple.a hleft
  have hb := congrArg Triple.b hleft
  have hc := congrArg Triple.c hleft
  simp [left] at ha hb hc
  apply Prod.ext
  · apply Fin.ext; omega
  · apply Prod.ext <;> apply Fin.ext <;> omega

/-- The cubic family of pairwise distinct, bounded off-diagonal solutions. -/
theorem cubic_off_diagonal (M : Nat) : ∃ f : Box M → OffDiagonal (12*M), injective f :=
  ⟨family M, family_injective M⟩

#print axioms cubic_off_diagonal

end Vinogradov
