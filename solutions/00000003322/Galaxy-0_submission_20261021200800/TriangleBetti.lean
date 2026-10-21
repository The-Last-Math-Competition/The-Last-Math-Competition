import TriangleGraded

namespace TLMC3322.Triangle

/-- Induced differentials of the actual residue complex, via canonical lifts. -/
def residueD0 (_ : Bool) : Unit := ()
def residueD1 (v : Residue3) : Bool := reduce0 (differential1 (lift3 v))
def residueD2 (v : Residue2) : Residue3 := reduce3 (differential2 (lift2 v))
def residueD3 (_ : Unit) : Residue2 := residueZero2

@[simp] theorem residueD1_zero (v : Residue3) : residueD1 v = false := rfl
@[simp] theorem residueD2_zero (v : Residue2) : residueD2 v = residueZero3 := rfl

theorem residueD1_descends (v : Free3) :
    residueD1 (reduce3 v) = reduce0 (differential1 v) := rfl

theorem residueD2_descends (v : Free2) :
    residueD2 (reduce2 v) = reduce3 (differential2 v) := rfl

theorem residueD1_image (b : Bool) : (∃ v, residueD1 v = b) ↔ b = false := by
  simp [eq_comm]
theorem residueD2_image (v : Residue3) : (∃ u, residueD2 u = v) ↔ v = residueZero3 := by
  simp [eq_comm]
theorem residueD3_image (v : Residue2) : (∃ u, residueD3 u = v) ↔ v = residueZero2 := by
  simp [residueD3,eq_comm]

/-- Nonzero homogeneous homology: a cycle whose class is not a boundary.
The tail module in homological degrees >=3 is zero. -/
def HomologySupport (i d : Nat) : Prop :=
  match i with
  | 0 => ∃ b : Bool, (¬ ∃ v, residueD1 v = b) ∧
      residueD0 b = () ∧ ReducedHomogeneous b 0 d
  | 1 => ∃ v : Residue3, (¬ ∃ u, residueD2 u = v) ∧
      residueD1 v = false ∧ ReducedHom3 v 2 d
  | 2 => ∃ v : Residue2, (¬ ∃ u, residueD3 u = v) ∧
      residueD2 v = residueZero3 ∧ ReducedHom2 v 3 d
  | _+3 => False

/-- After reducing the verified resolution modulo m, both differentials vanish.
Consequently the nonzero homogeneous residue vectors are precisely nonzero
homology classes. The zero module occurs in every homological degree >= 3. -/
def BettiSupport (i d : Nat) : Prop :=
  match i with
  | 0 => ∃ b : Bool, b ≠ false ∧ ReducedHomogeneous b 0 d
  | 1 => ∃ v : Residue3, v ≠ residueZero3 ∧ ReducedHom3 v 2 d
  | 2 => ∃ v : Residue2, v ≠ residueZero2 ∧ ReducedHom2 v 3 d
  | _+3 => False

theorem betti_support_is_homology (i d : Nat) : BettiSupport i d ↔ HomologySupport i d := by
  cases i with
  | zero => simp only [BettiSupport,HomologySupport,residueD1_image,residueD0,true_and]
  | succ i =>
    cases i with
    | zero => simp only [BettiSupport,HomologySupport,residueD2_image,residueD1_zero,true_and]
    | succ i =>
      cases i with
      | zero => simp only [BettiSupport,HomologySupport,residueD3_image,residueD2_zero,true_and]
      | succ i => rfl

theorem scalar_support (s d : Nat) :
    (∃ b : Bool, b ≠ false ∧ ReducedHomogeneous b s d) ↔ d = s := by
  constructor
  · rintro ⟨b,hb,hd⟩
    cases b with
    | false => exact False.elim (hb rfl)
    | true => exact hd rfl
  · intro h
    exact ⟨true,by decide,fun _ => h⟩

theorem rank_two_support (s d : Nat) :
    (∃ v : Residue2, v ≠ residueZero2 ∧ ReducedHom2 v s d) ↔ d = s := by
  constructor
  · rintro ⟨⟨a,b⟩,hn,hd⟩
    cases a <;> cases b <;> simp_all [residueZero2,ReducedHom2,ReducedHomogeneous]
  · intro h
    exact ⟨(true,false),by decide,(fun _ => h),by intro h; contradiction⟩

theorem rank_three_support (s d : Nat) :
    (∃ v : Residue3, v ≠ residueZero3 ∧ ReducedHom3 v s d) ↔ d = s := by
  constructor
  · rintro ⟨⟨a,b,c⟩,hn,hd⟩
    cases a <;> cases b <;> cases c <;>
      simp_all [residueZero3,ReducedHom3,ReducedHomogeneous]
  · intro h
    exact ⟨(true,false,false),by decide,(fun _ => h),
      (by intro h; contradiction),(by intro h; contradiction)⟩

theorem betti_support_iff (i d : Nat) : BettiSupport i d ↔
    (i=0 ∧ d=0) ∨ (i=1 ∧ d=2) ∨ (i=2 ∧ d=3) := by
  cases i with
  | zero => simp only [BettiSupport,scalar_support]; simp
  | succ i =>
    cases i with
    | zero => simp only [BettiSupport,rank_three_support]; simp
    | succ i =>
      cases i with
      | zero => simp only [BettiSupport,rank_two_support]; simp
      | succ i => simp [BettiSupport]

/-- Standard minimal-resolution characterization reg M = max{d-i : beta_i,d != 0}. -/
def Regularity (r : Int) : Prop :=
  (∀ i d, BettiSupport i d → (d : Int) - (i : Int) ≤ r) ∧
  ∃ i d, BettiSupport i d ∧ (d : Int) - (i : Int) = r

theorem regularity_one : Regularity 1 := by
  constructor
  · intro i d h
    rcases (betti_support_iff i d).mp h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> decide
  · exact ⟨1,2,(betti_support_iff 1 2).mpr (Or.inr (Or.inl ⟨rfl,rfl⟩)),rfl⟩

end TLMC3322.Triangle
