import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.List.Count
import Lean.Elab.Tactic.Omega

namespace FixedAlphabetA1

/-- A normal crystal for the one-colour A1 Cartan datum: root=2, weight lattice Z. -/
structure A1Crystal (V : Type) where
  wt : V → ℤ
  eps : V → ℕ
  phi : V → ℕ
  e : V → Option V
  f : V → Option V
  balance : ∀ x, (phi x : ℤ) = (eps x : ℤ) + wt x
  inverse : ∀ x y, f x = some y ↔ e y = some x
  e_none : ∀ x, e x = none ↔ eps x = 0
  f_none : ∀ x, f x = none ↔ phi x = 0
  f_eps : ∀ x y, f x = some y → eps y = eps x + 1
  f_phi : ∀ x y, f x = some y → phi y + 1 = phi x
  f_wt : ∀ x y, f x = some y → wt y = wt x - 2

namespace A1Crystal
variable {V W : Type}

theorem e_eps (A : A1Crystal V) {x y} (h : A.e x = some y) :
    A.eps y + 1 = A.eps x := (A.f_eps y x ((A.inverse y x).mpr h)).symm
theorem e_phi (A : A1Crystal V) {x y} (h : A.e x = some y) :
    A.phi y = A.phi x + 1 := (A.f_phi y x ((A.inverse y x).mpr h)).symm
theorem e_wt (A : A1Crystal V) {x y} (h : A.e x = some y) :
    A.wt y = A.wt x + 2 := by
  have t := A.f_wt y x ((A.inverse y x).mpr h)
  omega

def te (A : A1Crystal V) (B : A1Crystal W) (p : V×W) : Option (V×W) :=
  if B.phi p.2 < A.eps p.1 then (A.e p.1).map (fun x => (x,p.2))
  else (B.e p.2).map (fun y => (p.1,y))
def tf (A : A1Crystal V) (B : A1Crystal W) (p : V×W) : Option (V×W) :=
  if B.phi p.2 ≤ A.eps p.1 then (A.f p.1).map (fun x => (x,p.2))
  else (B.f p.2).map (fun y => (p.1,y))
def teps (A : A1Crystal V) (B : A1Crystal W) (p : V×W) : ℕ :=
  B.eps p.2 + (A.eps p.1 - B.phi p.2)
def tphi (A : A1Crystal V) (B : A1Crystal W) (p : V×W) : ℕ :=
  A.phi p.1 + (B.phi p.2 - A.eps p.1)

theorem te_iff (A : A1Crystal V) (B : A1Crystal W) (x x' : V) (y y' : W) :
    te A B (x,y) = some (x',y') ↔
    (B.phi y < A.eps x ∧ A.e x = some x' ∧ y = y') ∨
    (A.eps x ≤ B.phi y ∧ x = x' ∧ B.e y = some y') := by
  by_cases h : B.phi y < A.eps x
  · simp [te,h,Option.map_eq_some_iff,Prod.mk.injEq,Nat.not_le.mpr h]
  · have hn : A.eps x ≤ B.phi y := by omega
    simp [te,h,hn,Option.map_eq_some_iff,Prod.mk.injEq,and_comm]

theorem tf_iff (A : A1Crystal V) (B : A1Crystal W) (x x' : V) (y y' : W) :
    tf A B (x,y) = some (x',y') ↔
    (B.phi y ≤ A.eps x ∧ A.f x = some x' ∧ y = y') ∨
    (A.eps x < B.phi y ∧ x = x' ∧ B.f y = some y') := by
  by_cases h : B.phi y ≤ A.eps x
  · have hn : ¬ A.eps x < B.phi y := by omega
    simp [tf,h,hn,Option.map_eq_some_iff,Prod.mk.injEq]
  · have hn : A.eps x < B.phi y := by omega
    simp [tf,h,hn,Option.map_eq_some_iff,Prod.mk.injEq,and_comm]

theorem tensor_inverse (A : A1Crystal V) (B : A1Crystal W) (p q : V×W) :
    tf A B p = some q ↔ te A B q = some p := by
  rcases p with ⟨x,y⟩
  rcases q with ⟨x',y'⟩
  rw [tf_iff,te_iff]
  constructor
  · intro h
    rcases h with ⟨hc,hf,rfl⟩ | ⟨hc,rfl,hf⟩
    · left
      refine ⟨?_, (A.inverse x x').mp hf, rfl⟩
      have he := A.f_eps x x' hf
      omega
    · right
      refine ⟨?_,rfl,(B.inverse y y').mp hf⟩
      have hp := B.f_phi y y' hf
      omega
  · intro h
    rcases h with ⟨hc,he,rfl⟩ | ⟨hc,rfl,he⟩
    · left
      refine ⟨?_,(A.inverse x x').mpr he,rfl⟩
      have hx := A.e_eps he
      omega
    · right
      refine ⟨?_,rfl,(B.inverse y y').mpr he⟩
      have hy := B.e_phi he
      omega

def tensor (A : A1Crystal V) (B : A1Crystal W) : A1Crystal (V×W) where
  wt p := A.wt p.1+B.wt p.2
  eps := teps A B
  phi := tphi A B
  e := te A B
  f := tf A B
  balance p := by
    have ha := A.balance p.1
    have hb := B.balance p.2
    unfold teps tphi
    omega
  inverse := tensor_inverse A B
  e_none p := by
    unfold te teps
    split
    · have hp : A.eps p.1 ≠ 0 := by omega
      have hn : A.e p.1 ≠ none := fun h => hp ((A.e_none p.1).mp h)
      cases h : A.e p.1 <;> simp_all
      omega
    · simp only [Option.map_eq_none_iff, B.e_none]
      omega
  f_none p := by
    unfold tf tphi
    split
    · simp only [Option.map_eq_none_iff, A.f_none]
      omega
    · have hp : B.phi p.2 ≠ 0 := by omega
      have hn : B.f p.2 ≠ none := fun h => hp ((B.f_none p.2).mp h)
      cases h : B.f p.2 <;> simp_all
      omega
  f_eps p q h := by
    rcases p with ⟨x,y⟩
    rcases q with ⟨x',y'⟩
    rcases (tf_iff A B x x' y y').mp h with ⟨hc,hf,rfl⟩ | ⟨hc,rfl,hf⟩
    · have he := A.f_eps x x' hf
      unfold teps
      simp only [Prod.fst,Prod.snd] at *
      omega
    · have he := B.f_eps y y' hf
      have hp := B.f_phi y y' hf
      unfold teps
      simp only [Prod.fst,Prod.snd] at *
      omega
  f_phi p q h := by
    rcases p with ⟨x,y⟩
    rcases q with ⟨x',y'⟩
    rcases (tf_iff A B x x' y y').mp h with ⟨hc,hf,rfl⟩ | ⟨hc,rfl,hf⟩
    · have he := A.f_eps x x' hf
      have hp := A.f_phi x x' hf
      unfold tphi
      simp only [Prod.fst,Prod.snd] at *
      omega
    · have hp := B.f_phi y y' hf
      unfold tphi
      simp only [Prod.fst,Prod.snd] at *
      omega
  f_wt p q h := by
    rcases p with ⟨x,y⟩
    rcases q with ⟨x',y'⟩
    rcases (tf_iff A B x x' y y').mp h with ⟨hc,hf,rfl⟩ | ⟨hc,rfl,hf⟩
    · have hw := A.f_wt x x' hf
      simp only [Prod.fst,Prod.snd] at *
      omega
    · have hw := B.f_wt y y' hf
      simp only [Prod.fst,Prod.snd] at *
      omega

end A1Crystal
end FixedAlphabetA1
