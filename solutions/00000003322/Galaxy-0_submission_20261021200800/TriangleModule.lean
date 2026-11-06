import TriangleCore
import ThreeGrading
import Graphs

namespace TLMC3322.Triangle
open ThreePoly
noncomputable section

def mul2 (r : Poly) (v : Free2) : Free2 := (mul r v.1,mul r v.2)
def mul3 (r : Poly) (v : Free3) : Free3 :=
  (mul r v.1,mul r v.2.1,mul r v.2.2)

theorem differential1_linear (r : Poly) (v : Free3) :
    differential1 (mul3 r v) = mul r (differential1 v) := by
  simp only [differential1,mul3,mul_add,mul_xMul,mul_yMul,mul_zMul]

theorem differential2_linear (r : Poly) (v : Free2) :
    differential2 (mul2 r v) = mul3 r (differential2 v) := by
  simp only [differential2,mul2,mul3,mul_add,mul_xMul,mul_yMul,mul_zMul]

theorem ideal_mul (r : Poly) {p : Poly} (h : InIdeal p) : InIdeal (mul r p) := by
  obtain ⟨v,rfl⟩ := h
  exact ⟨mul3 r v,(differential1_linear r v).symm⟩

def IsIdeal (I : Poly → Prop) : Prop :=
  I zero ∧ (∀ p q, I p → I q → I (add p q)) ∧
  (∀ r p, I p → I (mul r p))

theorem ideal_laws : IsIdeal InIdeal :=
  ⟨ideal_zero,fun _ _ => ideal_add,fun r _ => ideal_mul r⟩

def e0 : Free3 := (one,zero,zero)
def e1 : Free3 := (zero,one,zero)
def e2 : Free3 := (zero,zero,one)

theorem generator_xy : differential1 e0 = mul X Y := by
  simp only [differential1,e0,xMul_zero,yMul_zero,zMul_zero,add_zero,X_mul]
  rfl

theorem generator_xz : differential1 e1 = mul X Z := by
  simp only [differential1,e1,xMul_zero,yMul_zero,zMul_zero,add_zero,zero_add,X_mul]
  rfl

theorem generator_yz : differential1 e2 = mul Y Z := by
  simp only [differential1,e2,xMul_zero,yMul_zero,zMul_zero,add_zero,zero_add,Y_mul]
  rfl

def vertexVariable (v : Fin 3) : Poly := if v.val=0 then X else if v.val=1 then Y else Z

def IsEdgeIdeal (I : Poly → Prop) : Prop :=
  IsIdeal I ∧
  (∀ u v, Graphs.K3 u v = true → I (mul (vertexVariable u) (vertexVariable v))) ∧
  (∀ J : Poly → Prop, IsIdeal J →
    (∀ u v, Graphs.K3 u v = true → J (mul (vertexVariable u) (vertexVariable v))) →
    ∀ p, I p → J p)

theorem actual_edge_ideal : IsEdgeIdeal InIdeal := by
  have hxy : InIdeal (mul X Y) := ⟨e0,generator_xy.symm⟩
  have hxz : InIdeal (mul X Z) := ⟨e1,generator_xz.symm⟩
  have hyz : InIdeal (mul Y Z) := ⟨e2,generator_yz.symm⟩
  refine ⟨ideal_laws,?_,?_⟩
  · intro u v huv
    have he : (u=0 ∧ v=1) ∨ (u=0 ∧ v=2) ∨ (u=1 ∧ v=0) ∨
        (u=1 ∧ v=2) ∨ (u=2 ∧ v=0) ∨ (u=2 ∧ v=1) := by
      have hh : ∀ u v : Fin 3, Graphs.K3 u v = true →
        (u=0 ∧ v=1) ∨ (u=0 ∧ v=2) ∨ (u=1 ∧ v=0) ∨
        (u=1 ∧ v=2) ∨ (u=2 ∧ v=0) ∨ (u=2 ∧ v=1) := by decide
      exact hh u v huv
    rcases he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ |
      ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact hxy
    · exact hxz
    · change InIdeal (mul Y X); rw [mul_comm]; exact hxy
    · exact hyz
    · change InIdeal (mul Z X); rw [mul_comm]; exact hxz
    · change InIdeal (mul Z Y); rw [mul_comm]; exact hyz
  · rintro J hJ hj p ⟨v,rfl⟩
    have hxy : J (mul X Y) := hj 0 1 (by decide)
    have hxz : J (mul X Z) := hj 0 2 (by decide)
    have hyz : J (mul Y Z) := hj 1 2 (by decide)
    have ha := hJ.2.2 v.1 (mul X Y) hxy
    have hb := hJ.2.2 v.2.1 (mul X Z) hxz
    have hc := hJ.2.2 v.2.2 (mul Y Z) hyz
    rw [mul_comm v.1,mul_assoc,X_mul,Y_mul] at ha
    rw [mul_comm v.2.1,mul_assoc,X_mul,Z_mul] at hb
    rw [mul_comm v.2.2,mul_assoc,Y_mul,Z_mul] at hc
    exact hJ.2.1 _ _ (hJ.2.1 _ _ ha hb) hc

theorem add_cancel_middle (p q r : Poly) : add (add p q) (add q r) = add p r := by
  apply Poly.ext
  intro i j k
  simp only [add_coeff]
  generalize p.coeff i j k = a; generalize q.coeff i j k = b; generalize r.coeff i j k = c
  revert a b c; decide

theorem add_four (p q r s : Poly) : add (add p q) (add r s) = add (add p r) (add q s) := by
  apply Poly.ext
  intro i j k
  simp only [add_coeff]
  generalize p.coeff i j k = a; generalize q.coeff i j k = b
  generalize r.coeff i j k = c; generalize s.coeff i j k = d
  revert a b c d; decide

def idealSetoid : Setoid Poly where
  r p q := InIdeal (add p q)
  iseqv := {
    refl := fun p => by simpa using ideal_zero
    symm := fun {p q} h => by simpa only [add_comm q p] using h
    trans := fun {p q r} h h' => by
      have hh := ideal_add h h'
      simpa only [add_cancel_middle] using hh }

abbrev QuotientModule := Quotient idealSetoid
def project (p : Poly) : QuotientModule := Quotient.mk idealSetoid p

def quotientAdd (p q : QuotientModule) : QuotientModule :=
  Quotient.liftOn₂ p q (fun a b => project (add a b)) (by
    intro a b c d hac hbd
    apply Quotient.sound
    change InIdeal (add (add a b) (add c d))
    rw [add_four]
    exact ideal_add hac hbd)

def quotientMul (r : Poly) (p : QuotientModule) : QuotientModule :=
  Quotient.liftOn p (fun a => project (mul r a)) (by
    intro a b h
    apply Quotient.sound
    change InIdeal (add (mul r a) (mul r b))
    rw [← mul_add]
    exact ideal_mul r h)

@[simp] theorem project_add (p q : Poly) :
    project (add p q) = quotientAdd (project p) (project q) := rfl
@[simp] theorem project_mul (r p : Poly) :
    project (mul r p) = quotientMul r (project p) := rfl

theorem projection_surjective (q : QuotientModule) : ∃ p, project p = q := by
  induction q using Quotient.inductionOn with
  | _ p => exact ⟨p,rfl⟩

theorem projection_kernel (p : Poly) : project p = project zero ↔ InIdeal p := by
  constructor
  · intro h
    have hh : InIdeal (add p zero) := Quotient.exact h
    simpa only [add_zero] using hh
  · intro h
    apply Quotient.sound
    change InIdeal (add p zero)
    simpa only [add_zero] using h

theorem quotient_module_laws :
    (∀ a b, quotientAdd a b = quotientAdd b a) ∧
    (∀ a b c, quotientAdd (quotientAdd a b) c = quotientAdd a (quotientAdd b c)) ∧
    (∀ a, quotientAdd a (project zero) = a ∧ quotientAdd a a = project zero) ∧
    (∀ a, quotientMul one a = a) ∧
    (∀ r s a, quotientMul (mul r s) a = quotientMul r (quotientMul s a)) ∧
    (∀ r a b, quotientMul r (quotientAdd a b) = quotientAdd (quotientMul r a) (quotientMul r b)) ∧
    (∀ r s a, quotientMul (add r s) a = quotientAdd (quotientMul r a) (quotientMul s a)) := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · intro a b
    obtain ⟨a,rfl⟩ := projection_surjective a
    obtain ⟨b,rfl⟩ := projection_surjective b
    exact congrArg project (add_comm a b)
  · intro a b c
    obtain ⟨a,rfl⟩ := projection_surjective a
    obtain ⟨b,rfl⟩ := projection_surjective b
    obtain ⟨c,rfl⟩ := projection_surjective c
    exact congrArg project (add_assoc a b c)
  · intro a
    obtain ⟨a,rfl⟩ := projection_surjective a
    exact ⟨congrArg project (add_zero a),congrArg project (add_self a)⟩
  · intro a
    obtain ⟨a,rfl⟩ := projection_surjective a
    exact congrArg project (one_mul a)
  · intro r s a
    obtain ⟨a,rfl⟩ := projection_surjective a
    exact congrArg project (mul_assoc r s a)
  · intro r a b
    obtain ⟨a,rfl⟩ := projection_surjective a
    obtain ⟨b,rfl⟩ := projection_surjective b
    exact congrArg project (mul_add r a b)
  · intro r s a
    obtain ⟨a,rfl⟩ := projection_surjective a
    exact congrArg project (add_mul r s a)

end
end TLMC3322.Triangle
