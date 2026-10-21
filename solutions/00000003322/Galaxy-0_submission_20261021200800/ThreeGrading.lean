import ThreeRing
namespace ThreePoly

/-- The standard total-degree grading, on the actual coefficient family. -/
def Homogeneous (p : Poly) (d : Nat) : Prop :=
  ∀ i j k, p.coeff i j k = true → i+j+k=d

/-- The degree of a coefficient in the shifted free summand R(-s). -/
def ShiftHomogeneous (p : Poly) (s d : Nat) : Prop :=
  ∀ i j k, p.coeff i j k = true → i+j+k+s=d

def ShiftHomogeneousZ (p : Poly) (s : Nat) (d : Int) : Prop :=
  ∀ i j k, p.coeff i j k = true → (i : Int)+(j : Int)+(k : Int)+(s : Int)=d

theorem shift_homogeneous_iff (p : Poly) (d s : Nat) :
    ShiftHomogeneous p s (d+s) ↔ Homogeneous p d := by
  constructor <;> intro h i j k hc <;> have hd := h i j k hc <;> omega

@[simp] theorem zero_homogeneous (d : Nat) : Homogeneous zero d := by
  intro i j k h; cases h
@[simp] theorem zero_shift_homogeneous (s d : Nat) : ShiftHomogeneous zero s d := by
  intro i j k h; cases h

theorem one_homogeneous : Homogeneous one 0 := by
  intro i j k h
  have := of_decide_eq_true h
  omega

theorem constant_homogeneous (c : Bool) : Homogeneous (constant c) 0 := by
  cases c
  · exact zero_homogeneous 0
  · exact one_homogeneous

theorem one_shift_homogeneous (s : Nat) : ShiftHomogeneous one s s := by
  intro i j k h
  have := one_homogeneous i j k h
  omega

theorem constant_shift_homogeneous (c : Bool) (s : Nat) : ShiftHomogeneous (constant c) s s := by
  cases c
  · exact zero_shift_homogeneous s s
  · exact one_shift_homogeneous s

theorem homogeneous_add {p q : Poly} {d : Nat}
    (hp : Homogeneous p d) (hq : Homogeneous q d) : Homogeneous (add p q) d := by
  intro i j k h
  have hor : p.coeff i j k = true ∨ q.coeff i j k = true := by
    cases ha : p.coeff i j k <;> cases hb : q.coeff i j k <;> simp_all
  exact hor.elim (hp i j k) (hq i j k)

namespace Raw

theorem coeff_true_mem {p : Poly} {i j k : Nat} (h : coeff p i j k = true) : (i,j,k) ∈ p := by
  induction p with
  | nil => cases h
  | cons m p ih =>
    rcases m with ⟨a,b,c⟩
    by_cases he : (a,b,c) = (i,j,k)
    · exact List.mem_cons.mpr (Or.inl he.symm)
    · have hz : ((a == i) && (b == j) && (c == k)) = false := by
        apply Bool.eq_false_iff.mpr
        intro hab
        simp only [Bool.and_eq_true, beq_iff_eq] at hab
        exact he (Prod.ext hab.1.1 (Prod.ext hab.1.2 hab.2))
      rw [coeff_cons, hz, Bool.false_xor] at h
      exact List.mem_cons.mpr (Or.inr (ih h))

theorem row_mem {f : Nat → Bool} {a b n : Nat} {m : Monomial}
    (hm : m ∈ row f a b n) : m.1 = a ∧ m.2.1 = b ∧ f m.2.2 = true := by
  induction n with
  | zero => cases hm
  | succ n ih =>
    simp only [row, List.mem_append] at hm
    rcases hm with h | h
    · cases hf : f n
      · simp only [hf, Bool.false_eq_true, ↓reduceIte, List.not_mem_nil] at h
      · simp only [hf, ↓reduceIte, List.mem_singleton] at h
        subst m
        exact ⟨rfl,rfl,hf⟩
    · exact ih h

theorem plane_mem {f : Nat → Nat → Bool} {a n k : Nat} {m : Monomial}
    (hm : m ∈ plane f a k n) : m.1 = a ∧ f m.2.1 m.2.2 = true := by
  induction n with
  | zero => cases hm
  | succ n ih =>
    simp only [plane, List.mem_append] at hm
    rcases hm with h | h
    · obtain ⟨he,he',hf⟩ := row_mem h
      exact ⟨he, by rw [he']; exact hf⟩
    · exact ih h

theorem box_mem {f : Nat → Nat → Nat → Bool} {l n k : Nat} {m : Monomial}
    (hm : m ∈ box f l k n) : f m.1 m.2.1 m.2.2 = true := by
  induction n with
  | zero => cases hm
  | succ n ih =>
    simp only [box, List.mem_append] at hm
    rcases hm with h | h
    · obtain ⟨he,hf⟩ := plane_mem h
      rw [he]
      exact hf
    · exact ih h

theorem mul_monomial_degree {p q : Poly} {d e : Nat}
    (hp : ∀ m ∈ p, m.1 + m.2.1 + m.2.2 = d)
    (hq : ∀ m ∈ q, m.1 + m.2.1 + m.2.2 = e) :
    ∀ m ∈ mul p q, m.1 + m.2.1 + m.2.2 = d+e := by
  induction p with
  | nil => intro m hm; cases hm
  | cons a p ih =>
    rcases a with ⟨a,b,c⟩
    intro m hm
    simp only [mul, List.mem_append] at hm
    rcases hm with hm | hm
    · obtain ⟨v,hv,he⟩ := List.mem_map.mp hm
      have hd := hp (a,b,c) (by simp)
      have hedeg := hq v hv
      change (a+v.1,b+v.2.1,c+v.2.2) = m at he
      subst m
      dsimp only at hd hedeg ⊢
      omega
    · exact ih (fun v hv => hp v (List.mem_cons.mpr (Or.inr hv))) m hm

end Raw

/-- Every homogeneous polynomial has a genuine homogeneous finite monomial sum. -/
theorem homogeneous_raw_representation {p : Poly} {d : Nat} (hp : Homogeneous p d) :
    ∃ l : Raw.Poly, ofRaw l = p ∧ ∀ m ∈ l, m.1+m.2.1+m.2.2=d := by
  obtain ⟨N,hN⟩ := p.finite
  refine ⟨Raw.box p.coeff N N N, ?_, ?_⟩
  · apply Poly.ext
    intro i j k
    rw [ofRaw_coeff, Raw.coeff_box]
    by_cases h : i<N ∧ j<N ∧ k<N
    · exact if_pos h
    · rw [if_neg h]
      exact (hN i j k (by omega)).symm
  · intro m hm
    exact hp m.1 m.2.1 m.2.2 (Raw.box_mem hm)

/-- Actual multiplication respects the total-degree grading. -/
theorem homogeneous_mul {p q : Poly} {d e : Nat}
    (hp : Homogeneous p d) (hq : Homogeneous q e) : Homogeneous (mul p q) (d+e) := by
  obtain ⟨a,rfl,ha⟩ := homogeneous_raw_representation hp
  obtain ⟨b,rfl,hb⟩ := homogeneous_raw_representation hq
  rw [mul_ofRaw]
  intro i j k h
  exact Raw.mul_monomial_degree ha hb (i,j,k) (Raw.coeff_true_mem h)

theorem xMul_homogeneous_iff (p : Poly) (d : Nat) :
    Homogeneous (xMul p) (d+1) ↔ Homogeneous p d := by
  constructor
  · intro h i j k hc
    have hd := h (i+1) j k hc
    omega
  · intro h i j k hc
    cases i with
    | zero => cases hc
    | succ i => have hd := h i j k hc; omega

theorem xMul_shift_homogeneous_iff (p : Poly) (s d : Nat) :
    ShiftHomogeneous (xMul p) s d ↔ ShiftHomogeneous p (s+1) d := by
  constructor
  · intro h i j k hc
    have hd := h (i+1) j k hc
    omega
  · intro h i j k hc
    cases i with
    | zero => cases hc
    | succ i => have hd := h i j k hc; omega

theorem X_homogeneous : Homogeneous X 1 :=
  (xMul_homogeneous_iff one 0).mpr one_homogeneous

theorem yMul_homogeneous_iff (p : Poly) (d : Nat) :
    Homogeneous (yMul p) (d+1) ↔ Homogeneous p d := by
  constructor
  · intro h i j k hc
    have hd := h i (j+1) k hc
    omega
  · intro h i j k hc
    cases j with
    | zero => cases hc
    | succ j => have hd := h i j k hc; omega

theorem yMul_shift_homogeneous_iff (p : Poly) (s d : Nat) :
    ShiftHomogeneous (yMul p) s d ↔ ShiftHomogeneous p (s+1) d := by
  constructor
  · intro h i j k hc
    have hd := h i (j+1) k hc
    omega
  · intro h i j k hc
    cases j with
    | zero => cases hc
    | succ j => have hd := h i j k hc; omega

theorem Y_homogeneous : Homogeneous Y 1 :=
  (yMul_homogeneous_iff one 0).mpr one_homogeneous

theorem zMul_homogeneous_iff (p : Poly) (d : Nat) :
    Homogeneous (zMul p) (d+1) ↔ Homogeneous p d := by
  constructor
  · intro h i j k hc
    have hd := h i j (k+1) hc
    omega
  · intro h i j k hc
    cases k with
    | zero => cases hc
    | succ k => have hd := h i j k hc; omega

theorem zMul_shift_homogeneous_iff (p : Poly) (s d : Nat) :
    ShiftHomogeneous (zMul p) s d ↔ ShiftHomogeneous p (s+1) d := by
  constructor
  · intro h i j k hc
    have hd := h i j (k+1) hc
    omega
  · intro h i j k hc
    cases k with
    | zero => cases hc
    | succ k => have hd := h i j k hc; omega

theorem Z_homogeneous : Homogeneous Z 1 :=
  (zMul_homogeneous_iff one 0).mpr one_homogeneous

end ThreePoly
