import PolynomialRingExtras
import BettiSupport
namespace TLMC506
namespace Raw

theorem coeff_true_mem {p : Poly} {i j : Nat} (h : coeff p i j = true) : (i,j) ∈ p := by
  induction p with
  | nil => cases h
  | cons m p ih =>
    rcases m with ⟨a,b⟩
    by_cases he : (a,b) = (i,j)
    · exact List.mem_cons.mpr (Or.inl he.symm)
    · have hz : ((a == i) && (b == j)) = false := by
        apply Bool.eq_false_iff.mpr
        intro hab
        have hab' := (Bool.and_eq_true _ _).mp hab
        exact he (Prod.ext (beq_iff_eq.mp hab'.1) (beq_iff_eq.mp hab'.2))
      rw [coeff_cons, hz, Bool.false_xor] at h
      exact List.mem_cons.mpr (Or.inr (ih h))

theorem row_mem {f : Nat → Bool} {a n : Nat} {m : Monomial}
    (hm : m ∈ row f a n) : m.1 = a ∧ f m.2 = true := by
  induction n with
  | zero => cases hm
  | succ n ih =>
    simp only [row, List.mem_append] at hm
    rcases hm with h | h
    · cases hf : f n
      · simp only [hf, Bool.false_eq_true, ↓reduceIte, List.not_mem_nil] at h
      · simp only [hf, ↓reduceIte, List.mem_singleton] at h
        subst m
        exact ⟨rfl,hf⟩
    · exact ih h

theorem box_mem {f : Nat → Nat → Bool} {n k : Nat} {m : Monomial}
    (hm : m ∈ box f k n) : f m.1 m.2 = true := by
  induction n with
  | zero => cases hm
  | succ n ih =>
    simp only [box, List.mem_append] at hm
    rcases hm with h | h
    · obtain ⟨he,hf⟩ := row_mem h
      rw [he]
      exact hf
    · exact ih h

theorem mul_monomial_degree {p q : Poly} {d e : Nat}
    (hp : ∀ m ∈ p, m.1 + m.2 = d)
    (hq : ∀ m ∈ q, m.1 + m.2 = e) :
    ∀ m ∈ mul p q, m.1 + m.2 = d+e := by
  induction p with
  | nil => intro m hm; cases hm
  | cons a p ih =>
    rcases a with ⟨a,b⟩
    intro m hm
    simp only [mul, List.mem_append] at hm
    rcases hm with hm | hm
    · obtain ⟨v,hv,he⟩ := List.mem_map.mp hm
      have hd := hp (a,b) (by simp)
      have hedeg := hq v hv
      change (a+v.1,b+v.2) = m at he
      subst m
      omega
    · exact ih (fun v hv => hp v (List.mem_cons.mpr (Or.inr hv))) m hm

end Raw

/-- A homogeneous polynomial can be represented without spurious cancelling
monomials of other degrees. This uses the actual finite coefficient rectangle. -/
theorem homogeneous_raw_representation {p : Poly} {d : Nat} (hp : Homogeneous p d) :
    ∃ l : Raw.Poly, ofRaw l = p ∧ ∀ m ∈ l, m.1+m.2=d := by
  obtain ⟨N,hN⟩ := p.finite
  refine ⟨Raw.box p.coeff N N, ?_, ?_⟩
  · apply Poly.ext
    intro i j
    rw [ofRaw_coeff, Raw.coeff_box]
    by_cases h : i<N ∧ j<N
    · exact if_pos h
    · rw [if_neg h]
      exact (hN i j (by omega)).symm
  · intro m hm
    exact hp m.1 m.2 (Raw.box_mem hm)

/-- Multiplication respects the standard total-degree grading of F₂[X,Y]. -/
theorem homogeneous_mul {p q : Poly} {d e : Nat}
    (hp : Homogeneous p d) (hq : Homogeneous q e) : Homogeneous (mul p q) (d+e) := by
  obtain ⟨a,rfl,ha⟩ := homogeneous_raw_representation hp
  obtain ⟨b,rfl,hb⟩ := homogeneous_raw_representation hq
  rw [mul_ofRaw]
  intro i j hij
  exact Raw.mul_monomial_degree ha hb (i,j) (Raw.coeff_true_mem hij)

end TLMC506
