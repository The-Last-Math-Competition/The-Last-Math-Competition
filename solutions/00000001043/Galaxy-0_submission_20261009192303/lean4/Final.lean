import Certificate
import FieldModel
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace TLMC1043

theorem length_three {bs : List F} (h : bs.length = 3) :
    ∃ a b c, bs = [a,b,c] := by
  cases bs with
  | nil => simp at h
  | cons a bs =>
    cases bs with
    | nil => simp at h
    | cons b bs =>
      cases bs with
      | nil => simp at h
      | cons c bs =>
        have ht : bs.length = 0 := by simp only [List.length_cons] at h; omega
        have hn : bs = [] := List.eq_nil_of_length_eq_zero ht
        subst bs
        exact ⟨a,b,c,rfl⟩

theorem length_four {bs : List F} (h : bs.length = 4) :
    ∃ a b c d, bs = [a,b,c,d] := by
  cases bs with
  | nil => simp at h
  | cons a bs =>
    have ht : bs.length = 3 := by simp only [List.length_cons] at h; omega
    obtain ⟨b,c,d,hbs⟩ := length_three ht
    subst bs
    exact ⟨a,b,c,d,rfl⟩

theorem no_three : ¬ Represents 3 witness := by
  intro h
  obtain ⟨bs,a,c,hlen,heq⟩ := complete_normal_form h
  obtain ⟨u,v,w,hbs⟩ := length_three hlen
  subst bs
  have hf : normal [u,v,w] a c = witness := funext heq
  have hc := certificate3 u v w
  rw [← hf, strip_normal] at hc
  exact affine_not_NotAffine a c hc

theorem no_four : ¬ Represents 4 witness := by
  intro h
  obtain ⟨bs,a,c,hlen,heq⟩ := complete_normal_form h
  obtain ⟨u,v,w,z,hbs⟩ := length_four hlen
  subst bs
  have hf : normal [u,v,w,z] a c = witness := funext heq
  have hc := certificate4 u v w z
  rw [← hf, strip_normal] at hc
  exact affine_not_NotAffine a c hc

theorem inversion_represents {k : Nat} {f : F → F} (h : Represents k f) :
    Represents (k+1) (fun x => inv (f x)) := by
  have h' := Represents.step 1 0 (by decide) h
  simpa only [Fin.one_mul, Fin.add_zero] using h'

theorem pad_two {k : Nat} {f : F → F} (h : Represents k f) : Represents (k+2) f := by
  have h' := inversion_represents (inversion_represents h)
  simpa only [inv_involutive] using h'

/-- No expression with at most four standard Carlitz inversions represents f. -/
theorem rank_exceeds_four : ¬ RankAtMost 4 witness := by
  intro ⟨k,hk,h⟩
  have cases_k : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 := by omega
  rcases cases_k with rfl | rfl | rfl | rfl | rfl
  · exact no_four (pad_two (pad_two h))
  · exact no_three (pad_two h)
  · exact no_four (pad_two h)
  · exact no_three h
  · exact no_four h

/-- The universal standard-Carlitz-rank bound already fails on the prime field F_11. -/
theorem standard_carlitz_bound_false :
    ¬ (∀ f : F → F,
      ((∀ x y, f x = f y → x = y) ∧ (∀ y, ∃ x, f x = y)) → RankAtMost 4 f) := by
  intro h
  exact rank_exceeds_four (h witness witness_bijective)

/-- The counterexample is an explicit polynomial and a permutation. -/
theorem polynomial_counterexample :
    ((∀ x y, witnessPolynomial x = witnessPolynomial y → x = y) ∧
     (∀ y, ∃ x, witnessPolynomial x = y)) ∧ ¬ RankAtMost 4 witnessPolynomial := by
  have hp : witnessPolynomial = witness := funext polynomial_represents_witness
  rw [hp]
  exact ⟨witness_bijective, rank_exceeds_four⟩

end TLMC1043
