import Words
import A1Family

namespace FixedAlphabetA1
open A1Crystal

def row (a b : ℕ) : List Bool := List.replicate a false ++ List.replicate b true

theorem true_stats (b : ℕ) :
    monoidCrystal.eps (List.replicate b true)=b ∧
    monoidCrystal.phi (List.replicate b true)=0 ∧
    monoidCrystal.wt (List.replicate b true)= -(b : ℤ) := by
  induction b with
  | zero => exact ⟨monoid_nil.1,monoid_nil.2.1,monoid_nil.2.2.2.2⟩
  | succ b ih =>
    simp [List.replicate_succ,monoid_cons_eps,monoid_cons_phi,monoid_cons_wt,
      letter,ih.1,ih.2.1,ih.2.2] <;> omega

theorem row_stats (a b : ℕ) :
    monoidCrystal.eps (row a b)=b ∧ monoidCrystal.phi (row a b)=a ∧
    monoidCrystal.wt (row a b)=(a : ℤ)-(b : ℤ) := by
  induction a with
  | zero => simpa [row] using true_stats b
  | succ a ih =>
    simp only [row,List.replicate_succ,List.cons_append,monoid_cons_eps,
      monoid_cons_phi,monoid_cons_wt,letter]
    change monoidCrystal.eps (row a b) + (0 - monoidCrystal.phi (row a b)) = b ∧
      1 + (monoidCrystal.phi (row a b)-0) = a+1 ∧
      (1 : ℤ) + monoidCrystal.wt (row a b) = ((a+1 : ℕ) : ℤ)-(b : ℤ)
    rw [ih.1,ih.2.1,ih.2.2]
    omega

theorem row_f (a b : ℕ) : monoidCrystal.f (row (a+1) b) = some (row a (b+1)) := by
  induction a with
  | zero =>
    simp only [row,List.replicate_succ,List.replicate_zero,List.nil_append,List.cons_append]
    rw [monoid_cons_f]
    simp only [(true_stats b).2.1,letter,Nat.le_refl,if_pos,Option.map_some]
    rfl
  | succ a ih =>
    have hphi := (row_stats (a+1) b).2.1
    change monoidCrystal.f (false :: row (a+1) b) = some (false :: row a (b+1))
    rw [monoid_cons_f,hphi]
    have hn : ¬ a+1 ≤ 0 := by omega
    simp [letter,hn,ih]

theorem row_e (a b : ℕ) : monoidCrystal.e (row a (b+1)) = some (row (a+1) b) :=
  (monoidCrystal.inverse _ _).mp (row_f a b)

def family (k : ℕ) : A1Crystal (Fin (k+1)) where
  wt := SupplementScout.wt k
  eps := SupplementScout.epsilon
  phi := SupplementScout.phi k
  e := SupplementScout.upper k
  f := SupplementScout.lower k
  balance := SupplementScout.balance k
  inverse := SupplementScout.partial_inverse k
  e_none := SupplementScout.upper_none_iff k
  f_none := SupplementScout.lower_none_iff k
  f_eps := SupplementScout.lower_epsilon k
  f_phi := SupplementScout.lower_phi k
  f_wt := SupplementScout.lower_weight k

def embedding (k : ℕ) (i : Fin (k+1)) : List Bool := row (k-i.val) i.val

theorem embedding_injective (k : ℕ) : Function.Injective (embedding k) :=
  SupplementScout.word_injective k

theorem embedding_length (k : ℕ) (i : Fin (k+1)) : (embedding k i).length=k :=
  SupplementScout.word_length k i

theorem embedding_stats (k : ℕ) (i : Fin (k+1)) :
    monoidCrystal.eps (embedding k i)=(family k).eps i ∧
    monoidCrystal.phi (embedding k i)=(family k).phi i ∧
    monoidCrystal.wt (embedding k i)=(family k).wt i := by
  have h := row_stats (k-i.val) i.val
  dsimp only [embedding,family,SupplementScout.epsilon,SupplementScout.phi,SupplementScout.wt]
  refine ⟨h.1,h.2.1,?_⟩
  rw [h.2.2]
  omega

theorem embedding_f (k : ℕ) (i : Fin (k+1)) :
    monoidCrystal.f (embedding k i)=((family k).f i).map (embedding k) := by
  change monoidCrystal.f (embedding k i)=(SupplementScout.lower k i).map (embedding k)
  unfold SupplementScout.lower
  by_cases h : i.val<k
  · rw [dif_pos h]
    have ha : k-i.val=(k-i.val-1)+1 := by omega
    have hb : k-(i.val+1)=k-i.val-1 := by omega
    change monoidCrystal.f (row (k-i.val) i.val)=some (row (k-(i.val+1)) (i.val+1))
    rw [ha,row_f,hb]
  · rw [dif_neg h]
    have hi : i.val=k := by omega
    have he : (family k).phi i=0 := by dsimp [family,SupplementScout.phi]; omega
    have hn := (monoidCrystal.f_none (embedding k i)).mpr ((embedding_stats k i).2.1.trans he)
    exact hn

theorem embedding_e (k : ℕ) (i : Fin (k+1)) :
    monoidCrystal.e (embedding k i)=((family k).e i).map (embedding k) := by
  change monoidCrystal.e (embedding k i)=(SupplementScout.upper k i).map (embedding k)
  unfold SupplementScout.upper
  by_cases h : 0<i.val
  · rw [dif_pos h]
    have hb : i.val=(i.val-1)+1 := by omega
    have ha : k-(i.val-1)=(k-i.val)+1 := by omega
    change monoidCrystal.e (row (k-i.val) i.val)=some (row (k-(i.val-1)) (i.val-1))
    rw [ha]
    simpa only [←hb] using row_e (k-i.val) (i.val-1)
  · rw [dif_neg h]
    have he : (family k).eps i=0 := by dsimp [family,SupplementScout.epsilon]; omega
    have hn := (monoidCrystal.e_none (embedding k i)).mpr ((embedding_stats k i).1.trans he)
    exact hn

end FixedAlphabetA1
