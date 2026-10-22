import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Real.Sqrt

set_option maxRecDepth 4000
set_option maxHeartbeats 1600000

namespace Markov8333

def Equation (a b c : ℕ) : Prop := a*a+b*b+c*c=3*a*b*c

structure Triple where
  a : ℕ
  b : ℕ
  c : ℕ
  deriving DecidableEq

def Good (t : Triple) : Prop :=
  0 < t.a ∧ t.a < t.b ∧ t.b < t.c ∧ Equation t.a t.b t.c

def root : Triple := ⟨1,2,5⟩
def child (r : Bool) (t : Triple) : Triple :=
  if r then ⟨t.b,t.c,3*t.b*t.c-t.a⟩ else ⟨t.a,t.c,3*t.a*t.c-t.b⟩

theorem mutate {a b c d : ℕ} (h : Equation a b c) (hd : d+b=3*a*c) :
    Equation a c d := by
  unfold Equation at *
  have h₁ := congrArg (fun x : ℕ => x*b) hd
  have h₂ := congrArg (fun x : ℕ => x*d) hd
  nlinarith

theorem child_good {t : Triple} (h : Good t) (r : Bool) : Good (child r t) := by
  rcases t with ⟨a,b,c⟩
  rcases h with ⟨ha,hab,hbc,he⟩
  change 0<a at ha
  change a<b at hab
  change b<c at hbc
  change Equation a b c at he
  have hac : c ≤ a*c := by nlinarith
  have hbc' : c ≤ b*c := by nlinarith
  cases r
  · have hs : (3*a*c-b)+b=3*a*c := Nat.sub_add_cancel (by nlinarith)
    change 0<a ∧ a<c ∧ c<3*a*c-b ∧ Equation a c (3*a*c-b)
    exact ⟨ha,by omega,by nlinarith,mutate he hs⟩
  · have hs : (3*b*c-a)+a=3*b*c := Nat.sub_add_cancel (by nlinarith)
    change 0<b ∧ b<c ∧ c<3*b*c-a ∧ Equation b c (3*b*c-a)
    have he' : Equation b a c := by unfold Equation at *; nlinarith
    exact ⟨by omega,hbc,by nlinarith,mutate he' hs⟩

theorem child_growth {t : Triple} (h : Good t) (r : Bool) :
    (3*t.a-1)*t.c ≤ (child r t).c := by
  rcases t with ⟨a,b,c⟩
  rcases h with ⟨ha,hab,hbc,_⟩
  change 0<a at ha
  change a<b at hab
  change b<c at hbc
  have hac : c ≤ a*c := by nlinarith
  have hs : 3*a-1+1=3*a := Nat.sub_add_cancel (by omega)
  cases r <;> simp only [child, Bool.false_eq_true, ↓reduceIte]
  · have hd : 3*a*c-b+b=3*a*c := Nat.sub_add_cancel (by nlinarith)
    nlinarith
  · have hbc' : c ≤ b*c := by nlinarith
    have hd : 3*b*c-a+a=3*b*c := Nat.sub_add_cancel (by nlinarith)
    nlinarith

theorem descent {a b c : ℕ} (ha : 0<a) (hab : a≤b) (hbc : b≤c)
    (he : Equation a b c) (hex : ¬(a=1 ∧ b=1)) :
    ∃ d : ℕ, 0<d ∧ d<b ∧ d+c=3*a*b ∧ Equation a b d := by
  have hb : 0<b := by omega
  have hc : 0<c := by omega
  have hc' : c<3*a*b := by
    by_contra hn
    have hmul : 3*a*b*c ≤ c*c := Nat.mul_le_mul_right c (by omega)
    unfold Equation at he
    nlinarith [Nat.mul_pos ha ha, Nat.mul_pos hb hb]
  let d := 3*a*b-c
  have hd : 0<d := Nat.sub_pos_of_lt hc'
  have hsum : d+c=3*a*b := Nat.sub_add_cancel (by omega)
  have hdc : d*c=a*a+b*b := by
    have hm := congrArg (fun x : ℕ => x*c) hsum
    unfold Equation at he
    nlinarith
  have hneg : a*a+2*b*b <3*a*b*b := by
    by_cases h₁ : a=1
    · subst a
      have : 2≤b := by omega
      nlinarith
    · have ha₂ : 2≤a := by omega
      have hs : a*a≤b*b := Nat.mul_self_le_mul_self hab
      have hm : 6*(b*b)≤(3*a)*(b*b) := Nat.mul_le_mul_right (b*b) (by omega)
      nlinarith [Nat.mul_pos hb hb]
  have hdb : d<b := by
    by_contra hn
    have heZ : (d:ℤ)*(c:ℤ)=(a:ℤ)*a+(b:ℤ)*b := by exact_mod_cast hdc
    have hsZ : (d:ℤ)+c=3*(a:ℤ)*b := by exact_mod_cast hsum
    have hnZ : 0≤(d:ℤ)-b := by omega
    have hcZ : 0≤(c:ℤ)-b := by omega
    have hh := mul_nonneg hnZ hcZ
    have hnegZ : (a:ℤ)*a+2*b*b<3*(a:ℤ)*b*b := by exact_mod_cast hneg
    nlinarith
  refine ⟨d,hd,hdb,hsum,?_⟩
  have hm₁ := congrArg (fun x : ℕ => x*c) hsum
  have hm₂ := congrArg (fun x : ℕ => x*d) hsum
  unfold Equation at *
  nlinarith

def run (t : Triple) : List Bool → Triple
  | [] => t
  | r::w => run (child r t) w

def node (w : List Bool) : Triple := run root w

theorem run_append (t : Triple) (u v : List Bool) :
    run t (u++v)=run (run t u) v := by
  induction u generalizing t with
  | nil => rfl
  | cons r u ih => exact ih (child r t)

theorem run_good {t : Triple} (h : Good t) (w : List Bool) : Good (run t w) := by
  induction w generalizing t with
  | nil => exact h
  | cons r w ih => exact ih (child_good h r)

theorem node_good (w : List Bool) : Good (node w) :=
  run_good (by norm_num [Good,root,Equation]) w

theorem sorted_coverage (a b c : ℕ) (ha : 0<a) (hab : a≤b) (hbc : b≤c)
    (he : Equation a b c) :
    (a=1 ∧ b=1 ∧ (c=1 ∨ c=2)) ∨ ∃w, node w=⟨a,b,c⟩ := by
  generalize hn : a+b+c=n
  induction n using Nat.strong_induction_on generalizing a b c with
  | h n ih =>
    by_cases hex : a=1 ∧ b=1
    · left
      rcases hex with ⟨rfl,rfl⟩
      refine ⟨rfl,rfl,?_⟩
      unfold Equation at he
      have : c≤2 := by nlinarith
      omega
    · obtain ⟨d,hd,hdb,hs,hed⟩ := descent ha hab hbc he hex
      have hbc' : b<c := by
        by_contra hn'
        have hcb : c=b := by omega
        subst c
        have hp := Nat.mul_lt_mul_of_pos_right hdb (by omega : 0<b)
        unfold Equation at he
        nlinarith
      by_cases hda : d≤a
      · have hep : Equation d a b := by unfold Equation at *; nlinarith
        have hp := ih (d+a+b) (by omega) d a b hd hda hab hep rfl
        rcases hp with hp | ⟨w,hw⟩
        · rcases hp with ⟨h₁,h₂,h₃|h₃⟩
          · subst d; subst a; subst b
            have : c=2 := by omega
            exact False.elim (hex ⟨rfl,rfl⟩)
          · subst d; subst a; subst b
            right
            refine ⟨[],?_⟩
            have : c=5 := by omega
            subst c
            rfl
        · right
          refine ⟨w++[true],?_⟩
          simp only [node,run_append] at hw ⊢
          rw [hw]
          simp only [run,child,↓reduceIte]
          congr 1
          omega
      · have had : a≤d := by omega
        have hep : Equation a d b := by unfold Equation at *; nlinarith
        have hp := ih (a+d+b) (by omega) a d b ha had (by omega) hep rfl
        rcases hp with hp | ⟨w,hw⟩
        · rcases hp with ⟨h₁,h₂,h₃⟩
          omega
        · right
          refine ⟨w++[false],?_⟩
          simp only [node,run_append] at hw ⊢
          rw [hw]
          simp only [run,child,Bool.false_eq_true,↓reduceIte]
          congr 1
          omega

theorem run_coordinate (t : Triple) (w : List Bool) (m : ℕ)
    (hm : m=(run t w).a ∨ m=(run t w).b ∨ m=(run t w).c) :
    (m=t.a ∨ m=t.b ∨ m=t.c) ∨ ∃u, (run t u).c=m := by
  induction w generalizing t with
  | nil => exact Or.inl hm
  | cons r w ih =>
    obtain hh | ⟨u,hu⟩ := ih (child r t) hm
    · cases r <;> simp only [child,Bool.false_eq_true,↓reduceIte] at hh
      · rcases hh with hh|hh|hh
        · exact Or.inl (Or.inl hh)
        · exact Or.inl (Or.inr (Or.inr hh))
        · exact Or.inr ⟨[false],hh.symm⟩
      · rcases hh with hh|hh|hh
        · exact Or.inl (Or.inr (Or.inl hh))
        · exact Or.inl (Or.inr (Or.inr hh))
        · exact Or.inr ⟨[true],hh.symm⟩
    · exact Or.inr ⟨r::u,hu⟩

def IsMarkovNumber (m : ℕ) : Prop :=
  0<m ∧ ∃a b : ℕ, 0<a ∧ 0<b ∧ Equation a b m

theorem sorted_birth {a b c m : ℕ} (ha : 0<a) (hab : a≤b) (hbc : b≤c)
    (he : Equation a b c) (hm : m=a ∨ m=b ∨ m=c) :
    m=1 ∨ m=2 ∨ ∃w, (node w).c=m := by
  obtain ⟨rfl,rfl,hc⟩ | ⟨w,hw⟩ := sorted_coverage a b c ha hab hbc he
  · rcases hm with rfl|rfl|rfl
    · exact Or.inl rfl
    · exact Or.inl rfl
    · rcases hc with rfl|rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
  · have hh : m=(node w).a ∨ m=(node w).b ∨ m=(node w).c := by simpa [hw] using hm
    obtain hh | hh := run_coordinate root w m hh
    · rcases hh with hh|hh|hh
      · exact Or.inl hh
      · exact Or.inr (Or.inl hh)
      · exact Or.inr (Or.inr ⟨[],hh.symm⟩)
    · exact Or.inr (Or.inr hh)

theorem number_birth {m : ℕ} (hm : IsMarkovNumber m) :
    m=1 ∨ m=2 ∨ ∃w, (node w).c=m := by
  rcases hm with ⟨hm,a,b,ha,hb,he⟩
  have perm₁ : Equation a m b := by unfold Equation at *; nlinarith
  have perm₂ : Equation b a m := by unfold Equation at *; nlinarith
  have perm₃ : Equation b m a := by unfold Equation at *; nlinarith
  have perm₄ : Equation m a b := by unfold Equation at *; nlinarith
  have perm₅ : Equation m b a := by unfold Equation at *; nlinarith
  by_cases hab : a≤b
  · by_cases hbm : b≤m
    · exact sorted_birth ha hab hbm he (Or.inr (Or.inr rfl))
    · by_cases ham : a≤m
      · exact sorted_birth ha ham (by omega) perm₁ (Or.inr (Or.inl rfl))
      · exact sorted_birth hm (by omega) hab perm₄ (Or.inl rfl)
  · by_cases ham : a≤m
    · exact sorted_birth hb (by omega) ham perm₂ (Or.inr (Or.inr rfl))
    · by_cases hbm : b≤m
      · exact sorted_birth hb hbm (by omega) perm₃ (Or.inr (Or.inl rfl))
      · exact sorted_birth hm (by omega) (by omega) perm₅ (Or.inl rfl)

theorem run_growth {t : Triple} (h : Good t) (k : ℕ)
    (hk : k≤3*t.a-1) (w : List Bool) : k^w.length*t.c≤(run t w).c := by
  induction w generalizing t with
  | nil => simp [run]
  | cons r w ih =>
    have hg := child_good h r
    have hmin : t.a≤(child r t).a := by
      cases r <;> simp [child]
      exact le_of_lt h.2.1
    have hstep : k*t.c≤(child r t).c :=
      (Nat.mul_le_mul_right t.c hk).trans (child_growth h r)
    have hi := ih hg (by omega : k≤3*(child r t).a-1)
    simp only [List.length_cons,run,pow_succ]
    nlinarith [Nat.mul_le_mul_left (k^w.length) hstep]

theorem node_length_bound {w : List Bool} {n : ℕ} (h : (node w).c≤64^n) :
    w.length≤6*n := by
  have hg := run_growth (t:=root) (by norm_num [Good,root,Equation]) 2 (by norm_num [root]) w
  have hp : 2^w.length≤64^n := by
    change 2^w.length*5≤(node w).c at hg
    nlinarith
  have hex : (64:ℕ)^n=2^(6*n) := by rw [pow_mul]; norm_num
  rw [hex] at hp
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1<2)).mp hp

theorem run_min {t : Triple} (h : Good t) (w : List Bool) :
    t.a + w.count true ≤ (run t w).a := by
  induction w generalizing t with
  | nil => simp [run]
  | cons r w ih =>
    have hi := ih (child_good h r)
    cases r <;> simp only [List.count_cons,beq_self_eq_true,↓reduceIte,
      Bool.false_eq_true,beq_false,run,child] at hi ⊢
    · simpa using hi
    · have ht := h.2.1
      omega

theorem suffix_length_bound (u v : List Bool) (n : ℕ)
    (hu : 2≤u.count true) (h : (node (u++v)).c≤64^n) : v.length≤2*n := by
  have hmin := run_min (t:=root) (by norm_num [Good,root,Equation]) u
  change 1+u.count true≤(node u).a at hmin
  have hg := run_growth (node_good u) 8 (by omega) v
  have hc := (node_good u).2.2.1
  have hp : 8^v.length≤64^n := by
    simp only [node,run_append] at h
    change (run (node u) v).c≤64^n at h
    have hcp : 1≤(node u).c := by have hh := node_good u; omega
    nlinarith
  have hex : (64:ℕ)^n=8^(2*n) := by rw [pow_mul]; norm_num
  rw [hex] at hp
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1<8)).mp hp

theorem first_true (w : List Bool) :
    w=List.replicate w.length false ∨
    ∃i v, w=List.replicate i false ++ true::v := by
  induction w with
  | nil => exact Or.inl rfl
  | cons r w ih =>
    cases r
    · rcases ih with ih|⟨i,v,ih⟩
      · left; simpa only [List.length_cons,List.replicate_succ] using congrArg (false::·) ih
      · right; exact ⟨i+1,v,by simpa only [List.replicate_succ,List.cons_append] using congrArg (false::·) ih⟩
    · exact Or.inr ⟨0,w,rfl⟩

def words : ℕ → Finset (List Bool)
  | 0 => {[]}
  | k+1 => insert [] (((words k).image (false::·)) ∪ ((words k).image (true::·)))

theorem mem_words {w : List Bool} {k : ℕ} (h : w.length≤k) : w∈words k := by
  induction k generalizing w with
  | zero => have : w=[] := List.length_eq_zero_iff.mp (by omega); simp [this,words]
  | succ k ih =>
    cases w with
    | nil => simp [words]
    | cons r w =>
      have hm := ih (w:=w) (by simpa using Nat.le_of_succ_le_succ h)
      cases r <;> simp [words,hm]

theorem words_card (k : ℕ) : (words k).card+1≤2^(k+1) := by
  induction k with
  | zero => norm_num [words]
  | succ k ih =>
    have h₁ := Finset.card_insert_le [] (((words k).image (false::·)) ∪ ((words k).image (true::·)))
    have h₂ := Finset.card_union_le ((words k).image (false::·)) ((words k).image (true::·))
    have h₃ := Finset.card_image_le (s:=words k) (f:=fun w : List Bool => false::w)
    have h₄ := Finset.card_image_le (s:=words k) (f:=fun w : List Bool => true::w)
    change (insert [] (((words k).image (false::·)) ∪ ((words k).image (true::·)))).card+1≤_
    rw [pow_succ]
    nlinarith

def candidates (n : ℕ) : Finset (List Bool) :=
  ((Finset.range (6*n+1)).image (fun i => List.replicate i false)) ∪
  (((Finset.range (6*n+1)) ×ˢ (Finset.range (6*n+1))).image
    (fun p => List.replicate p.1 false ++ true::List.replicate p.2 false)) ∪
  ((((Finset.range (6*n+1)) ×ˢ (Finset.range (6*n+1))) ×ˢ words (2*n)).image
    (fun p => (List.replicate p.1.1 false ++ true::List.replicate p.1.2 false ++ [true]) ++ p.2))

theorem qualifying_mem {w : List Bool} {n : ℕ} (h : (node w).c≤64^n) : w∈candidates n := by
  have hlen := node_length_bound h
  obtain hz | ⟨i,v,hw⟩ := first_true w
  · apply Finset.mem_union_left
    apply Finset.mem_union_left
    exact Finset.mem_image.mpr ⟨w.length,by simpa [Nat.lt_add_one_iff] using hlen,hz.symm⟩
  · obtain hv | ⟨j,z,hv⟩ := first_true v
    · have hi : i≤6*n := by rw [hw] at hlen; simp only [List.length_append,List.length_replicate,List.length_cons] at hlen; omega
      have hj : v.length≤6*n := by rw [hw] at hlen; simp only [List.length_append,List.length_replicate,List.length_cons] at hlen; omega
      apply Finset.mem_union_left
      apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨(i,v.length),by simp [hi,hj,Nat.lt_add_one_iff],?_⟩
      simp only [Prod.fst,Prod.snd]
      rw [←hv]
      exact hw.symm
    · have hword : w=(List.replicate i false ++ true::List.replicate j false ++ [true]) ++ z := by
        rw [hw,hv]; simp [List.append_assoc]
      have hi : i≤6*n := by rw [hword] at hlen; simp at hlen; omega
      have hj : j≤6*n := by rw [hword] at hlen; simp at hlen; omega
      have hz : z.length≤2*n := by
        apply suffix_length_bound (List.replicate i false ++ true::List.replicate j false ++ [true]) z n
        · simp; omega
        · simpa only [hword,List.append_assoc,List.cons_append] using h
      apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      exact ⟨((i,j),z),by simp [hi,hj,Nat.lt_add_one_iff,mem_words hz],hword.symm⟩

theorem candidates_card (n : ℕ) :
    (candidates n).card ≤ 3*(6*n+1)^2*2^(2*n+1) := by
  let s := (Finset.range (6*n+1)).image (fun i => List.replicate i false)
  let t := (((Finset.range (6*n+1)) ×ˢ (Finset.range (6*n+1))).image
    (fun p => List.replicate p.1 false ++ true::List.replicate p.2 false))
  let u := ((((Finset.range (6*n+1)) ×ˢ (Finset.range (6*n+1))) ×ˢ words (2*n)).image
    (fun p => (List.replicate p.1.1 false ++ true::List.replicate p.1.2 false ++ [true]) ++ p.2))
  have h₁ : s.card≤6*n+1 := by exact (Finset.card_image_le).trans_eq (Finset.card_range _)
  have h₂ : t.card≤(6*n+1)^2 := by
    simpa [t,Finset.card_product,pow_two] using (Finset.card_image_le (s:=((Finset.range (6*n+1)) ×ˢ (Finset.range (6*n+1)))) (f:=fun p => List.replicate p.1 false ++ true::List.replicate p.2 false))
  have h₃ : u.card≤(6*n+1)^2*(words (2*n)).card := by
    simpa [u,Finset.card_product,pow_two] using (Finset.card_image_le (s:=(((Finset.range (6*n+1)) ×ˢ (Finset.range (6*n+1))) ×ˢ words (2*n))) (f:=fun p => (List.replicate p.1.1 false ++ true::List.replicate p.1.2 false ++ [true]) ++ p.2))
  have h₄ := Finset.card_union_le (s∪t) u
  have h₅ := Finset.card_union_le s t
  have hw := words_card (2*n)
  have hp : 1≤2^(2*n+1) := Nat.one_le_pow _ _ (by omega)
  have hm := Nat.mul_le_mul_left ((6*n+1)^2) hw
  change (s∪t∪u).card≤_
  nlinarith [Nat.le_mul_self (6*n+1)]

noncomputable def numbersUpTo (X : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (X+1)).filter IsMarkovNumber

noncomputable def count (X : ℕ) : ℕ := (numbersUpTo X).card

theorem count_bound (n : ℕ) :
    count (64^n) ≤ 2+3*(6*n+1)^2*2^(2*n+1) := by
  classical
  have hsub : numbersUpTo (64^n) ⊆ ({1,2} : Finset ℕ) ∪
      ((candidates n).image (fun w => (node w).c)) := by
    intro m hm
    have hm' : m≤64^n ∧ IsMarkovNumber m := by
      simpa [numbersUpTo,Nat.lt_add_one_iff] using hm
    obtain h₁ | h₂ | ⟨w,hw⟩ := number_birth hm'.2
    · simp [h₁]
    · simp [h₂]
    · apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨w,qualifying_mem (by simpa [hw] using hm'.1),hw⟩
  have h₁ := Finset.card_le_card hsub
  have h₂ := Finset.card_union_le ({1,2} : Finset ℕ) ((candidates n).image (fun w => (node w).c))
  have h₃ := Finset.card_image_le (s:=candidates n) (f:=fun w => (node w).c)
  have h₄ := candidates_card n
  have hc₂ : ({1,2}:Finset ℕ).card=2 := by decide
  rw [hc₂] at h₂
  change (numbersUpTo (64^n)).card≤_
  omega

open Filter Topology

theorem count_subsequence_zero :
    Tendsto (fun n : ℕ => (count (64^n) : ℝ)/(8:ℝ)^n) atTop (𝓝 0) := by
  have h₀ := tendsto_pow_const_div_const_pow_of_one_lt 0 (by norm_num : (1:ℝ)<2)
  have h₁ := tendsto_pow_const_div_const_pow_of_one_lt 1 (by norm_num : (1:ℝ)<2)
  have h₂ := tendsto_pow_const_div_const_pow_of_one_lt 2 (by norm_num : (1:ℝ)<2)
  have hupper : Tendsto (fun n : ℕ =>
      2/(8:ℝ)^n + 216*((n:ℝ)^2/2^n) + 72*((n:ℝ)/2^n) + 6*(1/(2:ℝ)^n)) atTop (𝓝 0) := by
    have hzero := tendsto_pow_const_div_const_pow_of_one_lt 0 (by norm_num : (1:ℝ)<8)
    convert (((hzero.const_mul 2).add (h₂.const_mul 216)).add (h₁.const_mul 72)).add (h₀.const_mul 6) using 1 <;> simp [div_eq_mul_inv]
  apply squeeze_zero (fun n => div_nonneg (Nat.cast_nonneg _) (by positivity)) _ hupper
  intro n
  have hb : (count (64^n):ℝ) ≤ 2+3*(6*(n:ℝ)+1)^2*2^(2*n+1) := by exact_mod_cast count_bound n
  have hd : (0:ℝ)<8^n := by positivity
  have hq := (div_le_div_iff_of_pos_right hd).mpr hb
  refine hq.trans_eq ?_
  have hp : (8:ℝ)^n=2^n*2^n*2^n := by rw [←mul_pow,←mul_pow]; norm_num
  have hp₂ : (2:ℝ)^(2*n+1)=2^n*2^n*2 := by rw [show 2*n+1=n+n+1 by omega,pow_succ,pow_add]
  rw [hp,hp₂]
  field_simp
  ring

theorem arbitrarily_small_ratio (c : ℝ) (hc : 0<c) (N : ℕ) :
    ∃n : ℕ, N≤n ∧ (count (64^n):ℝ)<c*(8:ℝ)^n := by
  have hev : ∀ᶠn : ℕ in atTop, (count (64^n):ℝ)/(8:ℝ)^n<c :=
    (tendsto_order.mp count_subsequence_zero).2 c hc
  obtain ⟨K,hK⟩ := eventually_atTop.mp hev
  refine ⟨max N K,le_max_left _ _,?_⟩
  have hh := hK (max N K) (le_max_right _ _)
  exact (div_lt_iff₀ (by positivity : (0:ℝ)<8^(max N K))).mp hh

def SquareRootGrowth : Prop := ∃c : ℝ, 0<c ∧
  Tendsto (fun X : ℕ => (count X : ℝ)/Real.sqrt (X:ℝ)) atTop (𝓝 c)

theorem sqrt_power (n : ℕ) : Real.sqrt ((64^n:ℕ):ℝ)=(8:ℝ)^n := by
  push_cast
  have hp : (64:ℝ)^n=((8:ℝ)^n)^2 := by rw [←pow_mul, mul_comm n 2,pow_mul]; norm_num
  rw [hp,Real.sqrt_sq (by positivity)]

theorem conjecture_8333_false : ¬SquareRootGrowth := by
  rintro ⟨c,hc,hh⟩
  have hp := hh.comp (Nat.tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1<(64:ℕ)))
  have hp' : Tendsto (fun n : ℕ => (count (64^n):ℝ)/(8:ℝ)^n) atTop (𝓝 c) := by
    simpa only [Function.comp_def,sqrt_power] using hp
  have he := tendsto_nhds_unique hp' count_subsequence_zero
  linarith

#print axioms number_birth
#print axioms count_bound
#print axioms count_subsequence_zero
#print axioms arbitrarily_small_ratio
#print axioms conjecture_8333_false

end Markov8333
