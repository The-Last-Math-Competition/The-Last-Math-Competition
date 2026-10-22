import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps

/-! Genuine rooted induced radius-two balls. No disconnected-distance fallback
is used. Cycle copies give arbitrarily large equal-order Hanf-equivalent graphs
which are not globally isomorphic. -/
namespace TLMC5045
open SimpleGraph

def ball2 {V : Type*} (G : SimpleGraph V) (v : V) : Set V :=
  {w | w=v ∨ G.Adj v w ∨ ∃ z, G.Adj v z ∧ G.Adj z w}

instance ball2Decidable {V : Type*} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : DecidablePred (ball2 G v) := by
  intro w
  change Decidable (w=v ∨ G.Adj v w ∨ ∃ z, G.Adj v z ∧ G.Adj z w)
  infer_instance

theorem root_mem_ball2 {V : Type*} (G : SimpleGraph V) (v : V) : v∈ball2 G v :=
  Or.inl rfl

theorem ball2_iff_walk {V : Type*} (G : SimpleGraph V) (v w : V) :
    w∈ball2 G v ↔ ∃ p : G.Walk v w, p.length≤2 := by
  constructor
  · rintro (rfl|h|⟨z,hz,hw⟩)
    · exact ⟨.nil,by simp⟩
    · exact ⟨.cons h .nil,by simp⟩
    · exact ⟨.cons hz (.cons hw .nil),by simp⟩
  · rintro ⟨p,hp⟩
    cases p with
    | nil => exact Or.inl rfl
    | cons h p =>
      cases p with
      | nil => exact Or.inr (Or.inl h)
      | cons h' p =>
        cases p with
        | nil => exact Or.inr (Or.inr ⟨_,h,h'⟩)
        | cons h'' p => simp at hp

def RootedBallIso {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W)
    (v : V) (w : W) : Prop :=
  ∃ e : G.induce (ball2 G v) ≃g H.induce (ball2 H w),
    e ⟨v,root_mem_ball2 G v⟩ = ⟨w,root_mem_ball2 H w⟩

theorem rootedBallIso_refl {V : Type*} (G : SimpleGraph V) (v : V) :
    RootedBallIso G G v v := ⟨.refl,rfl⟩

theorem rootedBallIso_symm {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    {v : V} {w : W} (h : RootedBallIso G H v w) : RootedBallIso H G w v := by
  obtain ⟨e,he⟩ := h
  refine ⟨e.symm,?_⟩
  apply e.injective
  simpa using he.symm

theorem rootedBallIso_trans {V W X : Type*} {G : SimpleGraph V}
    {H : SimpleGraph W} {K : SimpleGraph X} {v : V} {w : W} {x : X}
    (h : RootedBallIso G H v w) (h' : RootedBallIso H K w x) :
    RootedBallIso G K v x := by
  obtain ⟨e,he⟩ := h; obtain ⟨f,hf⟩ := h'
  refine ⟨f.comp e,?_⟩
  exact (congrArg f he).trans hf

def copies (I : Type*) {V : Type*} (G : SimpleGraph V) : SimpleGraph (I×V) where
  Adj a b := a.1=b.1 ∧ G.Adj a.2 b.2
  symm := ⟨fun _ _ h => ⟨h.1.symm,h.2.symm⟩⟩
  loopless := ⟨fun a h => G.loopless.irrefl a.2 h.2⟩

instance copiesDecidable (I : Type*) [DecidableEq I] {V : Type*}
    (G : SimpleGraph V) [DecidableRel G.Adj] : DecidableRel (copies I G).Adj := by
  intro a b; unfold copies; infer_instance

theorem copies_ball2 {I V : Type*} (G : SimpleGraph V) (i j : I) (v w : V) :
    (j,w)∈ball2 (copies I G) (i,v) ↔ j=i ∧ w∈ball2 G v := by
  constructor
  · rintro (h|h|⟨⟨k,z⟩,hz,hw⟩)
    · cases h; exact ⟨rfl,Or.inl rfl⟩
    · exact ⟨h.1.symm,Or.inr (Or.inl h.2)⟩
    · exact ⟨hw.1.symm.trans hz.1.symm,Or.inr (Or.inr ⟨z,hz.2,hw.2⟩)⟩
  · rintro ⟨rfl,h⟩
    rcases h with rfl|h|⟨z,hz,hw⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨rfl,h⟩)
    · exact Or.inr (Or.inr ⟨(_,z),⟨rfl,hz⟩,⟨rfl,hw⟩⟩)

theorem copies_rootedBallIso {I V : Type*} (G : SimpleGraph V) (i : I) (v : V) :
    RootedBallIso (copies I G) G (i,v) v := by
  let e : (copies I G).induce (ball2 (copies I G) (i,v)) ≃g
      G.induce (ball2 G v) := {
    toFun := fun x => ⟨x.val.2,((copies_ball2 G i x.val.1 v x.val.2).mp x.property).2⟩
    invFun := fun x => ⟨(i,x.val),(copies_ball2 G i i v x.val).mpr ⟨rfl,x.property⟩⟩
    left_inv := by
      intro x; apply Subtype.ext
      have hx := ((copies_ball2 G i x.val.1 v x.val.2).mp x.property).1
      exact Prod.ext hx.symm rfl
    right_inv := by intro x; rfl
    map_rel_iff' := by
      intro x y
      change G.Adj x.val.2 y.val.2 ↔ x.val.1=y.val.1 ∧ G.Adj x.val.2 y.val.2
      have hx := ((copies_ball2 G i x.val.1 v x.val.2).mp x.property).1
      have hy := ((copies_ball2 G i y.val.1 v y.val.2).mp y.property).1
      simp [hx,hy] }
  exact ⟨e,rfl⟩

theorem ball2_map_iso {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) (v w : V) :
    e w∈ball2 H (e v) ↔ w∈ball2 G v := by
  constructor
  · rintro (h|h|⟨z,hz,hw⟩)
    · exact Or.inl (e.injective h)
    · exact Or.inr (Or.inl (e.map_adj_iff.mp h))
    · obtain ⟨z,rfl⟩ := e.surjective z
      exact Or.inr (Or.inr ⟨z,e.map_adj_iff.mp hz,e.map_adj_iff.mp hw⟩)
  · rintro (rfl|h|⟨z,hz,hw⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl (e.map_adj_iff.mpr h))
    · exact Or.inr (Or.inr ⟨e z,e.map_adj_iff.mpr hz,e.map_adj_iff.mpr hw⟩)

theorem rootedBallIso_of_iso {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) (v : V) : RootedBallIso G H v (e v) := by
  have hb : Set.BijOn e (ball2 G v) (ball2 H (e v)) := by
    refine ⟨?_,e.injective.injOn,?_⟩
    · intro w hw; exact (ball2_map_iso e v w).mpr hw
    · intro w hw
      obtain ⟨z,rfl⟩ := e.surjective w
      exact ⟨z,(ball2_map_iso e v z).mp hw,rfl⟩
  exact ⟨e.induce hb,rfl⟩

def rotation (n : ℕ) [NeZero n] (u : Fin n) : cycleGraph n ≃g cycleGraph n where
  toEquiv := Equiv.addRight u
  map_rel_iff' := by
    intro a b
    simp [SimpleGraph.cycleGraph_adj',add_sub_add_right_eq_sub]

theorem cycle_rootedBallIso_zero (n : ℕ) [NeZero n] (u : Fin n) :
    RootedBallIso (cycleGraph n) (cycleGraph n) 0 u := by
  simpa [rotation] using rootedBallIso_of_iso (rotation n u) 0

def v12 (i : Fin 5) : Fin 12 := ![0,1,2,10,11] i
def v6 (i : Fin 5) : Fin 6 := ![0,1,2,4,5] i

theorem v12_injective : Function.Injective v12 := by
  unfold Function.Injective; decide

theorem v6_injective : Function.Injective v6 := by
  unfold Function.Injective; decide

theorem v12_ball (w : Fin 12) : w∈ball2 (cycleGraph 12) 0 ↔ ∃ i, v12 i=w := by
  change (w=0 ∨ (cycleGraph 12).Adj 0 w ∨
    ∃ z, (cycleGraph 12).Adj 0 z ∧ (cycleGraph 12).Adj z w) ↔ ∃ i, v12 i=w
  fin_cases w <;> decide

theorem v6_ball (w : Fin 6) : w∈ball2 (cycleGraph 6) 0 ↔ ∃ i, v6 i=w := by
  change (w=0 ∨ (cycleGraph 6).Adj 0 w ∨
    ∃ z, (cycleGraph 6).Adj 0 z ∧ (cycleGraph 6).Adj z w) ↔ ∃ i, v6 i=w
  fin_cases w <;> decide

theorem v12_v6_adj : ∀ i j : Fin 5,
    (cycleGraph 12).Adj (v12 i) (v12 j) ↔ (cycleGraph 6).Adj (v6 i) (v6 j) := by
  decide

theorem base_rootedBallIso : RootedBallIso (cycleGraph 12) (cycleGraph 6) 0 0 := by
  let a : Fin 5 ≃ {w // w∈ball2 (cycleGraph 12) 0} :=
    Equiv.ofBijective (fun i => ⟨v12 i,(v12_ball _).mpr ⟨i,rfl⟩⟩) (by
      constructor
      · intro i j h; exact v12_injective (congrArg Subtype.val h)
      · intro w; obtain ⟨i,hi⟩ := (v12_ball w.val).mp w.property
        exact ⟨i,Subtype.ext hi⟩)
  let b : Fin 5 ≃ {w // w∈ball2 (cycleGraph 6) 0} :=
    Equiv.ofBijective (fun i => ⟨v6 i,(v6_ball _).mpr ⟨i,rfl⟩⟩) (by
      constructor
      · intro i j h; exact v6_injective (congrArg Subtype.val h)
      · intro w; obtain ⟨i,hi⟩ := (v6_ball w.val).mp w.property
        exact ⟨i,Subtype.ext hi⟩)
  let e : (cycleGraph 12).induce (ball2 (cycleGraph 12) 0) ≃g
      (cycleGraph 6).induce (ball2 (cycleGraph 6) 0) := {
    toEquiv := a.symm.trans b
    map_rel_iff' := by
      intro x y
      obtain ⟨i,rfl⟩ := a.surjective x
      obtain ⟨j,rfl⟩ := a.surjective y
      simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
      change (cycleGraph 6).Adj (v6 i) (v6 j) ↔ (cycleGraph 12).Adj (v12 i) (v12 j)
      exact (v12_v6_adj i j).symm }
  refine ⟨e,?_⟩
  have ha : a 0 = ⟨0,root_mem_ball2 _ _⟩ := rfl
  have hb : b 0 = ⟨0,root_mem_ball2 _ _⟩ := rfl
  change b (a.symm _) = _
  rw [← ha,a.symm_apply_apply,hb]

theorem all_cycle_balls_iso (u : Fin 12) (v : Fin 6) :
    RootedBallIso (cycleGraph 12) (cycleGraph 6) u v :=
  rootedBallIso_trans (rootedBallIso_symm (cycle_rootedBallIso_zero 12 u))
    (rootedBallIso_trans base_rootedBallIso (cycle_rootedBallIso_zero 6 v))

abbrev V (t : ℕ) := Fin (t+1) × Fin 12
abbrev W (t : ℕ) := (Fin (t+1) × Fin 2) × Fin 6
def G (t : ℕ) : SimpleGraph (V t) := copies (Fin (t+1)) (cycleGraph 12)
def H (t : ℕ) : SimpleGraph (W t) := copies (Fin (t+1) × Fin 2) (cycleGraph 6)
instance gDecidable (t : ℕ) : DecidableRel (G t).Adj := by unfold G; infer_instance
instance hDecidable (t : ℕ) : DecidableRel (H t).Adj := by unfold H; infer_instance

theorem every_ball_iso (t : ℕ) (v : V t) (w : W t) :
    RootedBallIso (G t) (H t) v w :=
  rootedBallIso_trans (copies_rootedBallIso _ v.1 v.2)
    (rootedBallIso_trans (all_cycle_balls_iso v.2 w.2)
      (rootedBallIso_symm (copies_rootedBallIso _ w.1 w.2)))

theorem equal_order (t : ℕ) : Fintype.card (V t)=Fintype.card (W t) := by
  simp [V,W,Fintype.card_prod]; omega

def HanfMatching {X Y : Type*} (A : SimpleGraph X) (B : SimpleGraph Y) : Prop :=
  ∃ f : X ≃ Y, ∀ x, RootedBallIso A B x (f x)

theorem actual_hanf_matching (t : ℕ) : HanfMatching (G t) (H t) := by
  exact ⟨Fintype.equivOfCardEq (equal_order t),fun v => every_ball_iso t v _⟩

noncomputable def typeCount {X Z : Type*} (A : SimpleGraph X) (K : SimpleGraph Z)
    (z : Z) : ℕ := Nat.card {x : X // RootedBallIso A K x z}

theorem matching_counts {X Y Z : Type*} {A : SimpleGraph X} {B : SimpleGraph Y}
    (h : HanfMatching A B) (K : SimpleGraph Z) (z : Z) :
    typeCount A K z = typeCount B K z := by
  obtain ⟨f,hf⟩ := h
  let e : {x : X // RootedBallIso A K x z} ≃ {y : Y // RootedBallIso B K y z} := {
    toFun := fun x => ⟨f x.val, rootedBallIso_trans (rootedBallIso_symm (hf x.val)) x.property⟩
    invFun := fun y => ⟨f.symm y.val, rootedBallIso_trans (hf (f.symm y.val)) (by simpa using y.property)⟩
    left_inv := by intro x; apply Subtype.ext; exact f.symm_apply_apply x.val
    right_inv := by intro y; apply Subtype.ext; exact f.apply_symm_apply y.val }
  exact Nat.card_congr e

def ThresholdHanf {X Y : Type*} (A : SimpleGraph X) (B : SimpleGraph Y) (q : ℕ) : Prop :=
  ∀ (m : ℕ) (K : SimpleGraph (Fin m)) (z : Fin m),
    typeCount A K z = typeCount B K z ∨ q < typeCount A K z ∧ q < typeCount B K z

theorem all_thresholds (t q : ℕ) : ThresholdHanf (G t) (H t) q := by
  intro m K z
  exact Or.inl (matching_counts (actual_hanf_matching t) K z)

theorem walk_same_copy {I X : Type*} {A : SimpleGraph X} {a b : I×X}
    (p : (copies I A).Walk a b) : a.1=b.1 := by
  induction p with
  | nil => rfl
  | cons h p ih => exact h.1.trans ih

def componentHom {I X : Type*} (A : SimpleGraph X) (i : I) : A →g copies I A where
  toFun x := (i,x)
  map_rel' h := ⟨rfl,h⟩

theorem no_global_iso (t : ℕ) : ¬ Nonempty (G t ≃g H t) := by
  rintro ⟨e⟩
  have same : ∀ v : Fin 12, (e (0,v)).1=(e (0,0)).1 := by
    intro v
    obtain ⟨p⟩ := (cycleGraph_connected (n:=11)).preconnected v 0
    exact walk_same_copy ((p.map (componentHom _ (0 : Fin (t+1)))).map e.toHom)
  have hi : Function.Injective (fun v : Fin 12 => (e (0,v)).2) := by
    intro v w hv
    have he : e (0,v)=e (0,w) := Prod.ext ((same v).trans (same w).symm) hv
    exact congrArg Prod.snd (e.injective he)
  have h := Fintype.card_le_of_injective _ hi
  norm_num at h

theorem copies_neighbor_card {I X : Type*} [Fintype I] [DecidableEq I]
    [Fintype X] [DecidableEq X] (A : SimpleGraph X) [DecidableRel A.Adj]
    (i : I) (x : X) : Fintype.card ((copies I A).neighborSet (i,x))=
      Fintype.card (A.neighborSet x) := by
  let e : (copies I A).neighborSet (i,x) ≃ A.neighborSet x := {
    toFun := fun y => ⟨y.val.2,y.property.2⟩
    invFun := fun y => ⟨(i,y.val),⟨rfl,y.property⟩⟩
    left_inv := by intro y; apply Subtype.ext; exact Prod.ext y.property.1 rfl
    right_inv := by intro y; rfl }
  exact Fintype.card_congr e

theorem degrees_two (t : ℕ) :
    (∀ v : V t, (G t).degree v=2) ∧ (∀ w : W t, (H t).degree w=2) := by
  constructor
  · intro v
    rw [← SimpleGraph.card_neighborSet_eq_degree]
    change Fintype.card ((copies _ (cycleGraph 12)).neighborSet v)=2
    rw [copies_neighbor_card, SimpleGraph.card_neighborSet_eq_degree]
    exact cycleGraph_degree_three_le (n:=9) (v:=v.2)
  · intro w
    rw [← SimpleGraph.card_neighborSet_eq_degree]
    change Fintype.card ((copies _ (cycleGraph 6)).neighborSet w)=2
    rw [copies_neighbor_card, SimpleGraph.card_neighborSet_eq_degree]
    exact cycleGraph_degree_three_le (n:=3) (v:=w.2)

theorem arbitrary_size_obstruction (N q : ℕ) :
    ∃ t : ℕ, N ≤ Fintype.card (V t) ∧
      Fintype.card (V t)=Fintype.card (W t) ∧
      (∀ v : V t, (G t).degree v=2) ∧ (∀ w : W t, (H t).degree w=2) ∧
      HanfMatching (G t) (H t) ∧ ThresholdHanf (G t) (H t) q ∧
      ¬ Nonempty (G t ≃g H t) := by
  refine ⟨N,?_,equal_order N,(degrees_two N).1,(degrees_two N).2,
    actual_hanf_matching N,all_thresholds N q,no_global_iso N⟩
  simp [V,Fintype.card_prod]; omega

theorem no_uniform_global_conversion :
    ¬ ∃ N q : ℕ, ∀ t : ℕ, N ≤ Fintype.card (V t) →
      ThresholdHanf (G t) (H t) q → Nonempty (G t ≃g H t) := by
  rintro ⟨N,q,h⟩
  obtain ⟨t,ht,_,_,_,_,hq,hn⟩ := arbitrary_size_obstruction N q
  exact hn (h t ht hq)

end TLMC5045
