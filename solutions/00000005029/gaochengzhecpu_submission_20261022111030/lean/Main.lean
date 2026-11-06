import Mathlib.Probability.Distributions.Uniform
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open scoped BigOperators Classical ENNReal NNReal
namespace Conjecture5029
noncomputable section

section FiniteProbability
variable {Ω : Type*} [Fintype Ω]

def average (f : Ω → ℝ) : ℝ := (∑ ω, f ω) / Fintype.card Ω
def mark (P : Prop) : ℝ := if P then 1 else 0
def probability (P : Ω → Prop) : ℝ := average (fun ω => mark (P ω))

lemma mark_nonneg (P : Prop) : 0 ≤ mark P := by unfold mark; split_ifs <;> norm_num

lemma mark_mono {P Q : Prop} (h : P → Q) : mark P ≤ mark Q := by
  by_cases hp : P <;> by_cases hq : Q <;> simp_all [mark]

lemma mark_and (P Q : Prop) : mark (P ∧ Q) = mark P * mark Q := by
  by_cases hp : P <;> by_cases hq : Q <;> simp [mark,hp,hq]

lemma sum_mark_eq {α : Type*} [Fintype α] (a : α) : (∑ b : α, mark (a = b)) = 1 := by
  classical
  rw [Finset.sum_eq_single a]
  · simp [mark]
  · intro b hb hne
    simp [mark,Ne.symm hne]
  · intro h
    exact False.elim (h (Finset.mem_univ a))

lemma average_mono {f g : Ω → ℝ} (h : ∀ ω, f ω ≤ g ω) : average f ≤ average g := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact Finset.sum_le_sum (fun ω _ => h ω)

lemma probability_count (P : Ω → Prop) :
    probability P = ((Finset.univ.filter P).card : ℝ) / Fintype.card Ω := by
  classical
  unfold probability average mark
  congr 1
  rw [← Finset.sum_filter]
  simp

lemma probability_PMF [Nonempty Ω] (P : Ω → Prop) :
    ((PMF.uniformOfFintype Ω).toOuterMeasure {ω | P ω}).toReal = probability P := by
  classical
  rw [PMF.toOuterMeasure_uniformOfFintype_apply,ENNReal.toReal_div,
    ENNReal.toReal_natCast,ENNReal.toReal_natCast,probability_count]
  congr 1
  exact_mod_cast Fintype.card_subtype P

lemma probability_mono {P Q : Ω → Prop} (h : ∀ ω, P ω → Q ω) :
    probability P ≤ probability Q := by
  classical
  apply average_mono
  intro ω
  exact mark_mono (h ω)

lemma probability_nonneg (P : Ω → Prop) : 0 ≤ probability P := by
  classical
  unfold probability average
  exact div_nonneg (Finset.sum_nonneg (fun ω _ => mark_nonneg _)) (Nat.cast_nonneg _)

lemma probability_true [Nonempty Ω] : probability (fun _ : Ω => True) = 1 := by
  classical
  simp [probability,average,mark,Fintype.card_ne_zero]

lemma probability_le_one [Nonempty Ω] (P : Ω → Prop) : probability P ≤ 1 := by
  rw [← probability_true (Ω := Ω)]
  exact probability_mono (fun _ _ => trivial)

lemma probability_compl [Nonempty Ω] (P : Ω → Prop) : probability (fun ω => ¬ P ω) = 1-probability P := by
  classical
  have hi : ∀ ω, mark (¬ P ω) = 1-mark (P ω) := by
    intro ω; by_cases h : P ω <;> simp [mark,h]
  simp only [probability,average]
  simp_rw [hi]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
  rw [sub_div,div_self (by exact_mod_cast Fintype.card_ne_zero (α := Ω))]

end FiniteProbability

section Cylinders
variable {E : Type*} [Fintype E] [DecidableEq E]
variable (q : ℕ) [NeZero q]

/-- Full independent uniform coordinate law, before mapping to actual edges. -/
abbrev Assignment := E → Fin q

lemma cylinder_count (S : Finset E) :
    (Finset.univ.filter (fun σ : Assignment (E := E) q => ∀ e ∈ S, σ e = 0)).card =
      q^(Fintype.card E - S.card) := by
  classical
  have he : Finset.univ.filter (fun σ : Assignment (E := E) q => ∀ e ∈ S, σ e = 0) =
      Fintype.piFinset (fun e => if e ∈ S then {0} else Finset.univ) := by
    ext σ
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Fintype.mem_piFinset]
    constructor
    · intro h e
      by_cases he : e ∈ S <;> simp [he,h e]
    · intro h e he
      simpa [he] using h e
  rw [he,Fintype.card_piFinset]
  have hr : (fun e : E => (if e ∈ S then ({0} : Finset (Fin q)) else Finset.univ).card) =
      (fun e => if e ∈ S then 1 else q) := by
    funext e
    split_ifs <;> simp
  rw [hr]
  rw [Finset.prod_ite]
  simp only [Finset.prod_const_one,one_mul,Finset.prod_const]
  congr 1
  have hf : Finset.univ.filter (fun e : E => e ∉ S) = Finset.univ \ S := by ext e; simp
  rw [hf,Finset.card_sdiff (Finset.subset_univ _),Finset.card_univ]

lemma cylinder_probability (S : Finset E) :
    probability (fun σ : Assignment (E := E) q => ∀ e ∈ S, σ e = 0) =
      (1 / (q : ℝ))^S.card := by
  rw [probability_count,Finset.filter_congr_decidable,cylinder_count,Fintype.card_fun,Fintype.card_fin]
  have hn : (q : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne q
  have hs : S.card ≤ Fintype.card E := Finset.card_le_univ _
  rw [Nat.cast_pow,Nat.cast_pow]
  have he : Fintype.card E = S.card + (Fintype.card E-S.card) := by omega
  rw [he,pow_add]
  field_simp
  ring

def allowed (b : E → Bool) (e : E) : Finset (Fin q) :=
  if b e = true then {0} else Finset.univ.erase 0

omit [Fintype E] [DecidableEq E] in
lemma allowed_card (b : E → Bool) (e : E) :
    (allowed q b e).card = if b e = true then 1 else q-1 := by
  by_cases h : b e = true <;> simp [allowed,h]

lemma pattern_count (S : Finset E) (b : E → Bool) :
    (Finset.univ.filter (fun σ : Assignment (E := E) q =>
      ∀ e ∈ S, (σ e = 0 ↔ b e = true))).card =
      (∏ e ∈ S, if b e = true then 1 else q-1) * q^(Fintype.card E-S.card) := by
  have he : Finset.univ.filter (fun σ : Assignment (E := E) q =>
      ∀ e ∈ S, (σ e = 0 ↔ b e = true)) =
      Fintype.piFinset (fun e => if e ∈ S then allowed q b e else Finset.univ) := by
    ext σ
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Fintype.mem_piFinset]
    constructor
    · intro h e
      by_cases hs : e ∈ S
      · have hh := h e hs
        by_cases hb : b e = true <;> simp_all [allowed]
      · simp [hs]
    · intro h e hs
      have hh := h e
      by_cases hb : b e = true <;> simp_all [allowed]
  rw [he,Fintype.card_piFinset]
  have hr : (fun e : E => (if e ∈ S then allowed q b e else Finset.univ).card) =
      (fun e => if e ∈ S then (if b e = true then 1 else q-1) else q) := by
    funext e
    by_cases h : e ∈ S <;> simp [h,allowed_card]
  rw [hr,Finset.prod_ite]
  have hf : Finset.univ.filter (fun e : E => e ∈ S) = S := by ext e; simp
  have hc : Finset.univ.filter (fun e : E => e ∉ S) = Finset.univ \ S := by ext e; simp
  rw [hf,hc,Finset.prod_const,Finset.card_sdiff (Finset.subset_univ _),Finset.card_univ]

/-- Every finite 0/1 pattern has its Bernoulli product probability, including
both prescribed zero coordinates and prescribed nonzero coordinates. -/
lemma pattern_probability (S : Finset E) (b : E → Bool) :
    probability (fun σ : Assignment (E := E) q => ∀ e ∈ S, (σ e = 0 ↔ b e = true)) =
      ∏ e ∈ S, if b e = true then 1/(q : ℝ) else 1-1/(q : ℝ) := by
  rw [probability_count,Finset.filter_congr_decidable,pattern_count,
    Fintype.card_fun,Fintype.card_fin,Nat.cast_mul,Nat.cast_prod,Nat.cast_pow,Nat.cast_pow]
  have hn : (q : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne q
  have hq : 1 ≤ q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hs : S.card ≤ Fintype.card E := Finset.card_le_univ _
  have he : Fintype.card E = S.card+(Fintype.card E-S.card) := by omega
  rw [he,pow_add]
  calc
    _ = (∏ e ∈ S, ((if b e = true then 1 else q-1 : ℕ) : ℝ))/(q : ℝ)^S.card := by
      field_simp
      ring
    _ = ∏ e ∈ S, ((if b e = true then 1 else q-1 : ℕ) : ℝ)/(q : ℝ) := by
      rw [Finset.prod_div_distrib,Finset.prod_const]
    _ = _ := by
      apply Finset.prod_congr rfl
      intro e he
      by_cases hb : b e = true
      · simp [hb]
      · simp only [hb,↓reduceIte,Nat.cast_sub hq,Nat.cast_one]
        field_simp

end Cylinders

section Bonferroni
variable {Ω I : Type*} [Fintype Ω] [Fintype I]

lemma average_add (f g : Ω → ℝ) :
    average (fun ω => f ω + g ω) = average f + average g := by
  unfold average
  rw [Finset.sum_add_distrib,add_div]

lemma average_sum (f : I → Ω → ℝ) :
    average (fun ω => ∑ i, f i ω) = ∑ i, average (f i) := by
  unfold average
  rw [Finset.sum_comm,Finset.sum_div]

/-- A deliberately weakened second Bonferroni inequality, using ordered pairs.
It is proved for the actual events, with no surrogate count assumption. -/
lemma probability_union_lower (P : I → Ω → Prop) :
    (∑ i, probability (P i)) ≤ probability (fun ω => ∃ i, P i ω) +
      ∑ i, ∑ j, probability (fun ω => i ≠ j ∧ P i ω ∧ P j ω) := by
  classical
  have hp : ∀ ω, (∑ i, mark (P i ω)) ≤
      mark (∃ i, P i ω) + ∑ i, ∑ j, mark (i ≠ j ∧ P i ω ∧ P j ω) := by
    intro ω
    by_cases he : ∃ i, P i ω
    · rw [show mark (∃ i, P i ω) = 1 by simp [mark,he]]
      obtain ⟨a,ha⟩ := he
      have hi : ∀ i, mark (P i ω) ≤ (if i = a then 1 else 0) +
          ∑ j, mark (i ≠ j ∧ P i ω ∧ P j ω) := by
        intro i
        by_cases hia : i = a
        · subst i
          have hh : 0 ≤ ∑ j, mark (a ≠ j ∧ P a ω ∧ P j ω) :=
            Finset.sum_nonneg (fun j _ => mark_nonneg _)
          rw [show mark (P a ω) = 1 by simp [mark,ha],if_pos rfl]
          exact le_add_of_nonneg_right hh
        · rw [if_neg hia,zero_add]
          have hh := Finset.single_le_sum (s := Finset.univ)
            (f := fun j => mark (i ≠ j ∧ P i ω ∧ P j ω))
            (fun j _ => mark_nonneg _) (Finset.mem_univ a)
          simpa [mark,hia,ha] using hh
      have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hi i)
      simpa [Finset.sum_add_distrib] using hh
    · have hn : ∀ i, ¬ P i ω := by simpa using he
      simp [mark,he,hn]
  have hh := average_mono hp
  rw [average_add,average_sum] at hh
  simp_rw [average_sum] at hh
  exact hh

end Bonferroni

abbrev V (m : ℕ) := Fin 3 × Fin (m+1)
abbrev Q (m : ℕ) := 3*(m+1)
instance (m : ℕ) : NeZero (Q m) := ⟨by unfold Q; omega⟩
abbrev Sample (m : ℕ) := Sym2 (V m) → Fin (Q m)

def randomGraph (m : ℕ) (σ : Sample m) : SimpleGraph (V m) where
  Adj a b := a ≠ b ∧ σ s(a,b) = 0
  symm := by
    intro a b h
    refine ⟨h.1.symm,?_⟩
    rw [Sym2.eq_swap]
    exact h.2
  loopless := by intro a h; exact h.1 rfl

/-- The actual Erdos-Renyi graph PMF. Independent uniform coordinate sampling
retains each undirected nonloop edge exactly when its coordinate equals zero.
Unused diagonal coordinates have no effect on the mapped graph law. -/
def graphPMF (m : ℕ) : PMF (SimpleGraph (V m)) :=
  (PMF.uniformOfFintype (Sample m)).map (randomGraph m)

def graphProbability (m : ℕ) (P : SimpleGraph (V m) → Prop) : ℝ :=
  ((graphPMF m).toOuterMeasure {G | P G}).toReal

lemma vertex_card (m : ℕ) : Fintype.card (V m) = Q m := by simp [V,Q]

lemma graphProbability_eq (m : ℕ) (P : SimpleGraph (V m) → Prop) :
    graphProbability m P = probability (fun σ => P (randomGraph m σ)) := by
  unfold graphProbability graphPMF
  rw [PMF.toOuterMeasure_map_apply]
  exact probability_PMF _

lemma sample_atom (m : ℕ) (σ : Sample m) :
    (PMF.uniformOfFintype (Sample m)) σ =
      ∏ _e : Sym2 (V m), ((Q m : ℝ≥0∞)⁻¹) := by
  simp [PMF.uniformOfFintype_apply,Fintype.card_fun,Nat.cast_pow,ENNReal.inv_pow]

lemma edge_membership (m : ℕ) (σ : Sample m) (e : Sym2 (V m)) (hne : ¬ e.IsDiag) :
    e ∈ (randomGraph m σ).edgeSet ↔ σ e = 0 := by
  induction e using Sym2.inductionOn with
  | hf a b =>
    have hab : a ≠ b := by simpa only [Sym2.mk_isDiag_iff] using hne
    change (a ≠ b ∧ σ s(a,b) = 0) ↔ σ s(a,b) = 0
    simp [hab]

/-- The actual graph law has every finite present/absent edge pattern with
the product mass of independent Bernoulli(1 / number-of-vertices) trials. -/
theorem independent_edge_patterns (m : ℕ) (S : Finset (Sym2 (V m)))
    (hS : ∀ e ∈ S, ¬ e.IsDiag) (b : Sym2 (V m) → Bool) :
    graphProbability m (fun G => ∀ e ∈ S, (e ∈ G.edgeSet ↔ b e = true)) =
      ∏ e ∈ S, if b e = true then 1/(Fintype.card (V m) : ℝ)
        else 1-1/(Fintype.card (V m) : ℝ) := by
  rw [graphProbability_eq,vertex_card]
  have he : (fun σ : Sample m => ∀ e ∈ S,
      (e ∈ (randomGraph m σ).edgeSet ↔ b e = true)) =
      (fun σ : Sample m => ∀ e ∈ S, (σ e = 0 ↔ b e = true)) := by
    funext σ
    apply propext
    constructor
    · intro h e he
      exact (edge_membership m σ e (hS e he)).symm.trans (h e he)
    · intro h e he
      exact (edge_membership m σ e (hS e he)).trans (h e he)
  rw [he]
  exact pattern_probability (Q m) S b

abbrev T (m : ℕ) := Fin (m+1) × Fin (m+1) × Fin (m+1)

def e0 {m : ℕ} (t : T m) : Sym2 (V m) := s((0,t.1),(1,t.2.1))
def e1 {m : ℕ} (t : T m) : Sym2 (V m) := s((1,t.2.1),(2,t.2.2))
def e2 {m : ℕ} (t : T m) : Sym2 (V m) := s((2,t.2.2),(0,t.1))
def triangleEdges {m : ℕ} (t : T m) : Finset (Sym2 (V m)) := {e0 t,e1 t,e2 t}

lemma e0_e1 {m : ℕ} (t s : T m) : e0 t ≠ e1 s := by
  simp [e0,e1,Sym2.eq_iff,Prod.mk.injEq]
lemma e0_e2 {m : ℕ} (t s : T m) : e0 t ≠ e2 s := by
  simp [e0,e2,Sym2.eq_iff,Prod.mk.injEq]
lemma e1_e2 {m : ℕ} (t s : T m) : e1 t ≠ e2 s := by
  simp [e1,e2,Sym2.eq_iff,Prod.mk.injEq]
lemma e0_eq {m : ℕ} (t s : T m) : e0 t = e0 s ↔ t.1 = s.1 ∧ t.2.1 = s.2.1 := by
  simp [e0,Sym2.eq_iff,Prod.mk.injEq]
lemma e1_eq {m : ℕ} (t s : T m) : e1 t = e1 s ↔ t.2.1 = s.2.1 ∧ t.2.2 = s.2.2 := by
  simp [e1,Sym2.eq_iff,Prod.mk.injEq]
lemma e2_eq {m : ℕ} (t s : T m) : e2 t = e2 s ↔ t.1 = s.1 ∧ t.2.2 = s.2.2 := by
  simp [e2,Sym2.eq_iff,Prod.mk.injEq,and_comm]

lemma triangleEdges_card {m : ℕ} (t : T m) : (triangleEdges t).card = 3 := by
  simp [triangleEdges,e0_e1,e0_e2,e1_e2]

def triangleEvent {m : ℕ} (t : T m) (σ : Sample m) : Prop :=
  ∀ e ∈ triangleEdges t, σ e = 0

def HasTriangle {W : Type*} (G : SimpleGraph W) : Prop :=
  ∃ a b c, G.Adj a b ∧ G.Adj b c ∧ G.Adj c a

lemma actual_triangle {m : ℕ} {t : T m} {σ : Sample m} (h : triangleEvent t σ) :
    HasTriangle (randomGraph m σ) := by
  refine ⟨(0,t.1),(1,t.2.1),(2,t.2.2),?_,?_,?_⟩
  · exact ⟨by simp, h (e0 t) (by simp [triangleEdges])⟩
  · exact ⟨by simp, h (e1 t) (by simp [triangleEdges])⟩
  · exact ⟨by simp, h (e2 t) (by simp [triangleEdges])⟩

lemma triangle_probability {m : ℕ} (t : T m) :
    probability (triangleEvent t) = (1/(Q m : ℝ))^3 := by
  change probability (fun σ : Sample m => ∀ e ∈ triangleEdges t, σ e = 0) = _
  rw [cylinder_probability,triangleEdges_card]

def shares {m : ℕ} (t s : T m) : Prop :=
  (t.1 = s.1 ∧ t.2.1 = s.2.1) ∨
  (t.1 = s.1 ∧ t.2.2 = s.2.2) ∨
  (t.2.1 = s.2.1 ∧ t.2.2 = s.2.2)

lemma singleton_union_eq_insert {α : Type*} [DecidableEq α] (a : α) (S : Finset α) :
    {a} ∪ S = insert a S := by ext x; simp

lemma joint_edges_card {m : ℕ} (t s : T m) (hne : t ≠ s) :
    (triangleEdges t ∪ triangleEdges s).card = if shares t s then 5 else 6 := by
  by_cases ha : t.1 = s.1 <;>
    by_cases hb : t.2.1 = s.2.1 <;> by_cases hc : t.2.2 = s.2.2
  all_goals first
    | exact False.elim (hne (Prod.ext ha (Prod.ext hb hc)))
    | simp [shares,triangleEdges,Finset.insert_union,singleton_union_eq_insert,
        Finset.card_insert_eq_ite,e0_e1,e0_e2,e1_e2,
        Ne.symm (e0_e1 s t),Ne.symm (e0_e2 s t),Ne.symm (e1_e2 s t),
        e0_eq,e1_eq,e2_eq,ha,hb,hc,eq_comm]

lemma joint_probability {m : ℕ} (t s : T m) (hne : t ≠ s) :
    probability (fun σ => triangleEvent t σ ∧ triangleEvent s σ) =
      if shares t s then (1/(Q m : ℝ))^5 else (1/(Q m : ℝ))^6 := by
  have he : (fun σ => triangleEvent t σ ∧ triangleEvent s σ) =
      (fun σ : Sample m => ∀ e ∈ triangleEdges t ∪ triangleEdges s, σ e = 0) := by
    funext σ
    apply propext
    constructor
    · intro h e he
      rcases Finset.mem_union.mp he with ht | hs
      · exact h.1 e ht
      · exact h.2 e hs
    · intro h
      exact ⟨fun e he => h e (Finset.mem_union_left _ he),
        fun e he => h e (Finset.mem_union_right _ he)⟩
  rw [he,cylinder_probability,joint_edges_card t s hne]
  split_ifs <;> rfl

lemma pair_probability_upper {m : ℕ} (t s : T m) :
    probability (fun σ => t ≠ s ∧ triangleEvent t σ ∧ triangleEvent s σ) ≤
      (1/(Q m : ℝ))^6 +
      mark (t.1 = s.1 ∧ t.2.1 = s.2.1) * (1/(Q m : ℝ))^5 +
      mark (t.1 = s.1 ∧ t.2.2 = s.2.2) * (1/(Q m : ℝ))^5 +
      mark (t.2.1 = s.2.1 ∧ t.2.2 = s.2.2) * (1/(Q m : ℝ))^5 := by
  by_cases hne : t ≠ s
  · have he : (fun σ => t ≠ s ∧ triangleEvent t σ ∧ triangleEvent s σ) =
        (fun σ => triangleEvent t σ ∧ triangleEvent s σ) := by
      funext σ; apply propext; simp [hne]
    rw [he,joint_probability t s hne]
    by_cases ha : t.1 = s.1 <;>
      by_cases hb : t.2.1 = s.2.1 <;> by_cases hc : t.2.2 = s.2.2
    all_goals simp [shares,mark,ha,hb,hc] <;> positivity
  · have he : probability (fun σ : Sample m => t ≠ s ∧ triangleEvent t σ ∧ triangleEvent s σ) = 0 := by
      simp [probability,average,mark,hne]
    rw [he]
    have h1 := mark_nonneg (t.1 = s.1 ∧ t.2.1 = s.2.1)
    have h2 := mark_nonneg (t.1 = s.1 ∧ t.2.2 = s.2.2)
    have h3 := mark_nonneg (t.2.1 = s.2.1 ∧ t.2.2 = s.2.2)
    positivity

lemma overlap_count0 (m : ℕ) :
    (∑ t : T m, ∑ s : T m, mark (t.1 = s.1 ∧ t.2.1 = s.2.1)) = ((m+1 : ℕ) : ℝ)^4 := by
  simp [T,Fintype.sum_prod_type,mark_and,← Finset.mul_sum,← Finset.sum_mul,sum_mark_eq]
  ring
lemma overlap_count1 (m : ℕ) :
    (∑ t : T m, ∑ s : T m, mark (t.1 = s.1 ∧ t.2.2 = s.2.2)) = ((m+1 : ℕ) : ℝ)^4 := by
  simp [T,Fintype.sum_prod_type,mark_and,← Finset.mul_sum,← Finset.sum_mul,sum_mark_eq]
  ring
lemma overlap_count2 (m : ℕ) :
    (∑ t : T m, ∑ s : T m, mark (t.2.1 = s.2.1 ∧ t.2.2 = s.2.2)) = ((m+1 : ℕ) : ℝ)^4 := by
  simp [T,Fintype.sum_prod_type,mark_and,← Finset.mul_sum,← Finset.sum_mul,sum_mark_eq]
  ring

lemma pair_sum_upper (m : ℕ) :
    (∑ t : T m, ∑ s : T m,
      probability (fun σ => t ≠ s ∧ triangleEvent t σ ∧ triangleEvent s σ)) ≤
      ((m+1 : ℕ) : ℝ)^6 * (1/(Q m : ℝ))^6 +
      3*((m+1 : ℕ) : ℝ)^4 * (1/(Q m : ℝ))^5 := by
  calc
    _ ≤ ∑ t : T m, ∑ s : T m, ((1/(Q m : ℝ))^6 +
        mark (t.1 = s.1 ∧ t.2.1 = s.2.1) * (1/(Q m : ℝ))^5 +
        mark (t.1 = s.1 ∧ t.2.2 = s.2.2) * (1/(Q m : ℝ))^5 +
        mark (t.2.1 = s.2.1 ∧ t.2.2 = s.2.2) * (1/(Q m : ℝ))^5) :=
      Finset.sum_le_sum (fun t _ => Finset.sum_le_sum (fun s _ => pair_probability_upper t s))
    _ = _ := by
      simp_rw [Finset.sum_add_distrib,← Finset.sum_mul]
      rw [overlap_count0,overlap_count1,overlap_count2]
      simp [T,Fintype.card_prod]
      ring

lemma first_sum (m : ℕ) : (∑ t : T m, probability (triangleEvent t)) = 1/27 := by
  simp only [triangle_probability,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  simp [T,Q,Fintype.card_prod]
  field_simp
  ring

theorem tripartite_triangle_lower (m : ℕ) :
    (1/50 : ℝ) ≤ probability (fun σ : Sample m => ∃ t : T m, triangleEvent t σ) := by
  have hb := probability_union_lower (fun t : T m => triangleEvent t)
  rw [first_sum] at hb
  have hu := pair_sum_upper m
  have hm : (0 : ℝ) < ((m+1 : ℕ) : ℝ) := by positivity
  have he : ((m+1 : ℕ) : ℝ)^6*(1/(Q m : ℝ))^6 +
      3*((m+1 : ℕ) : ℝ)^4*(1/(Q m : ℝ))^5 =
      1/729 + 1/(81*((m+1 : ℕ) : ℝ)) := by
    simp only [Q,Nat.cast_mul,Nat.cast_ofNat]
    field_simp
    ring
  rw [he] at hu
  have hd : 1/(81*((m+1 : ℕ) : ℝ)) ≤ 1/81 := by
    apply one_div_le_one_div_of_le (by norm_num)
    have h : (1 : ℝ) ≤ ((m+1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ m+1 by omega)
    linarith
  linarith

theorem graph_triangle_lower (m : ℕ) : (1/50 : ℝ) ≤ graphProbability m HasTriangle := by
  rw [graphProbability_eq]
  exact (tripartite_triangle_lower m).trans (probability_mono (fun _ h =>
    let ⟨_,ht⟩ := h; actual_triangle ht))

theorem triangle_not_acyclic {W : Type*} {G : SimpleGraph W} (h : HasTriangle G) :
    ¬ G.IsAcyclic := by
  obtain ⟨a,b,c,hab,hbc,hca⟩ := h
  intro hac
  let w : G.Walk a a := .cons hab (.cons hbc (.cons hca .nil))
  apply hac w
  simp [w,SimpleGraph.Walk.isCycle_def,SimpleGraph.Walk.isTrail_def,
    Sym2.eq_iff,hab.ne,hbc.ne,hca.ne,Ne.symm hab.ne,Ne.symm hbc.ne,Ne.symm hca.ne]

theorem trianglefree_probability_upper (m : ℕ) :
    graphProbability m (fun G => ¬ HasTriangle G) ≤ 49/50 := by
  have hh := graph_triangle_lower m
  rw [graphProbability_eq] at hh ⊢
  rw [probability_compl]
  linarith

theorem forest_probability_upper (m : ℕ) :
    graphProbability m SimpleGraph.IsAcyclic ≤ 49/50 := by
  have hh := trianglefree_probability_upper m
  rw [graphProbability_eq] at hh ⊢
  apply le_trans (probability_mono (fun σ hA =>
    show ¬ HasTriangle (randomGraph m σ) from fun hT => triangle_not_acyclic hT hA)) hh

open Filter Topology

theorem vertex_card_tends_atTop :
    Tendsto (fun m : ℕ => Fintype.card (V m)) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  apply eventually_atTop.2
  refine ⟨b,?_⟩
  intro m hm
  rw [vertex_card]
  unfold Q
  omega

theorem trianglefree_not_tends_one :
    ¬ Tendsto (fun m : ℕ => graphProbability m (fun G => ¬ HasTriangle G)) atTop (𝓝 1) := by
  intro h
  have he := (tendsto_order.1 h).1 (99/100 : ℝ) (by norm_num)
  obtain ⟨m,hm⟩ := he.exists
  have hb := trianglefree_probability_upper m
  linarith

theorem forest_not_tends_one :
    ¬ Tendsto (fun m : ℕ => graphProbability m SimpleGraph.IsAcyclic) atTop (𝓝 1) := by
  intro h
  have he := (tendsto_order.1 h).1 (99/100 : ℝ) (by norm_num)
  obtain ⟨m,hm⟩ := he.exists
  have hb := forest_probability_upper m
  linarith

end
end Conjecture5029

#print axioms Conjecture5029.graphPMF
#print axioms Conjecture5029.independent_edge_patterns
#print axioms Conjecture5029.actual_triangle
#print axioms Conjecture5029.joint_edges_card
#print axioms Conjecture5029.graph_triangle_lower
#print axioms Conjecture5029.triangle_not_acyclic
#print axioms Conjecture5029.vertex_card_tends_atTop
#print axioms Conjecture5029.trianglefree_not_tends_one
#print axioms Conjecture5029.forest_not_tends_one





