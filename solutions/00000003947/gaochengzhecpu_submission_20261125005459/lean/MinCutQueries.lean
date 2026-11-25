import Std

namespace C3947

inductive BlockVertex (t : Nat) where
  | hub (which : Bool)
  | leaf (group : Bool) (position : Fin t)
  deriving DecidableEq

abbrev Vertex (t : Nat) := Bool × BlockVertex t
abbrev Edge (t : Nat) := Vertex t × Vertex t
abbrev Oracle (t : Nat) := Edge t → Bool

def reverse (edge : Edge t) : Edge t := (edge.2, edge.1)

def SameEdge (left right : Edge t) : Prop := left = right ∨ left = reverse right

instance (left right : Edge t) : Decidable (SameEdge left right) := by
  unfold SameEdge
  infer_instance

private theorem same_symmetric {a b : Edge t} (h : SameEdge a b) : SameEdge b a := by
  rcases h with h | h
  · exact Or.inl h.symm
  · exact Or.inr (congrArg reverse h).symm

private theorem same_transitive {a b c : Edge t} (h : SameEdge a b)
    (h' : SameEdge b c) : SameEdge a c := by
  rcases h with h | h
  · exact h ▸ h'
  · rcases h' with h' | h'
    · exact Or.inr (h.trans (congrArg reverse h'))
    · exact Or.inl (by simpa [reverse] using h.trans (congrArg reverse h'))

def hub (t : Nat) (side which : Bool) : Vertex t := (side, .hub which)
def leaf (side group : Bool) (position : Fin t) : Vertex t := (side, .leaf group position)

def spoke (side which group : Bool) (position : Fin t) : Edge t :=
  (hub t side which, leaf side group position)

def bridge (t : Nat) : Edge t := (hub t false false, hub t true false)

def blockEdge : Edge t → Bool
  | ((side, .hub _), (other, .leaf _ _)) => side == other
  | ((side, .leaf _ _), (other, .hub _)) => side == other
  | _ => false

def base (t : Nat) (edge : Edge t) : Bool :=
  blockEdge edge || decide (SameEdge edge (bridge t))

def row (ht : 0 < t) (i : Fin (t * t)) : Fin t :=
  ⟨i.val / t, (Nat.div_lt_iff_lt_mul ht).mpr i.isLt⟩

def column (ht : 0 < t) (i : Fin (t * t)) : Fin t :=
  ⟨i.val % t, Nat.mod_lt _ ht⟩

def candidate (ht : 0 < t) (across : Bool) (i : Fin (t * t)) : Edge t :=
  (leaf false false (row ht i), leaf across true (column ht i))

def input (ht : 0 < t) (across : Bool) (i : Fin (t * t)) (edge : Edge t) : Bool :=
  base t edge || decide (SameEdge edge (candidate ht across i))

private theorem candidate_injective {t : Nat} (ht : 0 < t) (across : Bool)
    {i j : Fin (t * t)} (h : candidate ht across i = candidate ht across j) : i = j := by
  have hr : row ht i = row ht j := by
    have hfirst := congrArg Prod.fst h
    simpa [candidate, leaf] using hfirst
  have hc : column ht i = column ht j := by
    have hsecond := congrArg Prod.snd h
    simpa [candidate, leaf] using hsecond
  apply Fin.ext
  have hrow : i.val / t = j.val / t := congrArg Fin.val hr
  have hcolumn : i.val % t = j.val % t := congrArg Fin.val hc
  calc
    i.val = i.val % t + t * (i.val / t) := (Nat.mod_add_div i.val t).symm
    _ = j.val % t + t * (j.val / t) := by rw [hrow, hcolumn]
    _ = j.val := Nat.mod_add_div j.val t

theorem one_candidate_per_query (ht : 0 < t) (across : Bool) (query : Edge t)
    (i j : Fin (t * t)) (hi : SameEdge query (candidate ht across i))
    (hj : SameEdge query (candidate ht across j)) : i = j := by
  rcases same_transitive (same_symmetric hi) hj with h | h
  · exact candidate_injective ht across h
  · have hfirst := congrArg Prod.fst h
    simp [candidate, leaf, reverse] at hfirst

def Crosses (color : Vertex t → Bool) (edge : Edge t) : Prop :=
  color edge.1 ≠ color edge.2

/-- A partition crossed by precisely one undirected edge. -/
def HasUnitCut (oracle : Oracle t) : Prop :=
  ∃ color : Vertex t → Bool, ∃ edge,
    oracle edge = true ∧ Crosses color edge ∧
      ∀ other, oracle other = true → Crosses color other → SameEdge other edge

private theorem spoke_in_base (s h g : Bool) (i : Fin t) : base t (spoke s h g i) = true := by
  simp [base, blockEdge, spoke, hub, leaf]

private theorem bridge_in_base (t : Nat) : base t (bridge t) = true := by
  simp [base, SameEdge]

private theorem base_in_input (ht : 0 < t) (across : Bool) (i : Fin (t * t)) {e : Edge t}
    (h : base t e = true) : input ht across i e = true := by
  simp [input, h]

private theorem same_reversed (a b : Edge t) : SameEdge (reverse a) b ↔ SameEdge a b := by
  constructor
  · rintro (h | h)
    · exact Or.inr (congrArg reverse h)
    · exact Or.inl (congrArg reverse h)
  · rintro (h | h)
    · exact Or.inr (congrArg reverse h)
    · exact Or.inl (congrArg reverse h)

private theorem block_reversed (edge : Edge t) : blockEdge (reverse edge) = blockEdge edge := by
  rcases edge with ⟨⟨s, a⟩, ⟨s', b⟩⟩
  cases a <;> cases b <;> cases s <;> cases s' <;> rfl

theorem input_undirected (ht : 0 < t) (across : Bool) (i : Fin (t * t)) (edge : Edge t) :
    input ht across i (reverse edge) = input ht across i edge := by
  by_cases onBridge : SameEdge edge (bridge t) <;>
    by_cases onCandidate : SameEdge edge (candidate ht across i) <;>
    simp [input, base, block_reversed, same_reversed, onBridge, onCandidate]

private theorem loop_not_same {edge : Edge t} (distinct : edge.1 ≠ edge.2) (v : Vertex t) :
    ¬ SameEdge (v, v) edge := by
  rintro (h | h)
  · exact distinct ((congrArg Prod.fst h).symm.trans (congrArg Prod.snd h))
  · exact distinct ((congrArg Prod.snd h).symm.trans (congrArg Prod.fst h))

theorem input_loopless (ht : 0 < t) (across : Bool) (i : Fin (t * t)) (v : Vertex t) :
    input ht across i (v, v) = false := by
  have bridge_distinct : (bridge t).1 ≠ (bridge t).2 := by simp [bridge, hub]
  have candidate_distinct : (candidate ht across i).1 ≠ (candidate ht across i).2 := by
    simp [candidate, leaf]
  have hBlock : blockEdge (v, v) = false := by
    rcases v with ⟨s, a⟩
    cases a <;> rfl
  simp [input, base, hBlock, loop_not_same bridge_distinct v, loop_not_same candidate_distinct v]

private theorem constant_on_block (ht : 0 < t) (color : Vertex t → Bool) (side : Bool)
    (unique : ∀ e f, base t e = true → Crosses color e → base t f = true →
      Crosses color f → SameEdge e f) :
    ∀ v : BlockVertex t, color (side, v) = color (hub t side false) := by
  have hubs_equal : color (hub t side false) = color (hub t side true) := by
    by_cases equal : color (hub t side false) = color (hub t side true)
    · exact equal
    · let i : Fin t := ⟨0, ht⟩
      have crossed (group : Bool) : ∃ h, Crosses color (spoke side h group i) := by
        by_cases same : color (hub t side false) = color (leaf side group i)
        · exact ⟨true, fun he => equal (same.trans he.symm)⟩
        · exact ⟨false, same⟩
      obtain ⟨h₀, c₀⟩ := crossed false
      obtain ⟨h₁, c₁⟩ := crossed true
      have same := unique _ _ (spoke_in_base side h₀ false i) c₀
        (spoke_in_base side h₁ true i) c₁
      rcases same with eq | eq
      · have hs := congrArg Prod.snd eq
        simp [spoke, leaf] at hs
      · have hf := congrArg Prod.fst eq
        simp [spoke, hub, leaf, reverse] at hf
  intro v
  cases v with
  | hub h => cases h <;> first | rfl | exact hubs_equal.symm
  | leaf group position =>
    by_cases same : color (leaf side group position) = color (hub t side false)
    · exact same
    · have c₀ : Crosses color (spoke side false group position) := fun h => same h.symm
      have c₁ : Crosses color (spoke side true group position) :=
        fun h => same ((hubs_equal.trans h).symm)
      have sameEdge := unique _ _ (spoke_in_base side false group position) c₀
        (spoke_in_base side true group position) c₁
      rcases sameEdge with eq | eq
      · have hf := congrArg Prod.fst eq
        simp [spoke, hub] at hf
      · have hf := congrArg Prod.fst eq
        simp [spoke, hub, leaf, reverse] at hf

private theorem equal_everywhere {color : Vertex t → Bool}
    (constant : ∀ side (a : BlockVertex t), color (side, a) = color (hub t side false))
    (equal : color (hub t false false) = color (hub t true false)) (u v : Vertex t) :
    color u = color v := by
  rcases u with ⟨s, a⟩
  rcases v with ⟨s', b⟩
  rw [constant s a, constant s' b]
  cases s <;> cases s' <;> first | rfl | exact equal | exact equal.symm

/-- Every nontrivial partition has a crossing edge, hence the promised graph is connected. -/
theorem input_cuts_nonempty (ht : 0 < t) (across : Bool) (i : Fin (t * t))
    (color : Vertex t → Bool) (u v : Vertex t) (different : color u ≠ color v) :
    ∃ edge, input ht across i edge = true ∧ Crosses color edge := by
  classical
  by_cases found : ∃ edge, base t edge = true ∧ Crosses color edge
  · obtain ⟨edge, present, crosses⟩ := found
    exact ⟨edge, base_in_input ht across i present, crosses⟩
  · exfalso
    have unique : ∀ e f, base t e = true → Crosses color e → base t f = true →
        Crosses color f → SameEdge e f := by
      intro e _ present crosses _ _
      exact False.elim (found ⟨e, present, crosses⟩)
    have sameHubs : color (hub t false false) = color (hub t true false) := by
      by_cases equal : color (hub t false false) = color (hub t true false)
      · exact equal
      · exact False.elim (found ⟨bridge t, bridge_in_base t, equal⟩)
    exact different (equal_everywhere (fun side => constant_on_block ht color side unique) sameHubs u v)

theorem within_has_unit_cut (ht : 0 < t) (i : Fin (t * t)) : HasUnitCut (input ht false i) := by
  have bridge_cross : Crosses (t := t) Prod.fst (bridge t) := by
    change (false : Bool) ≠ true
    decide
  refine ⟨Prod.fst, bridge t, base_in_input ht false i (bridge_in_base t), bridge_cross, ?_⟩
  intro edge existsEdge crosses
  have hblock : blockEdge edge = false := by
    rcases edge with ⟨⟨s, a⟩, ⟨s', b⟩⟩
    change s ≠ s' at crosses
    cases a <;> cases b <;> simp [blockEdge, crosses]
  have hnew : ¬ SameEdge edge (candidate ht false i) := by
    intro same
    rcases same with he | he
    · subst edge
      exact crosses rfl
    · subst edge
      exact crosses rfl
  simpa [input, base, hblock, hnew] using existsEdge

theorem across_has_no_unit_cut (ht : 0 < t) (i : Fin (t * t)) : ¬ HasUnitCut (input ht true i) := by
  rintro ⟨color, edge, _, crosses, unique⟩
  have allBase : ∀ e f, base t e = true → Crosses color e → base t f = true →
      Crosses color f → SameEdge e f := by
    intro e f he ec hf fc
    exact same_transitive (unique e (base_in_input ht true i he) ec)
      (same_symmetric (unique f (base_in_input ht true i hf) fc))
  have constant := fun side => constant_on_block ht color side allBase
  have opposite : color (hub t false false) ≠ color (hub t true false) := by
    intro equal
    exact crosses (equal_everywhere constant equal edge.1 edge.2)
  have bridge_cross : Crosses color (bridge t) := opposite
  have new_cross : Crosses color (candidate ht true i) := by
    intro equal
    change color (false, .leaf false (row ht i)) = color (true, .leaf true (column ht i)) at equal
    rw [constant false _, constant true _] at equal
    exact opposite equal
  have new_exists : input ht true i (candidate ht true i) = true := by
    simp [input, SameEdge]
  have same := same_transitive
    (unique (bridge t) (base_in_input ht true i (bridge_in_base t)) bridge_cross)
    (same_symmetric (unique (candidate ht true i) new_exists new_cross))
  rcases same with he | he
  · have hf := congrArg Prod.fst he
    simp [bridge, hub, candidate, leaf] at hf
  · have hf := congrArg Prod.fst he
    simp [bridge, hub, candidate, leaf, reverse] at hf

private theorem covered_length {A B : Type} [BEq A] [LawfulBEq A] (hits : B → A → Prop)
    (unique : ∀ q a b, hits q a → hits q b → a = b)
    (queries : List B) (choices : List A) (distinct : choices.Nodup)
    (cover : ∀ a ∈ choices, ∃ q ∈ queries, hits q a) : choices.length ≤ queries.length := by
  classical
  induction queries generalizing choices with
  | nil =>
    cases choices with
    | nil => simp
    | cons first rest =>
      obtain ⟨q, member, _⟩ := cover first (by simp)
      simp at member
  | cons q rest ih =>
    by_cases someHit : ∃ a ∈ choices, hits q a
    · obtain ⟨a, ha, hitA⟩ := someHit
      have residual_cover : ∀ b ∈ choices.erase a, ∃ r ∈ rest, hits r b := by
        intro b hb
        obtain ⟨different, old⟩ := (distinct.mem_erase_iff.mp hb)
        obtain ⟨r, hr, hitB⟩ := cover b old
        rcases List.mem_cons.mp hr with same | tail
        · subst r
          exact False.elim (different (unique q b a hitB hitA))
        · exact ⟨r, tail, hitB⟩
      have bounds := ih (choices.erase a) (distinct.erase a) residual_cover
      rw [List.length_erase_of_mem ha] at bounds
      simp only [List.length_cons]
      omega
    · have residual_cover : ∀ b ∈ choices, ∃ r ∈ rest, hits r b := by
        intro b hb
        obtain ⟨r, hr, hitB⟩ := cover b hb
        rcases List.mem_cons.mp hr with same | tail
        · subst r
          exact False.elim (someHit ⟨b, hb, hitB⟩)
        · exact ⟨r, tail, hitB⟩
      have bounds := ih choices distinct residual_cover
      simp only [List.length_cons]
      omega

private theorem finRange_nodup (n : Nat) : (List.finRange n).Nodup := by
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj ordered equal
  rw [List.getElem_finRange, List.getElem_finRange] at equal
  have values := congrArg Fin.val equal
  change i = j at values
  omega

private theorem missed_candidate (ht : 0 < t) (across : Bool) (queries : List (Edge t))
    (tooShort : queries.length < t * t) :
    ∃ i : Fin (t * t), ∀ q ∈ queries, ¬ SameEdge q (candidate ht across i) := by
  classical
  by_cases existsMiss : ∃ i : Fin (t * t), ∀ q ∈ queries, ¬ SameEdge q (candidate ht across i)
  · exact existsMiss
  · exfalso
    have cover : ∀ i ∈ List.finRange (t * t), ∃ q ∈ queries, SameEdge q (candidate ht across i) := by
      intro i _
      by_cases hit : ∃ q ∈ queries, SameEdge q (candidate ht across i)
      · exact hit
      · exact False.elim (existsMiss ⟨i, fun q member same => hit ⟨q, member, same⟩⟩)
    have bound := covered_length (fun q i => SameEdge q (candidate ht across i))
      (one_candidate_per_query ht across) queries (List.finRange (t * t))
      (finRange_nodup (t * t)) cover
    rw [List.length_finRange] at bound
    exact (Nat.not_lt_of_ge bound) tooShort

inductive DecisionTree (t : Nat) where
  | answer (unitCut : Bool)
  | ask (edge : Edge t) (ifPresent ifAbsent : DecisionTree t)

def run (oracle : Oracle t) : DecisionTree t → Bool
  | .answer result => result
  | .ask q yes no => if oracle q then run oracle yes else run oracle no

def transcript (oracle : Oracle t) : DecisionTree t → List (Edge t)
  | .answer _ => []
  | .ask q yes no => q :: (if oracle q then transcript oracle yes else transcript oracle no)

def depth : DecisionTree t → Nat
  | .answer _ => 0
  | .ask _ yes no => (max (depth yes) (depth no)) + 1

private theorem transcript_le_depth (oracle : Oracle t) (tree : DecisionTree t) :
    (transcript oracle tree).length ≤ depth tree := by
  induction tree with
  | answer result => simp [transcript, depth]
  | ask q yes no ihY ihN =>
    cases h : oracle q
    · simp [transcript, depth, h]
      exact Nat.le_trans ihN (Nat.le_max_right _ _)
    · simp [transcript, depth, h]
      exact Nat.le_trans ihY (Nat.le_max_left _ _)

private theorem run_eq_when_agree (expected actual : Oracle t) (tree : DecisionTree t)
    (agrees : ∀ q ∈ transcript expected tree, expected q = actual q) :
    run expected tree = run actual tree := by
  induction tree with
  | answer result => rfl
  | ask e yes no ihYes ihNo =>
    have e_eq := agrees e (by simp [transcript])
    cases h : expected e
    · have hActual : actual e = false := e_eq.symm.trans h
      simp [run, h, hActual]
      apply ihNo
      intro q member
      exact agrees q (by simp [transcript, h, member])
    · have hActual : actual e = true := e_eq.symm.trans h
      simp [run, h, hActual]
      apply ihYes
      intro q member
      exact agrees q (by simp [transcript, h, member])

def truncate : DecisionTree t → Nat → DecisionTree t
  | .answer result, _ => .answer result
  | .ask _ _ _, 0 => .answer false
  | .ask e yes no, n + 1 => .ask e (truncate yes n) (truncate no n)

private theorem truncate_depth (tree : DecisionTree t) (n : Nat) : depth (truncate tree n) ≤ n := by
  induction tree generalizing n with
  | answer result => simp [truncate, depth]
  | ask q yes no ihYes ihNo =>
    cases n with
    | zero => simp [truncate, depth]
    | succ n =>
      simp [truncate, depth]
      exact Nat.max_le.mpr ⟨ihYes n, ihNo n⟩

private theorem truncate_run (oracle : Oracle t) (tree : DecisionTree t) (n : Nat)
    (within : (transcript oracle tree).length ≤ n) : run oracle (truncate tree n) = run oracle tree := by
  induction tree generalizing n with
  | answer result => rfl
  | ask e yes no ihYes ihNo =>
    cases n with
    | zero => simp [transcript] at within
    | succ n =>
      cases h : oracle e
      · simpa only [truncate, run, h, Bool.false_eq_true, ↓reduceIte] using
          ihNo n (by simpa [transcript, h] using within)
      · simpa only [truncate, run, h, ↓reduceIte] using
          ihYes n (by simpa [transcript, h] using within)

def CorrectOnPromisedInputs (ht : 0 < t) (tree : DecisionTree t) : Prop :=
  ∀ across i, run (input ht across i) tree = true ↔ HasUnitCut (input ht across i)

private theorem depth_lower_bound (ht : 0 < t) (tree : DecisionTree t)
    (correct : CorrectOnPromisedInputs ht tree) : t * t ≤ depth tree := by
  by_cases adequate : t * t ≤ depth tree
  · exact adequate
  · exfalso
    have short : (transcript (base t) tree).length < t * t :=
      Nat.lt_of_le_of_lt (transcript_le_depth (base t) tree) (Nat.lt_of_not_ge adequate)
    obtain ⟨i, missWithin⟩ := missed_candidate ht false (transcript (base t) tree) short
    obtain ⟨j, missAcross⟩ := missed_candidate ht true (transcript (base t) tree) short
    have sameWithin := run_eq_when_agree (base t) (input ht false i) tree
      (fun q member => by simp [input, missWithin q member])
    have sameAcross := run_eq_when_agree (base t) (input ht true j) tree
      (fun q member => by simp [input, missAcross q member])
    have withinYes := (correct false i).mpr (within_has_unit_cut ht i)
    have acrossYes := sameAcross.symm.trans (sameWithin.trans withinYes)
    exact across_has_no_unit_cut ht j ((correct true j).mp acrossYes)

/-- Some promised input makes at least `t*t` queries, even if other paths are impossible. -/
theorem quadratic_lower_bound (ht : 0 < t) (tree : DecisionTree t)
    (correct : CorrectOnPromisedInputs ht tree) :
    ∃ across i, t * t ≤ (transcript (input ht across i) tree).length := by
  classical
  by_cases long : ∃ across i, t * t ≤ (transcript (input ht across i) tree).length
  · exact long
  · exfalso
    let budget := t * t - 1
    have short (across : Bool) (i : Fin (t * t)) :
        (transcript (input ht across i) tree).length ≤ budget := by
      have tooShort := Nat.lt_of_not_ge (fun h => long ⟨across, i, h⟩)
      exact Nat.le_sub_of_add_le (by omega : (transcript (input ht across i) tree).length + 1 ≤ t * t)
    have truncatedCorrect : CorrectOnPromisedInputs ht (truncate tree budget) := by
      intro across i
      rw [truncate_run _ _ _ (short across i)]
      exact correct across i
    have lower := depth_lower_bound ht (truncate tree budget) truncatedCorrect
    have upper := truncate_depth tree budget
    have positive : 0 < t * t := Nat.mul_pos ht ht
    dsimp [budget] at lower upper
    omega

theorem quadratic_exceeds_any_linear_bound (C : Nat) :
    ∃ t, 0 < t ∧ C * (8 * t + 2) < t * t := by
  let t := 10 * C + 1
  have positive : 0 < t := by dsimp [t]; omega
  refine ⟨t, positive, ?_⟩
  calc
    C * (8 * t + 2) ≤ C * (10 * t) := Nat.mul_le_mul_left C (by omega)
    _ = (10 * C) * t := by ac_rfl
    _ < t * t := Nat.mul_lt_mul_of_pos_right (by dsimp [t]; omega) positive

#print axioms quadratic_lower_bound

end C3947
