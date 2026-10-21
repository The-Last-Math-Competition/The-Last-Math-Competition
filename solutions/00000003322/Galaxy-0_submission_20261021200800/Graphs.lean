import Std

namespace TLMC3322.Graphs

abbrev Graph (n : Nat) := Fin n → Fin n → Bool

def Simple {n : Nat} (G : Graph n) : Prop :=
  (∀ v, G v v = false) ∧ (∀ u v, G u v = G v u)

def Bipartite {n : Nat} (G : Graph n) : Prop :=
  ∃ color : Fin n → Bool, ∀ u v, G u v = true → color u ≠ color v

/-- A simple cycle is a cyclically adjacent injective list of at least 3 vertices. -/
def HasCycle {n : Nat} (G : Graph n) : Prop :=
  ∃ k : Nat, ∃ hk : 3 ≤ k, ∃ f : Fin k → Fin n,
    (∀ i j, f i = f j → i = j) ∧
    ∀ i : Fin k, G (f i) (f ⟨(i.val+1)%k, Nat.mod_lt _ (by omega)⟩) = true

def Forest {n : Nat} (G : Graph n) : Prop := ¬ HasCycle G

def disjointEdges {n : Nat} (e f : Fin n × Fin n) : Prop :=
  e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2

def Matching {n : Nat} (G : Graph n) (edges : List (Fin n × Fin n)) : Prop :=
  (∀ e ∈ edges, G e.1 e.2 = true) ∧ edges.Pairwise disjointEdges

def MatchingNumber {n : Nat} (G : Graph n) (m : Nat) : Prop :=
  (∃ edges, Matching G edges ∧ edges.length = m) ∧
  ∀ edges, Matching G edges → edges.length ≤ m

def K2 : Graph 2 := fun u v => decide (u ≠ v)
def K3 : Graph 3 := fun u v => decide (u ≠ v)

theorem K2_simple : Simple K2 := by unfold Simple; decide
theorem K3_simple : Simple K3 := by unfold Simple; decide

theorem K2_bipartite : Bipartite K2 := by
  refine ⟨fun v => decide (v.val = 0), ?_⟩
  decide

theorem K2_forest : Forest K2 := by
  rintro ⟨k,hk,f,hi,_⟩
  let a : Fin k := ⟨0,by omega⟩
  let b : Fin k := ⟨1,by omega⟩
  let c : Fin k := ⟨2,by omega⟩
  have hab : f a ≠ f b := by intro h; have he := congrArg Fin.val (hi a b h); simp [a,b] at he
  have hac : f a ≠ f c := by intro h; have he := congrArg Fin.val (hi a c h); simp [a,c] at he
  have hbc : f b ≠ f c := by intro h; have he := congrArg Fin.val (hi b c h); simp [b,c] at he
  have pigeonhole : ∀ x y z : Fin 2, x = y ∨ x = z ∨ y = z := by decide
  rcases pigeonhole (f a) (f b) (f c) with h | h | h
  · exact hab h
  · exact hac h
  · exact hbc h

theorem K3_not_bipartite : ¬ Bipartite K3 := by
  rintro ⟨color,hc⟩
  have h01 := hc 0 1 (by decide)
  have h02 := hc 0 2 (by decide)
  have h12 := hc 1 2 (by decide)
  have pigeonhole : ∀ a b c : Bool, a = b ∨ a = c ∨ b = c := by decide
  rcases pigeonhole (color 0) (color 1) (color 2) with h | h | h
  · exact h01 h
  · exact h02 h
  · exact h12 h

theorem matching_length_le_one {n : Nat} (G : Graph n)
    (h : ∀ a b c d, G a b = true → G c d = true →
      ¬ disjointEdges (a,b) (c,d))
    (edges : List (Fin n × Fin n)) (hm : Matching G edges) :
    edges.length ≤ 1 := by
  cases edges with
  | nil => simp
  | cons e tail =>
    cases tail with
    | nil => simp
    | cons f rest =>
      have he := hm.1 e (by simp)
      have hf := hm.1 f (by simp)
      have hd : disjointEdges e f := (List.pairwise_cons.mp hm.2).1 f (by simp)
      exact False.elim (h e.1 e.2 f.1 f.2 he hf hd)

theorem K2_matching_one : MatchingNumber K2 1 := by
  constructor
  · exact ⟨[(0,1)], by simp [Matching, K2], rfl⟩
  · apply matching_length_le_one
    unfold disjointEdges
    decide

theorem K3_matching_one : MatchingNumber K3 1 := by
  constructor
  · exact ⟨[(0,1)], by simp [Matching, K3], rfl⟩
  · apply matching_length_le_one
    unfold disjointEdges
    decide

end TLMC3322.Graphs
