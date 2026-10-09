import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# The literal containment minimum in conjecture 00000002187

The source explicitly asks for the minimum number of edges of a graph
containing a path; it imposes no coloring requirement. Containment below is
an injective Mathlib graph homomorphism, equivalently an isomorphism onto a
(not necessarily induced) subgraph. Hosts may have any vertex set, including
infinite ones, but their number of edges must be finite.
-/

namespace Conjecture2187

open SimpleGraph Filter Topology

/-- Containment as an ordinary subgraph: an injective adjacency-preserving map. -/
def Contains {V W : Type*} (H : SimpleGraph V) (G : SimpleGraph W) : Prop :=
  ∃ f : H →g G, Function.Injective f

/-- `m` occurs as the finite edge count of some graph containing `H`.
The predicate ranges over host graphs, rather than encoding an anticipated
value for the minimum. -/
def Attainable {V : Type} (H : SimpleGraph V) (m : ℕ) : Prop :=
  ∃ (W : Type) (G : SimpleGraph W),
    Finite G.edgeSet ∧ Contains H G ∧ Nat.card G.edgeSet = m

theorem attainable_self {V : Type} (H : SimpleGraph V) [Finite H.edgeSet] :
    Attainable H (Nat.card H.edgeSet) :=
  ⟨V, H, inferInstance, ⟨SimpleGraph.Hom.id, Function.injective_id⟩, rfl⟩

theorem attainable_nonempty {V : Type} (H : SimpleGraph V) [Finite H.edgeSet] :
    ∃ m, Attainable H m :=
  ⟨Nat.card H.edgeSet, attainable_self H⟩

/-- The least *attained* number of host edges. `Nat.find` uses the proved
existence of the host `H` itself. -/
noncomputable def minimumEdges {V : Type} (H : SimpleGraph V) [Finite H.edgeSet] : ℕ :=
  by
    classical
    exact Nat.find (attainable_nonempty H)

theorem minimumEdges_attained {V : Type} (H : SimpleGraph V) [Finite H.edgeSet] :
    Attainable H (minimumEdges H) :=
  by
    classical
    exact Nat.find_spec (attainable_nonempty H)

theorem minimumEdges_le {V : Type} (H : SimpleGraph V) [Finite H.edgeSet]
    {m : ℕ} (hm : Attainable H m) : minimumEdges H ≤ m :=
  by
    classical
    exact Nat.find_min' (attainable_nonempty H) hm

/-- A graph copy injects the source edge set into the host edge set. This
statement also covers hosts with infinitely many isolated vertices. -/
theorem edgeCount_le_of_contained {V W : Type*} (H : SimpleGraph V)
    (G : SimpleGraph W) [Finite G.edgeSet] (h : Contains H G) :
    Nat.card H.edgeSet ≤ Nat.card G.edgeSet := by
  obtain ⟨f, hf⟩ := h
  exact Nat.card_le_card_of_injective f.mapEdgeSet (SimpleGraph.Hom.mapEdgeSet.injective f hf)

theorem edgeCount_le_of_attainable {V : Type} (H : SimpleGraph V)
    {m : ℕ} (hm : Attainable H m) : Nat.card H.edgeSet ≤ m := by
  obtain ⟨W, G, hfin, hcopy, hcard⟩ := hm
  letI := hfin
  rw [← hcard]
  exact edgeCount_le_of_contained H G hcopy

/-- The containment-only minimum is exactly the edge count of the object
being contained. The upper bound uses `H` itself; the lower bound uses the
injection on unordered edges induced by every copy. -/
theorem minimumEdges_eq {V : Type} (H : SimpleGraph V) [Finite H.edgeSet] :
    minimumEdges H = Nat.card H.edgeSet := by
  exact Nat.le_antisymm (minimumEdges_le H (attainable_self H))
    (edgeCount_le_of_attainable H (minimumEdges_attained H))

/-- The consecutive unordered pairs enumerate exactly all edges of P_(n+1). -/
lemma pathGraph_card_succ (n : ℕ) [Fintype (pathGraph (n + 1)).edgeSet] :
    (pathGraph (n + 1)).edgeFinset.card = n := by
  classical
  let f : Fin n → Sym2 (Fin (n + 1)) := fun i => s(i.castSucc, i.succ)
  have hf : Function.Injective f := by
    intro i j hij
    simp only [f, Sym2.eq_iff] at hij
    rcases hij with ⟨h, _⟩ | ⟨h, h'⟩
    · exact Fin.castSucc_injective _ h
    · have h1 := congrArg Fin.val h
      have h2 := congrArg Fin.val h'
      simp only [Fin.coe_castSucc, Fin.val_succ] at h1 h2
      omega
  have he : (pathGraph (n + 1)).edgeFinset = Finset.univ.image f := by
    ext e
    induction e using Sym2.inductionOn with
    | _ u v =>
      simp only [mem_edgeFinset, mem_edgeSet, pathGraph_adj, Finset.mem_image,
        Finset.mem_univ, true_and]
      constructor
      · intro huv
        rcases huv with huv | huv
        · have hu : u.val < n := by have := v.isLt; omega
          refine ⟨⟨u.val, hu⟩, ?_⟩
          have hv : (⟨u.val, hu⟩ : Fin n).succ = v := by apply Fin.ext; exact huv
          have hh : (⟨u.val, hu⟩ : Fin n).castSucc = u := by apply Fin.ext; rfl
          simp only [f, hv, hh]
        · have hv : v.val < n := by have := u.isLt; omega
          refine ⟨⟨v.val, hv⟩, ?_⟩
          have hu : (⟨v.val, hv⟩ : Fin n).succ = u := by apply Fin.ext; exact huv
          have hh : (⟨v.val, hv⟩ : Fin n).castSucc = v := by apply Fin.ext; rfl
          simp only [f, hu, hh, Sym2.eq_swap]
      · rintro ⟨i, hi⟩
        simp only [f, Sym2.eq_iff] at hi
        rcases hi with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  rw [he, Finset.card_image_of_injective _ hf]
  simp

lemma pathGraph_card (n : ℕ) [Fintype (pathGraph n).edgeSet] :
    (pathGraph n).edgeFinset.card = n - 1 := by
  classical
  cases n with
  | zero =>
    have h : pathGraph 0 = ⊥ := by ext u v; exact Fin.elim0 u
    simp [h]
  | succ n => simpa using pathGraph_card_succ n


/-- The written definition of R̂(P_n), taking P_n to have n vertices. -/
noncomputable def pathMinimum (n : ℕ) : ℕ := minimumEdges (pathGraph n)

/-- The exact value under the definition printed in the conjecture. -/
theorem pathMinimum_eq (n : ℕ) : pathMinimum n = n - 1 := by
  classical
  rw [pathMinimum, minimumEdges_eq, Nat.card_eq_fintype_card,
    ← SimpleGraph.edgeFinset_card, pathGraph_card]

/-- Under the alternate convention in which P_n has n edges, the minimum is n. -/
theorem pathMinimum_succ (n : ℕ) : pathMinimum (n + 1) = n := by
  simp [pathMinimum_eq]

/-- The asymptotic quantitative statement in the conjecture, with little-o
spelled out: some real error tends to zero and the asserted formula holds
for all sufficiently large natural n. -/
def ClaimedAsymptotic : Prop :=
  ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
    ∀ᶠ n : ℕ in atTop, (pathMinimum n : ℝ) = (3 + ε n) * (n : ℝ)

/-- The actual normalized minimum tends to 1. -/
theorem pathMinimum_ratio_tendsto_one :
    Tendsto (fun n : ℕ => (pathMinimum n : ℝ) / (n : ℝ)) atTop (𝓝 1) := by
  have h : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have h' : Tendsto (fun n : ℕ => (1 : ℝ) - 1 / (n : ℝ)) atTop (𝓝 1) := by
    simpa using h.sub tendsto_one_div_atTop_nhds_zero_nat
  apply h'.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [pathMinimum_eq, Nat.cast_sub hn]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  push_cast
  field_simp

/-- In particular the normalized minimum cannot tend to 3. -/
theorem pathMinimum_ratio_not_tendsto_three :
    ¬ Tendsto (fun n : ℕ => (pathMinimum n : ℝ) / (n : ℝ)) atTop (𝓝 3) := by
  intro h
  have h13 : (1 : ℝ) = 3 := tendsto_nhds_unique pathMinimum_ratio_tendsto_one h
  norm_num at h13

/-- Complete negation of the original little-o quantitative claim. -/
theorem conjecture_false : ¬ ClaimedAsymptotic := by
  rintro ⟨ε, hε, hformula⟩
  apply pathMinimum_ratio_not_tendsto_three
  have h : Tendsto (fun n => (3 : ℝ) + ε n) atTop (𝓝 3) := by
    simpa using tendsto_const_nhds.add hε
  apply h.congr'
  filter_upwards [hformula, eventually_ge_atTop 1] with n hn hnpos
  rw [hn]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  field_simp

end Conjecture2187

