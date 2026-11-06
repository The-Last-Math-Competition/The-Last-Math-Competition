import Mathlib

set_option linter.unusedSectionVars false

/-!
# The matching polynomial

For a finite simple graph `G` on a vertex type `V` and a finite set of vertices `s`, a
*matching inside `s`* is a set `M` of edges of `G`, each with both end points in `s`, which are
pairwise vertex-disjoint.  The matching polynomial of the induced subgraph `G[s]` is

  `μ(G[s]; x) = ∑_{M} (-1)^{|M|} x^{|s| - 2|M|} = ∑_k (-1)^k m_k(G[s]) x^{|s| - 2k}`,

where `m_k` is the number of `k`-matchings.  The matching polynomial of `G` itself is the case
`s = univ`.

The main result of this file is the *leaf recurrence*: if `v ∈ s` has exactly one neighbour `u`
inside `s`, then `μ(G[s]) = x · μ(G[s ∖ v]) - μ(G[s ∖ {v, u}])`.
-/

open Polynomial Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- `M` is a matching of `G` inside the vertex set `s`: a set of edges of `G`, each having both
end points in `s`, pairwise vertex-disjoint. -/
def IsMatchingIn (s : Finset V) (M : Finset (Sym2 V)) : Prop :=
  M ⊆ G.edgeFinset ∧ (∀ e ∈ M, ∀ x, x ∈ e → x ∈ s) ∧
    ∀ e ∈ M, ∀ f ∈ M, e ≠ f → ∀ x, x ∈ e → x ∉ f

noncomputable instance (s : Finset V) : DecidablePred (G.IsMatchingIn s) :=
  Classical.decPred _

/-- The finite set of all matchings of `G` inside `s`. -/
noncomputable def matchings (s : Finset V) : Finset (Finset (Sym2 V)) :=
  G.edgeFinset.powerset.filter (G.IsMatchingIn s)

theorem mem_matchings {s : Finset V} {M : Finset (Sym2 V)} :
    M ∈ G.matchings s ↔ G.IsMatchingIn s M := by
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr h.1, h⟩

/-- The number of `k`-matchings of `G` inside `s`. -/
noncomputable def numMatchings (s : Finset V) (k : ℕ) : ℕ :=
  ((G.matchings s).filter (fun M => M.card = k)).card

variable (R : Type*) [CommRing R]

/-- The matching polynomial of the induced subgraph `G[s]`, as a sum over matchings. -/
noncomputable def matchingPolyIn (s : Finset V) : R[X] :=
  ∑ M ∈ G.matchings s, (-1 : R[X]) ^ M.card * X ^ (s.card - 2 * M.card)

/-- The matching polynomial `μ(G; x) = ∑_k (-1)^k m_k(G) x^{n - 2k}` of the finite graph `G`. -/
noncomputable def matchingPolynomial : R[X] := G.matchingPolyIn R Finset.univ

/-! ### Basic facts about matchings -/

variable {G}

theorem IsMatchingIn.mono {s t : Finset V} {M : Finset (Sym2 V)} (hst : s ⊆ t)
    (hM : G.IsMatchingIn s M) : G.IsMatchingIn t M :=
  ⟨hM.1, fun e he x hx => hst (hM.2.1 e he x hx), hM.2.2⟩

theorem IsMatchingIn.not_isDiag {s : Finset V} {M : Finset (Sym2 V)} (hM : G.IsMatchingIn s M)
    {e : Sym2 V} (he : e ∈ M) : ¬ e.IsDiag :=
  SimpleGraph.not_isDiag_of_mem_edgeSet G (G.mem_edgeFinset.mp (hM.1 he))

/-- A matching inside `s` covers `2|M|` vertices of `s`, hence `2|M| ≤ |s|`. -/
theorem IsMatchingIn.two_mul_card_le {s : Finset V} {M : Finset (Sym2 V)}
    (hM : G.IsMatchingIn s M) : 2 * M.card ≤ s.card := by
  classical
  obtain ⟨hsub, hcov, hdis⟩ := hM
  have hdisj : (M : Set (Sym2 V)).PairwiseDisjoint (fun e : Sym2 V => e.toFinset) := by
    intro e he f hf hef
    rw [Function.onFun, Finset.disjoint_left]
    intro x hxe hxf
    exact hdis e he f hf hef x (Sym2.mem_toFinset.mp hxe) (Sym2.mem_toFinset.mp hxf)
  have hcard : (M.biUnion fun e => e.toFinset).card = 2 * M.card := by
    rw [Finset.card_biUnion hdisj]
    have h2 : ∀ e ∈ M, e.toFinset.card = 2 := fun e he =>
      Sym2.card_toFinset_of_not_isDiag e
        (SimpleGraph.not_isDiag_of_mem_edgeSet G (G.mem_edgeFinset.mp (hsub he)))
    rw [Finset.sum_congr rfl h2, Finset.sum_const, smul_eq_mul, mul_comm]
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  obtain ⟨e, he, hxe⟩ := Finset.mem_biUnion.mp hx
  exact hcov e he x (Sym2.mem_toFinset.mp hxe)

theorem IsMatchingIn.card_le {s : Finset V} {M : Finset (Sym2 V)}
    (hM : G.IsMatchingIn s M) : M.card ≤ s.card := by
  have := hM.two_mul_card_le
  omega

/-- The matching polynomial in the classical form `∑_k (-1)^k m_k x^{n-2k}`. -/
theorem matchingPolyIn_eq_sum_numMatchings (s : Finset V) :
    G.matchingPolyIn R s =
      ∑ k ∈ Finset.range (s.card + 1),
        (-1 : R[X]) ^ k * (G.numMatchings s k : R[X]) * X ^ (s.card - 2 * k) := by
  classical
  unfold matchingPolyIn numMatchings
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun M : Finset (Sym2 V) => M.card)
    (t := Finset.range (s.card + 1))]
  · apply Finset.sum_congr rfl
    intro k _
    rw [Finset.sum_congr rfl (g := fun _ => (-1 : R[X]) ^ k * X ^ (s.card - 2 * k))]
    · rw [Finset.sum_const, nsmul_eq_mul]
      ring
    · intro M hM
      rw [(Finset.mem_filter.mp hM).2]
  · intro M hM
    rw [Finset.mem_range, Nat.lt_succ_iff]
    exact ((G.mem_matchings).mp hM).card_le

theorem matchingPolynomial_eq_sum_numMatchings :
    G.matchingPolynomial R =
      ∑ k ∈ Finset.range (Fintype.card V + 1),
        (-1 : R[X]) ^ k * (G.numMatchings Finset.univ k : R[X]) * X ^ (Fintype.card V - 2 * k) := by
  rw [matchingPolynomial, matchingPolyIn_eq_sum_numMatchings, Finset.card_univ]

/-! ### The edgeless case -/

/-- If `G` has no edge inside `s`, the only matching inside `s` is the empty one. -/
theorem matchings_eq_singleton_empty (s : Finset V) (h : ∀ a ∈ s, ∀ b ∈ s, ¬ G.Adj a b) :
    G.matchings s = {∅} := by
  ext M
  rw [G.mem_matchings, Finset.mem_singleton]
  constructor
  · intro hM
    rw [Finset.eq_empty_iff_forall_notMem]
    intro e he
    induction e with
    | h a b =>
      have hab : G.Adj a b := G.mem_edgeSet.mp (G.mem_edgeFinset.mp (hM.1 he))
      exact h a (hM.2.1 _ he a (Sym2.mem_mk_left a b)) b (hM.2.1 _ he b (Sym2.mem_mk_right a b)) hab
  · rintro rfl
    exact ⟨Finset.empty_subset _, fun e he => absurd he (Finset.notMem_empty e),
      fun e he => absurd he (Finset.notMem_empty e)⟩

theorem matchingPolyIn_of_no_edge (s : Finset V) (h : ∀ a ∈ s, ∀ b ∈ s, ¬ G.Adj a b) :
    G.matchingPolyIn R s = X ^ s.card := by
  rw [matchingPolyIn, G.matchings_eq_singleton_empty s h, Finset.sum_singleton]
  simp

/-! ### The leaf recurrence -/

section Leaf

variable {s : Finset V} {v u : V}

/-- Matchings inside `s ∖ v` are matchings inside `s` not using any edge at `v`. -/
theorem isMatchingIn_erase_iff (hv : v ∈ s) (hleaf : ∀ w ∈ s, G.Adj v w → w = u)
    (M : Finset (Sym2 V)) :
    G.IsMatchingIn (s.erase v) M ↔ G.IsMatchingIn s M ∧ s(v, u) ∉ M := by
  constructor
  · intro hM
    refine ⟨hM.mono (Finset.erase_subset v s), fun hvu => ?_⟩
    have := hM.2.1 _ hvu v (Sym2.mem_mk_left v u)
    exact (Finset.mem_erase.mp this).1 rfl
  · rintro ⟨hM, hvu⟩
    refine ⟨hM.1, ?_, hM.2.2⟩
    intro e he x hx
    rw [Finset.mem_erase]
    refine ⟨?_, hM.2.1 e he x hx⟩
    rintro rfl
    -- `e = s(x, w)` with `w` a neighbour of `x = v` inside `s`, so `w = u`.
    have hspec := Sym2.other_spec hx
    have hadj : G.Adj x (Sym2.Mem.other hx) := by
      rw [← G.mem_edgeSet, hspec]
      exact G.mem_edgeFinset.mp (hM.1 he)
    have hw : Sym2.Mem.other hx ∈ s := hM.2.1 e he _ (Sym2.other_mem hx)
    have := hleaf _ hw hadj
    rw [this] at hspec
    rw [hspec] at hvu
    exact hvu he

/-- Adding the pendant edge `s(v, u)` to a matching inside `s ∖ {v, u}` gives a matching
inside `s`. -/
theorem isMatchingIn_insert (hv : v ∈ s) (hu : u ∈ s) (hadj : G.Adj v u)
    {M : Finset (Sym2 V)} (hM : G.IsMatchingIn ((s.erase v).erase u) M) :
    G.IsMatchingIn s (insert s(v, u) M) := by
  have hnot : ∀ x, x ∈ s(v, u) → ∀ f ∈ M, x ∉ f := by
    intro x hx f hf hxf
    have := hM.2.1 f hf x hxf
    rw [Finset.mem_erase, Finset.mem_erase] at this
    rcases Sym2.mem_iff.mp hx with rfl | rfl
    · exact this.2.1 rfl
    · exact this.1 rfl
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    rcases Finset.mem_insert.mp he with rfl | he
    · exact G.mem_edgeFinset.mpr (G.mem_edgeSet.mpr hadj)
    · exact hM.1 he
  · intro e he x hx
    rcases Finset.mem_insert.mp he with rfl | he
    · rcases Sym2.mem_iff.mp hx with rfl | rfl
      · exact hv
      · exact hu
    · have := hM.2.1 e he x hx
      exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase this)
  · intro e he f hf hef x hxe hxf
    rcases Finset.mem_insert.mp he with rfl | he
    · rcases Finset.mem_insert.mp hf with rfl | hf
      · exact hef rfl
      · exact hnot x hxe f hf hxf
    · rcases Finset.mem_insert.mp hf with rfl | hf
      · exact hnot x hxf e he hxe
      · exact hM.2.2 e he f hf hef x hxe hxf

/-- Removing the pendant edge from a matching inside `s` containing it gives a matching inside
`s ∖ {v, u}`. -/
theorem isMatchingIn_erase_of_mem {M : Finset (Sym2 V)} (hM : G.IsMatchingIn s M)
    (hvu : s(v, u) ∈ M) : G.IsMatchingIn ((s.erase v).erase u) (M.erase s(v, u)) := by
  refine ⟨(Finset.erase_subset _ _).trans hM.1, ?_, ?_⟩
  · intro e he x hx
    have he' := Finset.mem_erase.mp he
    have hxs := hM.2.1 e he'.2 x hx
    have hx' : x ∉ s(v, u) := hM.2.2 e he'.2 _ hvu he'.1 x hx
    rw [Sym2.mem_iff] at hx'
    push Not at hx'
    exact Finset.mem_erase.mpr ⟨hx'.2, Finset.mem_erase.mpr ⟨hx'.1, hxs⟩⟩
  · intro e he f hf hef x hxe hxf
    exact hM.2.2 e (Finset.mem_of_mem_erase he) f (Finset.mem_of_mem_erase hf) hef x hxe hxf

theorem pendant_notMem {M : Finset (Sym2 V)} (hM : G.IsMatchingIn ((s.erase v).erase u) M) :
    s(v, u) ∉ M := by
  intro h
  have := hM.2.1 _ h v (Sym2.mem_mk_left v u)
  exact (Finset.mem_erase.mp (Finset.mem_of_mem_erase this)).1 rfl

/-- The decomposition of the matchings inside `s` according to the pendant edge. -/
theorem matchings_eq_union (hv : v ∈ s) (hu : u ∈ s) (hadj : G.Adj v u)
    (hleaf : ∀ w ∈ s, G.Adj v w → w = u) :
    G.matchings s = G.matchings (s.erase v) ∪
      (G.matchings ((s.erase v).erase u)).image (insert s(v, u)) := by
  ext M
  rw [Finset.mem_union, Finset.mem_image, G.mem_matchings, G.mem_matchings,
    G.isMatchingIn_erase_iff hv hleaf]
  constructor
  · intro hM
    by_cases hvu : s(v, u) ∈ M
    · right
      exact ⟨M.erase s(v, u), (G.mem_matchings).mpr (G.isMatchingIn_erase_of_mem hM hvu),
        Finset.insert_erase hvu⟩
    · left
      exact ⟨hM, hvu⟩
  · rintro (⟨hM, -⟩ | ⟨M', hM', rfl⟩)
    · exact hM
    · exact G.isMatchingIn_insert hv hu hadj ((G.mem_matchings).mp hM')

theorem disjoint_matchings_image (hv : v ∈ s) (hleaf : ∀ w ∈ s, G.Adj v w → w = u) :
    Disjoint (G.matchings (s.erase v))
      ((G.matchings ((s.erase v).erase u)).image (insert s(v, u))) := by
  rw [Finset.disjoint_left]
  intro M hM hM'
  obtain ⟨M', -, rfl⟩ := Finset.mem_image.mp hM'
  have := ((G.isMatchingIn_erase_iff hv hleaf _).mp ((G.mem_matchings).mp hM)).2
  exact this (Finset.mem_insert_self _ _)

/-- **Leaf recurrence** for the matching polynomial: if `v ∈ s` is adjacent to `u ∈ s` and to no
other vertex of `s`, then `μ(G[s]) = x · μ(G[s ∖ v]) - μ(G[s ∖ {v, u}])`. -/
theorem matchingPolyIn_leaf (hv : v ∈ s) (hu : u ∈ s) (hvu : v ≠ u) (hadj : G.Adj v u)
    (hleaf : ∀ w ∈ s, G.Adj v w → w = u) :
    G.matchingPolyIn R s =
      X * G.matchingPolyIn R (s.erase v) - G.matchingPolyIn R ((s.erase v).erase u) := by
  classical
  have hu' : u ∈ s.erase v := Finset.mem_erase.mpr ⟨hvu.symm, hu⟩
  have hc1 : s.card = (s.erase v).card + 1 := (Finset.card_erase_add_one hv).symm
  have hc2 : (s.erase v).card = ((s.erase v).erase u).card + 1 :=
    (Finset.card_erase_add_one hu').symm
  unfold matchingPolyIn
  rw [G.matchings_eq_union hv hu hadj hleaf,
    Finset.sum_union (G.disjoint_matchings_image hv hleaf), Finset.sum_image, sub_eq_add_neg,
    Finset.mul_sum, ← Finset.sum_neg_distrib]
  · congr 1
    · apply Finset.sum_congr rfl
      intro M hM
      have hle := ((G.mem_matchings).mp hM).two_mul_card_le
      rw [hc1, show (s.erase v).card + 1 - 2 * M.card = ((s.erase v).card - 2 * M.card) + 1 by
        omega, pow_succ]
      ring
    · apply Finset.sum_congr rfl
      intro M hM
      have hnot := G.pendant_notMem ((G.mem_matchings).mp hM)
      rw [Finset.card_insert_of_notMem hnot, hc1, hc2,
        show ((s.erase v).erase u).card + 1 + 1 - 2 * (M.card + 1) =
          ((s.erase v).erase u).card - 2 * M.card by omega, pow_succ]
      ring
  · intro M hM M' hM' h
    have h1 := G.pendant_notMem ((G.mem_matchings).mp hM)
    have h2 := G.pendant_notMem ((G.mem_matchings).mp hM')
    rw [← Finset.erase_insert h1, ← Finset.erase_insert h2, h]

end Leaf

end SimpleGraph
