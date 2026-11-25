/-
  Conjecture 00000003970 — Reading III: Isomorphism-Class Connected Subgraph Counts
  Complete Universal Proof (Whitney–Lovász Connected Subgraph Algebra)
  Pure Core Lean 4.19.0 (zero external dependencies).

  Main Result: For ANY finite simple graphs `G₁` and `G₂` (connected or disconnected,
  of ANY vertex orders `n₁, n₂`), if their isomorphism-class counts of all connected
  subgraphs coincide — either in the induced sense `indIsoCount H G₁ = indIsoCount H G₂`
  or in the non-induced sense `subIsoCount H G₁ = subIsoCount H G₂` for every connected
  simple graph `H` — then `G₁ ≅ G₂` (`GraphIso G₁ G₂`), `n₁ = n₂`, and their characteristic
  polynomials `charPoly G₁ = charPoly G₂` (hence adjacency spectra) are IDENTICAL.
  Consequently, subgraph-count vs. adjacency-spectrum separation is IMPOSSIBLE at every `n`.
-/

import Conjecture00000003970.SubgraphCounts

namespace Conjecture00000003970

/-! ### Homomorphism, Embedding, and Isomorphism-Class Subgraph Counts -/

/-- Boolean injectivity test for `φ : Fin k → Fin n`. -/
def isInjBool {k n : Nat} (φ : Fin k → Fin n) : Bool :=
  (allFin k).all (fun i => (allFin k).all (fun j => !(φ i == φ j) || (i == j)))

theorem isInjBool_eq_true_iff {k n : Nat} (φ : Fin k → Fin n) :
    isInjBool φ = true ↔ (∀ i j : Fin k, φ i = φ j → i = j) := by
  unfold isInjBool
  constructor
  · intro h i j hij
    have h1 := List.all_eq_true.mp h i (mem_allFin i)
    have h2 := List.all_eq_true.mp h1 j (mem_allFin j)
    have hbeq : (φ i == φ j) = true := by simpa using decide_eq_true hij
    simp only [hbeq, Bool.not_true, Bool.false_or] at h2
    exact of_decide_eq_true (by simpa using h2)
  · intro hinj
    apply List.all_eq_true.mpr; intro i _
    apply List.all_eq_true.mpr; intro j _
    by_cases hij : φ i = φ j
    · have := hinj i j hij
      subst this; simp
    · have hbeq : (φ i == φ j) = false :=
        Bool.eq_false_iff.mpr (fun h => hij (of_decide_eq_true (by simpa using h)))
      simp [hbeq]

/-- Image indicator subset of `φ : Fin k → Fin n`. -/
def imageMask {k n : Nat} (φ : Fin k → Fin n) (y : Fin n) : Bool :=
  (allFin k).any (fun i => φ i == y)

theorem imageMask_eq_true_iff {k n : Nat} (φ : Fin k → Fin n) (y : Fin n) :
    imageMask φ y = true ↔ ∃ i : Fin k, φ i = y := by
  unfold imageMask
  constructor
  · intro h
    rcases List.any_eq_true.mp h with ⟨i, _, hi⟩
    exact ⟨i, of_decide_eq_true (by simpa using hi)⟩
  · rintro ⟨i, rfl⟩
    exact List.any_eq_true.mpr ⟨i, mem_allFin i, by simp⟩

/-- Boolean graph homomorphism test `H → G`. -/
def isHomBool {k n : Nat} (H : SimpleGraphN k) (G : SimpleGraphN n)
    (φ : Fin k → Fin n) : Bool :=
  (allFin k).all (fun u => (allFin k).all (fun v => !H.adj u v || G.adj (φ u) (φ v)))

theorem isHomBool_eq_true_iff {k n : Nat} (H : SimpleGraphN k) (G : SimpleGraphN n)
    (φ : Fin k → Fin n) :
    isHomBool H G φ = true ↔ (∀ u v : Fin k, H.adj u v = true → G.adj (φ u) (φ v) = true) := by
  unfold isHomBool
  constructor
  · intro h u v huv
    have h1 := List.all_eq_true.mp h u (mem_allFin u)
    have h2 := List.all_eq_true.mp h1 v (mem_allFin v)
    simp only [huv, Bool.not_true, Bool.false_or] at h2
    exact h2
  · intro h
    apply List.all_eq_true.mpr; intro u _
    apply List.all_eq_true.mpr; intro v _
    cases huv : H.adj u v
    · simp
    · simp [h u v huv]

/-- Boolean induced-embedding test `H ↪_ind G`. -/
def isIndEmbBool {k n : Nat} (H : SimpleGraphN k) (G : SimpleGraphN n)
    (φ : Fin k → Fin n) : Bool :=
  (allFin k).all (fun u => (allFin k).all (fun v => H.adj u v == G.adj (φ u) (φ v)))

theorem isIndEmbBool_eq_true_iff {k n : Nat} (H : SimpleGraphN k) (G : SimpleGraphN n)
    (φ : Fin k → Fin n) :
    isIndEmbBool H G φ = true ↔ (∀ u v : Fin k, H.adj u v = G.adj (φ u) (φ v)) := by
  unfold isIndEmbBool
  constructor
  · intro h u v
    have h1 := List.all_eq_true.mp h u (mem_allFin u)
    have h2 := List.all_eq_true.mp h1 v (mem_allFin v)
    exact eq_of_beq h2
  · intro h
    apply List.all_eq_true.mpr; intro u _
    apply List.all_eq_true.mpr; intro v _
    rw [h u v]; simp

/-- Test whether the induced subgraph `G[S]` is isomorphic to `H : SimpleGraphN k`. -/
def indIsoOnSubsetBool {k n : Nat} (H : SimpleGraphN k) (G : SimpleGraphN n)
    (S : Fin n → Bool) : Bool :=
  (allFinMaps k n).any (fun φ => isInjBool φ && (imageMask φ == S) && isIndEmbBool H G φ)

/-- Number of induced subgraphs `G[S]` (`S ⊆ V(G)`) isomorphic to `H`. -/
def indIsoCount {k n : Nat} (H : SimpleGraphN k) (G : SimpleGraphN n) : Nat :=
  countWhere (allSubsets n) (indIsoOnSubsetBool H G)

/-- Number of general (not-necessarily-induced) subgraphs `(S, F)` of `G` isomorphic to `H`. -/
def subIsoCount {k n : Nat} (H : SimpleGraphN k) (G : SimpleGraphN n) : Nat :=
  countWhere (listProd (allSubsets n) (allSimpleGraphs n))
    (fun p => isSpanningSubgraphOn G p.1 p.2 && indIsoOnSubsetBool H p.2 p.1)

/-- Number of graph homomorphisms `H → G`. -/
def homCount {k n : Nat} (H : SimpleGraphN k) (G : SimpleGraphN n) : Nat :=
  countWhere (allFinMaps k n) (isHomBool H G)

/-- Number of injective graph homomorphisms `H ↪ G`. -/
def injHomCount {k n : Nat} (H : SimpleGraphN k) (G : SimpleGraphN n) : Nat :=
  countWhere (allFinMaps k n) (fun φ => isInjBool φ && isHomBool H G φ)

/-- Number of induced embeddings `H ↪_ind G`. -/
def indEmbCount {k n : Nat} (H : SimpleGraphN k) (G : SimpleGraphN n) : Nat :=
  countWhere (allFinMaps k n) (fun φ => isInjBool φ && isIndEmbBool H G φ)

/-- Automorphism group order `|Aut(H)|`. -/
def autCount {k : Nat} (H : SimpleGraphN k) : Nat :=
  indEmbCount H H

/-! ### Step 1: `|Aut(H)| ≥ 1`, `|Aut(H)| * indIsoCount = indEmbCount`,
    and `|Aut(H)| * subIsoCount = injHomCount` -/

theorem countWhere_pos_of_witness {α : Type u} {L : List α} {P : α → Bool}
    {x₀ : α} (hx₀ : x₀ ∈ L) (hP₀ : P x₀ = true) : 0 < countWhere L P := by
  unfold countWhere
  induction L with
  | nil => cases hx₀
  | cons x xs ih =>
    rcases List.mem_cons.mp hx₀ with rfl | hxs
    · simp [List.filter, hP₀]
    · have := ih hxs
      unfold List.filter
      split
      · simp only [List.length]; omega
      · exact this

theorem autCount_pos {k : Nat} (H : SimpleGraphN k) : 0 < autCount H := by
  refine countWhere_pos_of_witness (x₀ := id) (mem_allFinMaps id) ?_
  simp only [Bool.and_eq_true]
  exact ⟨(isInjBool_eq_true_iff id).mpr (fun _ _ h => h),
         (isIndEmbBool_eq_true_iff H H id).mpr (fun _ _ => rfl)⟩

/-- Given `φ₀, φ : Fin k → Fin n`, pull `φ i` back along `φ₀` using `i` as unreachable fallback. -/
def pullbackPerm {k n : Nat} (φ₀ φ : Fin k → Fin n) (i : Fin k) : Fin k :=
  match (allFin k).find? (fun j => φ₀ j == φ i) with
  | some j => j
  | none => i

theorem pullbackPerm_spec {k n : Nat} {φ₀ φ : Fin k → Fin n}
    (hmem : ∀ i : Fin k, imageMask φ₀ (φ i) = true) (i : Fin k) :
    φ₀ (pullbackPerm φ₀ φ i) = φ i := by
  unfold pullbackPerm
  have hex : (allFin k).any (fun j => φ₀ j == φ i) = true := hmem i
  cases hfind : (allFin k).find? (fun j => φ₀ j == φ i) with
  | some j =>
    have hj := List.find?_some hfind
    exact of_decide_eq_true (by simpa using hj)
  | none =>
    have hnone := List.find?_eq_none.mp hfind
    rcases List.any_eq_true.mp hex with ⟨j, hjmem, hj⟩
    exact False.elim (by simpa [hj] using hnone j hjmem)

theorem autCount_mul_indIsoCount {k n : Nat} (H : SimpleGraphN k) (G : SimpleGraphN n) :
    autCount H * indIsoCount H G = indEmbCount H G := by
  symm
  unfold indEmbCount indIsoCount autCount
  refine countWhere_uniform_fiber (nodup_allSubsets n) imageMask (indEmbCount H H) ?_ ?_
  · intro φ _ hφ
    simp only [Bool.and_eq_true] at hφ
    refine ⟨mem_allSubsets _, ?_⟩
    unfold indIsoOnSubsetBool
    apply List.any_eq_true.mpr
    refine ⟨φ, mem_allFinMaps φ, ?_⟩
    simp [hφ.1, hφ.2]
  · intro S _ hS
    unfold indIsoOnSubsetBool at hS
    rcases List.any_eq_true.mp hS with ⟨φ₀, _, hφ₀⟩
    simp only [Bool.and_eq_true] at hφ₀
    have hinj₀ := (isInjBool_eq_true_iff φ₀).mp hφ₀.1.1
    have himg₀ : imageMask φ₀ = S := of_decide_eq_true (by simpa using hφ₀.1.2)
    have hemb₀ := (isIndEmbBool_eq_true_iff H G φ₀).mp hφ₀.2
    unfold indEmbCount
    refine countWhere_bij
      (fun φ => pullbackPerm φ₀ φ)
      (fun α i => φ₀ (α i))
      (nodup_allFinMaps k n) (nodup_allFinMaps k k) ?_ ?_
    · intro φ _ hφ
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hφ
      have hinj := (isInjBool_eq_true_iff φ).mp hφ.1.1
      have himg : imageMask φ = imageMask φ₀ := hφ.2.trans himg₀.symm
      have hemb := (isIndEmbBool_eq_true_iff H G φ).mp hφ.1.2
      have hspec : ∀ i, φ₀ (pullbackPerm φ₀ φ i) = φ i :=
        pullbackPerm_spec (fun i => by
          rw [← himg]
          exact (imageMask_eq_true_iff φ (φ i)).mpr ⟨i, rfl⟩)
      refine ⟨mem_allFinMaps _, ?_, ?_⟩
      · simp only [Bool.and_eq_true]
        refine ⟨(isInjBool_eq_true_iff _).mpr ?_, (isIndEmbBool_eq_true_iff H H _).mpr ?_⟩
        · intro i j hij
          apply hinj
          rw [← hspec i, ← hspec j, hij]
        · intro u v
          rw [hemb u v, ← hspec u, ← hspec v, ← hemb₀]
      · funext i; exact hspec i
    · intro α _ hα
      simp only [Bool.and_eq_true] at hα
      have hinjα := (isInjBool_eq_true_iff α).mp hα.1
      have hembα := (isIndEmbBool_eq_true_iff H H α).mp hα.2
      -- Note α is injective Fin k → Fin k, hence surjective on Fin k!
      have hsurjα : ∀ j : Fin k, ∃ i : Fin k, α i = j := by
        intro j
        by_cases hmem : imageMask α j = true
        · exact (imageMask_eq_true_iff α j).mp hmem
        · exfalso
          have hmemF : imageMask α j = false := Bool.eq_false_iff.mpr hmem
          -- Count imageMask α: since α is injective, `(allFin k).map α` has length k and Nodup!
          have hnd : Nodup ((allFin k).map α) :=
            nodup_map_of_inj_on (nodup_allFin k) (fun a _ b _ h => hinjα a b h)
          have hsub : ∀ z ∈ (allFin k).map α, z ∈ removeOne j (allFin k) := by
            intro z hz
            rcases List.mem_map.mp hz with ⟨i, _, rfl⟩
            refine mem_removeOne_of_ne ?_ (mem_allFin (α i))
            intro heq
            have : imageMask α j = true := (imageMask_eq_true_iff α j).mpr ⟨i, heq⟩
            rw [hmemF] at this; cases this
          have hle := nodup_length_le_of_subset hnd hsub
          have hrem := length_removeOne_of_mem (mem_allFin j)
          rw [List.length_map, length_allFin] at hle
          rw [length_allFin] at hrem
          omega
      refine ⟨mem_allFinMaps _, ?_, ?_⟩
      · simp only [Bool.and_eq_true, decide_eq_true_eq]
        refine ⟨⟨(isInjBool_eq_true_iff _).mpr ?_, (isIndEmbBool_eq_true_iff H G _).mpr ?_⟩, ?_⟩
        · intro i j hij; exact hinjα i j (hinj₀ _ _ hij)
        · intro u v; rw [← hemb₀ (α u) (α v), ← hembα u v]
        · rw [← himg₀]
          funext y
          by_cases hy : imageMask φ₀ y = true
          · rcases (imageMask_eq_true_iff φ₀ y).mp hy with ⟨j, rfl⟩
            rcases hsurjα j with ⟨i, rfl⟩
            have lhs : imageMask (fun x => φ₀ (α x)) (φ₀ (α i)) = true :=
              (imageMask_eq_true_iff _ _).mpr ⟨i, rfl⟩
            rw [lhs, hy]
          · have hyF : imageMask φ₀ y = false := Bool.eq_false_iff.mpr hy
            have lhsF : imageMask (fun x => φ₀ (α x)) y = false := by
              apply Bool.eq_false_iff.mpr; intro h
              rcases (imageMask_eq_true_iff _ y).mp h with ⟨i, rfl⟩
              exact hy ((imageMask_eq_true_iff φ₀ _).mpr ⟨α i, rfl⟩)
            rw [lhsF, hyF]
      · funext i
        apply hinj₀
        exact pullbackPerm_spec (fun x => (imageMask_eq_true_iff φ₀ _).mpr ⟨α x, rfl⟩) i

/-- Pushforward the edges of `H : SimpleGraphN k` along `φ : Fin k → Fin n`. -/
def pushSubgraph {k n : Nat} (H : SimpleGraphN k) (φ : Fin k → Fin n) : SimpleGraphN n where
  adj y₁ y₂ :=
    if y₁ = y₂ then false
    else (allFin k).any (fun u => (allFin k).any (fun v => (φ u == y₁) && (φ v == y₂) && H.adj u v))
  loopless y := by simp
  symm y₁ y₂ := by
    by_cases hy : y₁ = y₂
    · subst hy; simp
    · have hy' : y₂ ≠ y₁ := fun h => hy h.symm
      simp only [hy, hy', ↓reduceIte]
      by_cases h1 : ((allFin k).any fun u => (allFin k).any fun v => (φ u == y₁) && (φ v == y₂) && H.adj u v) = true
      · rcases List.any_eq_true.mp h1 with ⟨u, _, hu⟩
        rcases List.any_eq_true.mp hu with ⟨v, _, hv⟩
        simp only [Bool.and_eq_true] at hv
        have h2 : ((allFin k).any fun a => (allFin k).any fun b => (φ a == y₂) && (φ b == y₁) && H.adj a b) = true := by
          refine List.any_eq_true.mpr ⟨v, mem_allFin v, List.any_eq_true.mpr ⟨u, mem_allFin u, ?_⟩⟩
          rw [H.symm v u]
          simp [hv.1.1, hv.1.2, hv.2]
        rw [h1, h2]
      · have h1F := Bool.eq_false_iff.mpr h1
        have h2F : ((allFin k).any fun a => (allFin k).any fun b => (φ a == y₂) && (φ b == y₁) && H.adj a b) = false := by
          apply Bool.eq_false_iff.mpr; intro h2
          rcases List.any_eq_true.mp h2 with ⟨v, _, hv⟩
          rcases List.any_eq_true.mp hv with ⟨u, _, hu⟩
          simp only [Bool.and_eq_true] at hu
          apply h1
          refine List.any_eq_true.mpr ⟨u, mem_allFin u, List.any_eq_true.mpr ⟨v, mem_allFin v, ?_⟩⟩
          rw [H.symm u v]
          simp [hu.1.1, hu.1.2, hu.2]
        rw [h1F, h2F]

theorem pushSubgraph_adj_of_inj {k n : Nat} (H : SimpleGraphN k) {φ : Fin k → Fin n}
    (hinj : ∀ i j, φ i = φ j → i = j) (u v : Fin k) :
    (pushSubgraph H φ).adj (φ u) (φ v) = H.adj u v := by
  unfold pushSubgraph; dsimp only
  by_cases huv : φ u = φ v
  · have := hinj u v huv
    subst this
    simp [H.loopless]
  · simp only [huv, ↓reduceIte]
    cases hH : H.adj u v
    · apply Bool.eq_false_iff.mpr; intro hany
      rcases List.any_eq_true.mp hany with ⟨a, _, ha⟩
      rcases List.any_eq_true.mp ha with ⟨b, _, hb⟩
      simp only [Bool.and_eq_true] at hb
      have hau : a = u := hinj a u (of_decide_eq_true (by simpa using hb.1.1))
      have hbv : b = v := hinj b v (of_decide_eq_true (by simpa using hb.1.2))
      subst hau; subst hbv
      rw [hH] at hb; cases hb.2
    · refine List.any_eq_true.mpr ⟨u, mem_allFin u, List.any_eq_true.mpr ⟨v, mem_allFin v, ?_⟩⟩
      simp [hH]

theorem autCount_mul_subIsoCount {k n : Nat} (H : SimpleGraphN k) (G : SimpleGraphN n) :
    autCount H * subIsoCount H G = injHomCount H G := by
  symm
  unfold injHomCount subIsoCount autCount
  refine countWhere_uniform_fiber
    (nodup_listProd (nodup_allSubsets n) (nodup_allSimpleGraphs n))
    (fun φ => (imageMask φ, pushSubgraph H φ))
    (indEmbCount H H) ?_ ?_
  · intro φ _ hφ
    simp only [Bool.and_eq_true] at hφ
    have hinj := (isInjBool_eq_true_iff φ).mp hφ.1
    have hhom := (isHomBool_eq_true_iff H G φ).mp hφ.2
    refine ⟨mem_listProd.mpr ⟨mem_allSubsets _, mem_allSimpleGraphs _⟩, ?_⟩
    simp only [Bool.and_eq_true]
    constructor
    · rw [isSpanningSubgraphOn_eq_true_iff]
      intro y₁ y₂ hy
      unfold pushSubgraph at hy; dsimp only at hy
      by_cases hyy : y₁ = y₂
      · simp [hyy] at hy
      · simp only [hyy, ↓reduceIte] at hy
        rcases List.any_eq_true.mp hy with ⟨u, _, hu⟩
        rcases List.any_eq_true.mp hu with ⟨v, _, hv⟩
        simp only [Bool.and_eq_true] at hv
        have hu' : φ u = y₁ := of_decide_eq_true (by simpa using hv.1.1)
        have hv' : φ v = y₂ := of_decide_eq_true (by simpa using hv.1.2)
        subst hu'; subst hv'
        exact ⟨(imageMask_eq_true_iff φ _).mpr ⟨u, rfl⟩,
               (imageMask_eq_true_iff φ _).mpr ⟨v, rfl⟩,
               hhom u v hv.2⟩
    · unfold indIsoOnSubsetBool
      refine List.any_eq_true.mpr ⟨φ, mem_allFinMaps φ, ?_⟩
      simp only [hφ.1, beq_self_eq_true, Bool.and_self, Bool.true_and]
      exact (isIndEmbBool_eq_true_iff H _ φ).mpr fun u v =>
        (pushSubgraph_adj_of_inj H hinj u v).symm
  · rintro ⟨S, F⟩ _ hSF
    simp only [Bool.and_eq_true] at hSF
    have hspan := (isSpanningSubgraphOn_eq_true_iff G S F).mp hSF.1
    -- Notice: for ANY φ with `isInjBool φ`, `(imageMask φ, pushSubgraph H φ) = (S, F)`
    -- holds IFF `imageMask φ = S ∧ isIndEmbBool H F φ = true` (which ALSO implies `isHomBool H G φ = true`!)!
    have hfiber_eq :
        countWhere (allFinMaps k n)
          (fun φ => (isInjBool φ && isHomBool H G φ) &&
            decide ((imageMask φ, pushSubgraph H φ) = (S, F))) =
        countWhere (allFinMaps k n)
          (fun φ => (isInjBool φ && isIndEmbBool H F φ) && decide (imageMask φ = S)) := by
      unfold countWhere
      congr 1
      refine List.filter_congr ?_
      intro φ _
      by_cases hinjb : isInjBool φ = true
      · have hinj := (isInjBool_eq_true_iff φ).mp hinjb
        by_cases himgb : imageMask φ = S
        · subst himgb
          -- Show `(isHomBool H G φ = true ∧ pushSubgraph H φ = F) ↔ isIndEmbBool H F φ = true`
          have hiff : (isHomBool H G φ = true ∧ pushSubgraph H φ = F) ↔
              isIndEmbBool H F φ = true := by
            constructor
            · rintro ⟨_, rfl⟩
              exact (isIndEmbBool_eq_true_iff H _ φ).mpr fun u v =>
                (pushSubgraph_adj_of_inj H hinj u v).symm
            · intro hemb
              have hemb' := (isIndEmbBool_eq_true_iff H F φ).mp hemb
              refine ⟨(isHomBool_eq_true_iff H G φ).mpr fun u v huv => ?_, ?_⟩
              · rw [hemb' u v] at huv
                exact (hspan _ _ huv).2.2
              · apply SimpleGraphN.ext; funext y₁ y₂
                by_cases hy₁ : imageMask φ y₁ = true <;> by_cases hy₂ : imageMask φ y₂ = true
                · rcases (imageMask_eq_true_iff φ y₁).mp hy₁ with ⟨u, rfl⟩
                  rcases (imageMask_eq_true_iff φ y₂).mp hy₂ with ⟨v, rfl⟩
                  rw [pushSubgraph_adj_of_inj H hinj u v, hemb' u v]
                · have hF0 : F.adj y₁ y₂ = false :=
                    Bool.eq_false_iff.mpr (fun h => hy₂ (hspan y₁ y₂ h).2.1)
                  have hP0 : (pushSubgraph H φ).adj y₁ y₂ = false := by
                    unfold pushSubgraph; dsimp only
                    split
                    · rfl
                    · apply Bool.eq_false_iff.mpr; intro hany
                      rcases List.any_eq_true.mp hany with ⟨u, _, hu⟩
                      rcases List.any_eq_true.mp hu with ⟨v, _, hv⟩
                      simp only [Bool.and_eq_true] at hv
                      have hv' : φ v = y₂ := of_decide_eq_true (by simpa using hv.1.2)
                      exact hy₂ ((imageMask_eq_true_iff φ y₂).mpr ⟨v, hv'⟩)
                  rw [hP0, hF0]
                · have hF0 : F.adj y₁ y₂ = false :=
                    Bool.eq_false_iff.mpr (fun h => hy₁ (hspan y₁ y₂ h).1)
                  have hP0 : (pushSubgraph H φ).adj y₁ y₂ = false := by
                    unfold pushSubgraph; dsimp only
                    split
                    · rfl
                    · apply Bool.eq_false_iff.mpr; intro hany
                      rcases List.any_eq_true.mp hany with ⟨u, _, hu⟩
                      rcases List.any_eq_true.mp hu with ⟨v, _, hv⟩
                      simp only [Bool.and_eq_true] at hv
                      have hu' : φ u = y₁ := of_decide_eq_true (by simpa using hv.1.1)
                      exact hy₁ ((imageMask_eq_true_iff φ y₁).mpr ⟨u, hu'⟩)
                  rw [hP0, hF0]
                · have hF0 : F.adj y₁ y₂ = false :=
                    Bool.eq_false_iff.mpr (fun h => hy₁ (hspan y₁ y₂ h).1)
                  have hP0 : (pushSubgraph H φ).adj y₁ y₂ = false := by
                    unfold pushSubgraph; dsimp only
                    split
                    · rfl
                    · apply Bool.eq_false_iff.mpr; intro hany
                      rcases List.any_eq_true.mp hany with ⟨u, _, hu⟩
                      rcases List.any_eq_true.mp hu with ⟨v, _, hv⟩
                      simp only [Bool.and_eq_true] at hv
                      have hu' : φ u = y₁ := of_decide_eq_true (by simpa using hv.1.1)
                      exact hy₁ ((imageMask_eq_true_iff φ y₁).mpr ⟨u, hu'⟩)
                  rw [hP0, hF0]
          by_cases he : isIndEmbBool H F φ = true
          · rcases hiff.mpr he with ⟨hh, hp⟩
            simp [hinjb, hh, hp, he]
          · have hef := Bool.eq_false_iff.mpr he
            have hnot : ¬ (isHomBool H G φ = true ∧ pushSubgraph H φ = F) := fun h => he (hiff.mp h)
            cases hh : isHomBool H G φ
            · simp [hinjb, hh, hef]
            · have hp : pushSubgraph H φ ≠ F := fun h => hnot ⟨hh, h⟩
              simp [hinjb, hh, hp, hef]
        · simp [hinjb, himgb]
      · have hinjf := Bool.eq_false_iff.mpr hinjb
        simp [hinjf]
    rw [hfiber_eq]
    -- Now reuse the exact fiber calculation over `S` for `H` and `F`!
    -- Wait: we know from `hSF.2 : indIsoOnSubsetBool H F S = true`!
    rcases List.any_eq_true.mp hSF.2 with ⟨φ₀, _, hφ₀⟩
    simp only [Bool.and_eq_true] at hφ₀
    have hinj₀ := (isInjBool_eq_true_iff φ₀).mp hφ₀.1.1
    have himg₀ : imageMask φ₀ = S := of_decide_eq_true (by simpa using hφ₀.1.2)
    have hemb₀ := (isIndEmbBool_eq_true_iff H F φ₀).mp hφ₀.2
    unfold indEmbCount
    refine countWhere_bij
      (fun φ => pullbackPerm φ₀ φ)
      (fun α i => φ₀ (α i))
      (nodup_allFinMaps k n) (nodup_allFinMaps k k) ?_ ?_
    · intro φ _ hφ
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hφ
      have hinj := (isInjBool_eq_true_iff φ).mp hφ.1.1
      have himg : imageMask φ = imageMask φ₀ := hφ.2.trans himg₀.symm
      have hemb := (isIndEmbBool_eq_true_iff H F φ).mp hφ.1.2
      have hspec : ∀ i, φ₀ (pullbackPerm φ₀ φ i) = φ i :=
        pullbackPerm_spec (fun i => by
          rw [← himg]; exact (imageMask_eq_true_iff φ (φ i)).mpr ⟨i, rfl⟩)
      refine ⟨mem_allFinMaps _, ?_, funext hspec⟩
      simp only [Bool.and_eq_true]
      refine ⟨(isInjBool_eq_true_iff _).mpr fun i j hij => hinj i j (by rw [← hspec i, ← hspec j, hij]),
              (isIndEmbBool_eq_true_iff H H _).mpr fun u v => by
                rw [hemb u v, ← hspec u, ← hspec v, ← hemb₀]⟩
    · intro α _ hα
      simp only [Bool.and_eq_true] at hα
      have hinjα := (isInjBool_eq_true_iff α).mp hα.1
      have hembα := (isIndEmbBool_eq_true_iff H H α).mp hα.2
      have hsurjα : ∀ j : Fin k, ∃ i : Fin k, α i = j := by
        intro j
        by_cases hmem : imageMask α j = true
        · exact (imageMask_eq_true_iff α j).mp hmem
        · exfalso
          have hmemF := Bool.eq_false_iff.mpr hmem
          have hnd := nodup_map_of_inj_on (nodup_allFin k) (fun a _ b _ h => hinjα a b h)
          have hsub : ∀ z ∈ (allFin k).map α, z ∈ removeOne j (allFin k) := by
            intro z hz
            rcases List.mem_map.mp hz with ⟨i, _, rfl⟩
            refine mem_removeOne_of_ne ?_ (mem_allFin (α i))
            intro heq
            have : imageMask α j = true := (imageMask_eq_true_iff α j).mpr ⟨i, heq⟩
            rw [hmemF] at this; cases this
          have hle := nodup_length_le_of_subset hnd hsub
          have hrem := length_removeOne_of_mem (mem_allFin j)
          rw [List.length_map, length_allFin] at hle
          rw [length_allFin] at hrem
          omega
      refine ⟨mem_allFinMaps _, ?_, ?_⟩
      · simp only [Bool.and_eq_true, decide_eq_true_eq]
        refine ⟨⟨(isInjBool_eq_true_iff _).mpr fun i j hij => hinjα i j (hinj₀ _ _ hij),
                 (isIndEmbBool_eq_true_iff H F _).mpr fun u v => by
                   rw [← hemb₀ (α u) (α v), ← hembα u v]⟩, ?_⟩
        rw [← himg₀]; funext y
        by_cases hy : imageMask φ₀ y = true
        · rcases (imageMask_eq_true_iff φ₀ y).mp hy with ⟨j, rfl⟩
          rcases hsurjα j with ⟨i, rfl⟩
          have lhs : imageMask (fun x => φ₀ (α x)) (φ₀ (α i)) = true :=
            (imageMask_eq_true_iff _ _).mpr ⟨i, rfl⟩
          rw [lhs, hy]
        · have hyF := Bool.eq_false_iff.mpr hy
          have lhsF : imageMask (fun x => φ₀ (α x)) y = false := by
            apply Bool.eq_false_iff.mpr; intro h
            rcases (imageMask_eq_true_iff _ y).mp h with ⟨i, rfl⟩
            exact hy ((imageMask_eq_true_iff φ₀ _).mpr ⟨α i, rfl⟩)
          rw [lhsF, hyF]
      · funext i
        apply hinj₀
        exact pullbackPerm_spec (fun x => (imageMask_eq_true_iff φ₀ _).mpr ⟨α x, rfl⟩) i

/-! ### Step 2: Connected `indEmbCount` Equality Implies Connected `injHomCount` Equality -/

/-- Pullback of `G : SimpleGraphN n` along `φ : Fin k → Fin n` (setting diagonal to `false`). -/
def pullbackGraph {k n : Nat} (G : SimpleGraphN n) (φ : Fin k → Fin n) : SimpleGraphN k where
  adj u v := if u = v then false else G.adj (φ u) (φ v)
  loopless u := by simp
  symm u v := by
    by_cases huv : u = v
    · subst huv; simp
    · have hvu : v ≠ u := fun h => huv h.symm
      simp [huv, hvu, G.symm]

/-- Test whether `H'` is a supergraph of `H` on `Fin k`. -/
def isSupergraph {k : Nat} (H H' : SimpleGraphN k) : Bool :=
  (allFin k).all (fun u => (allFin k).all (fun v => !H.adj u v || H'.adj u v))

theorem isConnectedGraph_of_supergraph {k : Nat} {H H' : SimpleGraphN k}
    (hconn : IsConnectedGraph H) (hsup : isSupergraph H H' = true) :
    IsConnectedGraph H' := by
  have hmono : ∀ a b : Fin k, H.adj a b = true → H'.adj a b = true := by
    intro a b hab
    have h1 := List.all_eq_true.mp hsup a (mem_allFin a)
    have h2 := List.all_eq_true.mp h1 b (mem_allFin b)
    simp only [hab, Bool.not_true, Bool.false_or] at h2
    exact h2
  refine ⟨hconn.1, fun u v hu hv => ?_⟩
  exact ReachableIn.mono_adj (fun a b _ _ hab => hmono a b hab) (hconn.2 u v hu hv)

theorem injHomCount_eq_sum_supergraphs {k n : Nat} (H : SimpleGraphN k) (G : SimpleGraphN n) :
    injHomCount H G =
      listSum (((allSimpleGraphs k).filter (isSupergraph H)).map (fun H' => indEmbCount H' G)) := by
  unfold injHomCount
  have hmem : ∀ φ ∈ allFinMaps k n, (isInjBool φ && isHomBool H G φ) = true →
      pullbackGraph G φ ∈ (allSimpleGraphs k).filter (isSupergraph H) := by
    intro φ _ hφ
    simp only [Bool.and_eq_true] at hφ
    have hhom := (isHomBool_eq_true_iff H G φ).mp hφ.2
    refine List.mem_filter.mpr ⟨mem_allSimpleGraphs _, ?_⟩
    unfold isSupergraph
    apply List.all_eq_true.mpr; intro u _
    apply List.all_eq_true.mpr; intro v _
    cases huv : H.adj u v
    · simp
    · have hne : u ≠ v := fun h => by subst h; rw [H.loopless] at huv; cases huv
      simp [pullbackGraph, hne, hhom u v huv]
  rw [countWhere_partition (nodup_filter _ (nodup_allSimpleGraphs k)) (pullbackGraph G) hmem]
  refine listSum_congr ?_
  intro H' hH'
  have hsup : isSupergraph H H' = true := (List.mem_filter.mp hH').2
  have hsup' : ∀ u v, H.adj u v = true → H'.adj u v = true := by
    intro u v huv
    have h1 := List.all_eq_true.mp hsup u (mem_allFin u)
    have h2 := List.all_eq_true.mp h1 v (mem_allFin v)
    simp only [huv, Bool.not_true, Bool.false_or] at h2
    exact h2
  unfold indEmbCount countWhere
  congr 1
  refine List.filter_congr ?_
  intro φ _
  by_cases hinjb : isInjBool φ = true
  · have hinj := (isInjBool_eq_true_iff φ).mp hinjb
    by_cases hemb : isIndEmbBool H' G φ = true
    · have hemb' := (isIndEmbBool_eq_true_iff H' G φ).mp hemb
      have hhom : isHomBool H G φ = true :=
        (isHomBool_eq_true_iff H G φ).mpr fun u v huv => by
          rw [← hemb' u v]; exact hsup' u v huv
      have hpb : pullbackGraph G φ = H' := by
        apply SimpleGraphN.ext; funext u v
        unfold pullbackGraph; dsimp only
        by_cases huv : u = v
        · subst huv; simp [H'.loopless]
        · simp [huv, ← hemb' u v]
      simp [hinjb, hemb, hhom, hpb]
    · have hembf := Bool.eq_false_iff.mpr hemb
      have hnotpb : pullbackGraph G φ ≠ H' := by
        intro hpb
        apply hemb
        rw [isIndEmbBool_eq_true_iff]
        intro u v
        rw [← hpb]; unfold pullbackGraph; dsimp only
        by_cases huv : u = v
        · subst huv; simp [G.loopless]
        · simp [huv]
      simp [hinjb, hembf, hnotpb]
  · have hinjf := Bool.eq_false_iff.mpr hinjb
    simp [hinjf]

theorem conn_indEmb_imp_conn_injHom {n₁ n₂ : Nat}
    {G₁ : SimpleGraphN n₁} {G₂ : SimpleGraphN n₂}
    (h : ∀ k (H : SimpleGraphN k), IsConnectedGraph H → indEmbCount H G₁ = indEmbCount H G₂) :
    ∀ k (H : SimpleGraphN k), IsConnectedGraph H → injHomCount H G₁ = injHomCount H G₂ := by
  intro k H hconn
  rw [injHomCount_eq_sum_supergraphs H G₁, injHomCount_eq_sum_supergraphs H G₂]
  refine listSum_congr ?_
  intro H' hH'
  have hsup := (List.mem_filter.mp hH').2
  exact h k H' (isConnectedGraph_of_supergraph hconn hsup)

/-! ### Step 3: 1-Edge Inequality Contraction Recurrence (`ConstrainedHom`) -/

/-- Test whether `φ : Fin k → Fin n` assigns distinct values to every edge of `D`. -/
def isNeqOnBool {k n : Nat} (D : SimpleGraphN k) (φ : Fin k → Fin n) : Bool :=
  (allFin k).all (fun u => (allFin k).all (fun v => !D.adj u v || !(φ u == φ v)))

theorem isNeqOnBool_eq_true_iff {k n : Nat} (D : SimpleGraphN k) (φ : Fin k → Fin n) :
    isNeqOnBool D φ = true ↔ (∀ u v : Fin k, D.adj u v = true → φ u ≠ φ v) := by
  unfold isNeqOnBool
  constructor
  · intro h u v huv heq
    have h1 := List.all_eq_true.mp h u (mem_allFin u)
    have h2 := List.all_eq_true.mp h1 v (mem_allFin v)
    have hbeq : (φ u == φ v) = true := by simpa using decide_eq_true heq
    simp [huv, hbeq] at h2
  · intro h
    apply List.all_eq_true.mpr; intro u _
    apply List.all_eq_true.mpr; intro v _
    cases huv : D.adj u v
    · simp
    · have hne := h u v huv
      have hbeq : (φ u == φ v) = false :=
        Bool.eq_false_iff.mpr (fun hb => hne (of_decide_eq_true (by simpa using hb)))
      simp [hbeq]

/-- Count of homomorphisms `H → G` respecting inequality constraints `D`. -/
def constrainedHomCount {k n : Nat} (H D : SimpleGraphN k) (G : SimpleGraphN n) : Nat :=
  countWhere (allFinMaps k n) (fun φ => isHomBool H G φ && isNeqOnBool D φ)

/-- Empty simple graph on `k` vertices (0 edges). -/
def emptySimpleGraph (k : Nat) : SimpleGraphN k where
  adj _ _ := false
  loopless _ := rfl
  symm _ _ := rfl

/-- Complete simple graph `K_k` on `k` vertices. -/
def completeSimpleGraph (k : Nat) : SimpleGraphN k where
  adj u v := !(u == v)
  loopless u := by simp
  symm u v := by
    by_cases h : u = v
    · subst h; simp
    · have h' : v ≠ u := fun e => h e.symm
      have b1 : (u == v) = false := Bool.eq_false_iff.mpr (fun e => h (of_decide_eq_true (by simpa using e)))
      have b2 : (v == u) = false := Bool.eq_false_iff.mpr (fun e => h' (of_decide_eq_true (by simpa using e)))
      simp [b1, b2]

theorem constrainedHomCount_empty {k n : Nat} (H : SimpleGraphN k) (G : SimpleGraphN n) :
    constrainedHomCount H (emptySimpleGraph k) G = homCount H G := by
  unfold constrainedHomCount homCount countWhere
  congr 1
  refine List.filter_congr ?_
  intro φ _
  have : isNeqOnBool (emptySimpleGraph k) φ = true :=
    (isNeqOnBool_eq_true_iff _ φ).mpr fun _ _ h => by cases h
  simp [this]

theorem constrainedHomCount_complete {k n : Nat} (H : SimpleGraphN k) (G : SimpleGraphN n) :
    constrainedHomCount H (completeSimpleGraph k) G = injHomCount H G := by
  unfold constrainedHomCount injHomCount countWhere
  congr 1
  refine List.filter_congr ?_
  intro φ _
  have hiff : isNeqOnBool (completeSimpleGraph k) φ = isInjBool φ := by
    by_cases h : isInjBool φ = true
    · have hinj := (isInjBool_eq_true_iff φ).mp h
      have hn : isNeqOnBool (completeSimpleGraph k) φ = true :=
        (isNeqOnBool_eq_true_iff _ φ).mpr fun u v huv heq => by
          have := hinj u v heq; subst this
          unfold completeSimpleGraph at huv; simp at huv
      rw [h, hn]
    · have hf := Bool.eq_false_iff.mpr h
      have hnf : isNeqOnBool (completeSimpleGraph k) φ = false := by
        apply Bool.eq_false_iff.mpr; intro hn
        have hn' := (isNeqOnBool_eq_true_iff _ φ).mp hn
        apply h; rw [isInjBool_eq_true_iff]
        intro u v heq
        by_cases huv : u = v
        · exact huv
        · exfalso; apply hn' u v ?_ heq
          unfold completeSimpleGraph
          have b : (u == v) = false := Bool.eq_false_iff.mpr (fun e => huv (of_decide_eq_true (by simpa using e)))
          simp [b]
      rw [hf, hnf]
  rw [hiff, Bool.and_comm]

/-- Number of ordered non-edges `(u, v)` (`u ≠ v`, `D.adj u v = false`) in `D`. -/
def nonEdgeCount {k : Nat} (D : SimpleGraphN k) : Nat :=
  countWhere (listProd (allFin k) (allFin k)) (fun p => !(p.1 == p.2) && !D.adj p.1 p.2)

/-- Number of ordered edges `(u, v)` (`D.adj u v = true`) in `D`. -/
def directedEdgeCount {k : Nat} (D : SimpleGraphN k) : Nat :=
  countWhere (listProd (allFin k) (allFin k)) (fun p => D.adj p.1 p.2)

/-- Add undirected edge `{a, b}` (`a ≠ b`) to `D`. -/
def addEdgeGraph {k : Nat} (D : SimpleGraphN k) (a b : Fin k) (hab : a ≠ b) : SimpleGraphN k where
  adj u v := D.adj u v || ((u == a) && (v == b)) || ((u == b) && (v == a))
  loopless u := by
    by_cases hua : u = a
    · subst hua
      have hba : (u == b) = false := Bool.eq_false_iff.mpr (fun e => hab (of_decide_eq_true (by simpa using e)))
      simp [D.loopless, hba]
    · have huaF : (u == a) = false := Bool.eq_false_iff.mpr (fun e => hua (of_decide_eq_true (by simpa using e)))
      simp [D.loopless, huaF]
  symm u v := by
    rw [D.symm u v]
    cases (u == a) <;> cases (v == b) <;> cases (u == b) <;> cases (v == a) <;> simp

/-- Remove undirected edge `{a, b}` from `D`. -/
def removeEdgeGraph {k : Nat} (D : SimpleGraphN k) (a b : Fin k) : SimpleGraphN k where
  adj u v := D.adj u v && !((u == a) && (v == b)) && !((u == b) && (v == a))
  loopless u := by simp [D.loopless]
  symm u v := by
    rw [D.symm u v]
    cases (u == a) <;> cases (v == b) <;> cases (u == b) <;> cases (v == a) <;> simp

theorem addEdge_removeEdge {k : Nat} (D : SimpleGraphN k) {a b : Fin k}
    (hadj : D.adj a b = true) :
    ∃ hab : a ≠ b, addEdgeGraph (removeEdgeGraph D a b) a b hab = D := by
  have hab : a ≠ b := fun h => by subst h; rw [D.loopless] at hadj; cases hadj
  refine ⟨hab, SimpleGraphN.ext ?_⟩
  funext u v
  unfold addEdgeGraph removeEdgeGraph; dsimp only
  have hba : D.adj b a = true := by rw [D.symm b a]; exact hadj
  by_cases h1 : u = a ∧ v = b
  · rcases h1 with ⟨rfl, rfl⟩; simp [hadj]
  · by_cases h2 : u = b ∧ v = a
    · rcases h2 with ⟨rfl, rfl⟩; simp [hba]
    · have b1 : ((u == a) && (v == b)) = false := by
        apply Bool.eq_false_iff.mpr; intro h
        simp only [Bool.and_eq_true] at h
        exact h1 ⟨of_decide_eq_true (by simpa using h.1), of_decide_eq_true (by simpa using h.2)⟩
      have b2 : ((u == b) && (v == a)) = false := by
        apply Bool.eq_false_iff.mpr; intro h
        simp only [Bool.and_eq_true] at h
        exact h2 ⟨of_decide_eq_true (by simpa using h.1), of_decide_eq_true (by simpa using h.2)⟩
      simp [b1, b2]

/-- Compress `x : Fin (m + 1)` (`x ≠ b`) into `Fin m`, inverse to `deleteIdx b`. -/
def compressIdx {m : Nat} (b x : Fin (m + 1)) (hxb : x ≠ b) : Fin m :=
  if h : x.val < b.val then ⟨x.val, by have := b.isLt; omega⟩
  else ⟨x.val - 1, by
    have hxl := x.isLt
    have hne : x.val ≠ b.val := fun e => hxb (Fin.ext e)
    omega⟩

theorem deleteIdx_compressIdx {m : Nat} (b x : Fin (m + 1)) (hxb : x ≠ b) :
    deleteIdx b (compressIdx b x hxb) = x := by
  apply Fin.ext
  rw [deleteIdx_val]
  unfold compressIdx
  have hne : x.val ≠ b.val := fun e => hxb (Fin.ext e)
  by_cases h : x.val < b.val
  · simp [h]
  · have h2 : ¬ (x.val - 1 < b.val) := by omega
    simp [h, h2]; omega

theorem compressIdx_val {m : Nat} (b x : Fin (m + 1)) (hxb : x ≠ b) :
    (compressIdx b x hxb).val = if x.val < b.val then x.val else x.val - 1 := by
  unfold compressIdx
  split <;> rfl

theorem compressIdx_deleteIdx {m : Nat} (b : Fin (m + 1)) (i : Fin m)
    (hne : deleteIdx b i ≠ b) :
    compressIdx b (deleteIdx b i) hne = i := by
  apply Fin.ext
  rw [compressIdx_val, deleteIdx_val]
  by_cases h : i.val < b.val
  · simp [h]
  · have h2 : ¬ (i.val + 1 < b.val) := by omega
    simp [h, h2]

theorem deleteIdx_ne_self {m : Nat} (b : Fin (m + 1)) (i : Fin m) :
    deleteIdx b i ≠ b := by
  intro h
  have := congrArg Fin.val h
  rw [deleteIdx_val] at this
  split at this <;> omega

/-- Contraction surjection `Fin (m + 1) → Fin m` merging `b` into `a` (`a ≠ b`). -/
def projContract {m : Nat} (a b : Fin (m + 1)) (hab : a ≠ b) (x : Fin (m + 1)) : Fin m :=
  if hxb : x = b then compressIdx b a hab
  else compressIdx b x hxb

theorem projContract_b {m : Nat} (a b : Fin (m + 1)) (hab : a ≠ b) :
    projContract a b hab b = compressIdx b a hab := by
  unfold projContract; simp

theorem projContract_a {m : Nat} (a b : Fin (m + 1)) (hab : a ≠ b) :
    projContract a b hab a = compressIdx b a hab := by
  unfold projContract; simp [hab]

theorem projContract_deleteIdx {m : Nat} (a b : Fin (m + 1)) (hab : a ≠ b) (i : Fin m) :
    projContract a b hab (deleteIdx b i) = i := by
  unfold projContract
  have hne := deleteIdx_ne_self b i
  simp only [hne, ↓reduceDIte]
  exact compressIdx_deleteIdx b i hne

theorem deleteIdx_projContract {m : Nat} (a b : Fin (m + 1)) (hab : a ≠ b) (x : Fin (m + 1)) :
    deleteIdx b (projContract a b hab x) = if x = b then a else x := by
  unfold projContract
  by_cases hxb : x = b
  · simp [hxb, deleteIdx_compressIdx]
  · simp [hxb, deleteIdx_compressIdx]

/-- Contract non-adjacent vertices `a` and `b` (`a ≠ b`, `K.adj a b = false`) into a single
    vertex `compressIdx b a hab` in `SimpleGraphN m`. -/
def contractPairGraph {m : Nat} (K : SimpleGraphN (m + 1)) (a b : Fin (m + 1))
    (hab : a ≠ b) (hno : K.adj a b = false) : SimpleGraphN m :=
  let a' := compressIdx b a hab
  { adj := fun i j =>
      K.adj (deleteIdx b i) (deleteIdx b j) ||
      ((i == a') && K.adj b (deleteIdx b j)) ||
      ((j == a') && K.adj (deleteIdx b i) b)
    loopless := fun i => by
      by_cases hia : i = a'
      · subst hia
        have hda : deleteIdx b a' = a := deleteIdx_compressIdx b a hab
        have hba : K.adj b a = false := by rw [K.symm b a]; exact hno
        simp [K.loopless, hda, hno, hba]
      · have hiaF : (i == a') = false :=
          Bool.eq_false_iff.mpr (fun e => hia (of_decide_eq_true (by simpa using e)))
        simp [K.loopless, hiaF]
    symm := fun i j => by
      rw [K.symm (deleteIdx b i) (deleteIdx b j),
          K.symm b (deleteIdx b j),
          K.symm (deleteIdx b i) b]
      cases K.adj (deleteIdx b j) (deleteIdx b i) <;>
      cases (i == a') <;> cases (j == a') <;>
      cases K.adj (deleteIdx b j) b <;> cases K.adj b (deleteIdx b i) <;> rfl }

theorem contractPairGraph_connected {m : Nat} {H : SimpleGraphN (m + 1)}
    (a b : Fin (m + 1)) (hab : a ≠ b) (hno : H.adj a b = false)
    (hconn : IsConnectedGraph H) :
    IsConnectedGraph (contractPairGraph H a b hab hno) := by
  let p := projContract a b hab
  let Hc := contractPairGraph H a b hab hno
  have hp_reach : ∀ u v : Fin (m + 1),
      ReachableIn H.adj (fun _ => true) u v →
      ReachableIn Hc.adj (fun _ => true) (p u) (p v) := by
    intro u v hr
    induction hr with
    | refl _ => exact .refl rfl
    | @step x y _ _ _ hxy _ ih =>
      by_cases hp_eq : p x = p y
      · rw [hp_eq]; exact ih
      · refine .step rfl rfl ?_ ih
        unfold Hc contractPairGraph; dsimp only
        have hx := deleteIdx_projContract a b hab x
        have hy := deleteIdx_projContract a b hab y
        change deleteIdx b (p x) = _ at hx
        change deleteIdx b (p y) = _ at hy
        by_cases hxb : x = b <;> by_cases hyb : y = b
        · rw [hxb, hyb, H.loopless] at hxy; cases hxy
        · have hpx : (p x == compressIdx b a hab) = true := by
            show (projContract a b hab x == compressIdx b a hab) = true
            rw [hxb, projContract_b]; simp
          have hb_adj : H.adj b y = true := hxb ▸ hxy
          simp only [hyb, ↓reduceIte] at hy
          rw [hy]
          simp [hpx, hb_adj]
        · have hpy : (p y == compressIdx b a hab) = true := by
            show (projContract a b hab y == compressIdx b a hab) = true
            rw [hyb, projContract_b]; simp
          have hb_adj : H.adj x b = true := hyb ▸ hxy
          simp only [hxb, ↓reduceIte] at hx
          rw [hx]
          simp [hpy, hb_adj]
        · simp only [hxb, hyb, ↓reduceIte] at hx hy
          rw [hx, hy]
          simp [hxy]
  refine ⟨⟨p 0, rfl⟩, fun i j _ _ => ?_⟩
  have hreach := hconn.2 (deleteIdx b i) (deleteIdx b j) rfl rfl
  have hm := hp_reach _ _ hreach
  dsimp only [p] at hm
  rw [projContract_deleteIdx, projContract_deleteIdx] at hm
  exact hm

/-- Fundamental 1-Edge Contraction Recurrence for `constrainedHomCount`! -/
theorem constrainedHomCount_split {m n : Nat} (H D : SimpleGraphN (m + 1))
    (G : SimpleGraphN n) (a b : Fin (m + 1)) (hab : a ≠ b) (hd : D.adj a b = false) :
    constrainedHomCount H D G =
      constrainedHomCount H (addEdgeGraph D a b hab) G +
      (if hH : H.adj a b = true then 0
       else constrainedHomCount
              (contractPairGraph H a b hab (Bool.eq_false_iff.mpr hH))
              (contractPairGraph D a b hab hd) G) := by
  have hpart := countWhere_partition (L := allFinMaps (m + 1) n)
    (P := fun φ => isHomBool H G φ && isNeqOnBool D φ)
    (tags := [false, true])
    (.cons (by simp) (.cons (by simp) .nil))
    (fun φ => φ a == φ b)
    (fun φ _ _ => by
      dsimp only
      cases (φ a == φ b) <;> simp)
  unfold constrainedHomCount
  rw [hpart]
  simp only [List.map, listSum, Nat.add_zero]
  -- Term 1 (`(φ a == φ b) = false`): literally `constrainedHomCount H (addEdgeGraph D a b hab) G`!
  have hterm1 :
      countWhere (allFinMaps (m + 1) n)
        (fun φ => (isHomBool H G φ && isNeqOnBool D φ) && decide ((φ a == φ b) = false)) =
      countWhere (allFinMaps (m + 1) n)
        (fun φ => isHomBool H G φ && isNeqOnBool (addEdgeGraph D a b hab) φ) := by
    unfold countWhere; congr 1
    refine List.filter_congr ?_; intro φ _
    by_cases hh : isHomBool H G φ = true
    · simp only [hh, Bool.true_and]
      by_cases hd' : isNeqOnBool D φ = true
      · have hd_iff := (isNeqOnBool_eq_true_iff D φ).mp hd'
        by_cases heq : φ a = φ b
        · have hb : (φ a == φ b) = true := by simpa using decide_eq_true heq
          have haddF : isNeqOnBool (addEdgeGraph D a b hab) φ = false := by
            apply Bool.eq_false_iff.mpr; intro hadd
            have := (isNeqOnBool_eq_true_iff _ φ).mp hadd a b (by unfold addEdgeGraph; simp)
            exact this heq
          simp [hd', hb, haddF]
        · have hb : (φ a == φ b) = false :=
            Bool.eq_false_iff.mpr (fun e => heq (of_decide_eq_true (by simpa using e)))
          have haddT : isNeqOnBool (addEdgeGraph D a b hab) φ = true := by
            rw [isNeqOnBool_eq_true_iff]
            intro u v huv
            unfold addEdgeGraph at huv; dsimp only at huv
            simp only [Bool.or_eq_true, Bool.and_eq_true] at huv
            rcases huv with (hduv | ⟨hua, hvb⟩) | ⟨hub, hva⟩
            · exact hd_iff u v hduv
            · have hu' : u = a := of_decide_eq_true (by simpa using hua)
              have hv' : v = b := of_decide_eq_true (by simpa using hvb)
              subst hu'; subst hv'; exact heq
            · have hu' : u = b := of_decide_eq_true (by simpa using hub)
              have hv' : v = a := of_decide_eq_true (by simpa using hva)
              subst hu'; subst hv'; exact fun e => heq e.symm
          simp [hd', hb, haddT]
      · have hdF := Bool.eq_false_iff.mpr hd'
        have haddF : isNeqOnBool (addEdgeGraph D a b hab) φ = false := by
          apply Bool.eq_false_iff.mpr; intro hadd
          have hadd_iff := (isNeqOnBool_eq_true_iff _ φ).mp hadd
          apply hd'; rw [isNeqOnBool_eq_true_iff]
          intro u v huv
          exact hadd_iff u v (by unfold addEdgeGraph; simp [huv])
        simp [hdF, haddF]
    · have hhF := Bool.eq_false_iff.mpr hh
      simp [hhF]
  rw [hterm1]
  congr 1
  -- Term 2 (`(φ a == φ b) = true`):
  by_cases hH : H.adj a b = true
  · simp only [hH, ↓reduceDIte]
    unfold countWhere
    suffices hnil : (allFinMaps (m + 1) n).filter
        (fun φ => (isHomBool H G φ && isNeqOnBool D φ) && decide ((φ a == φ b) = true)) = [] by
      rw [hnil]; rfl
    apply List.filter_eq_nil_iff.mpr
    intro φ _ htrue
    simp only [Bool.and_eq_true, decide_eq_true_eq] at htrue
    have hhom := (isHomBool_eq_true_iff H G φ).mp htrue.1.1 a b hH
    have heq : φ a = φ b := of_decide_eq_true (by simpa using htrue.2)
    rw [heq, G.loopless] at hhom
    cases hhom
  · simp only [hH, ↓reduceDIte]
    have hHF : H.adj a b = false := Bool.eq_false_iff.mpr hH
    let Hc := contractPairGraph H a b hab hHF
    let Dc := contractPairGraph D a b hab hd
    let p := projContract a b hab
    refine countWhere_bij
      (fun φ i => φ (deleteIdx b i))
      (fun ψ x => ψ (p x))
      (nodup_allFinMaps (m + 1) n) (nodup_allFinMaps m n) ?_ ?_
    · intro φ _ hφ
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hφ
      have hhom := (isHomBool_eq_true_iff H G φ).mp hφ.1.1
      have hneq := (isNeqOnBool_eq_true_iff D φ).mp hφ.1.2
      have hab_eq : φ a = φ b := of_decide_eq_true (by simpa using hφ.2)
      have hφ_factor : ∀ x, φ (deleteIdx b (p x)) = φ x := by
        intro x
        rw [deleteIdx_projContract]
        split
        · next hxb => subst hxb; exact hab_eq
        · rfl
      refine ⟨mem_allFinMaps _, ?_, funext hφ_factor⟩
      simp only [Bool.and_eq_true]
      refine ⟨(isHomBool_eq_true_iff Hc G _).mpr ?_, (isNeqOnBool_eq_true_iff Dc _).mpr ?_⟩
      · intro i j hij
        unfold Hc contractPairGraph at hij; dsimp only at hij
        simp only [Bool.or_eq_true, Bool.and_eq_true] at hij
        rcases hij with (h1 | ⟨hi, h2⟩) | ⟨hj, h3⟩
        · exact hhom _ _ h1
        · have hi' : i = compressIdx b a hab := of_decide_eq_true (by simpa using hi)
          subst hi'
          rw [deleteIdx_compressIdx, hab_eq]
          exact hhom _ _ h2
        · have hj' : j = compressIdx b a hab := of_decide_eq_true (by simpa using hj)
          subst hj'
          rw [deleteIdx_compressIdx, hab_eq]
          exact hhom _ _ h3
      · intro i j hij
        unfold Dc contractPairGraph at hij; dsimp only at hij
        simp only [Bool.or_eq_true, Bool.and_eq_true] at hij
        rcases hij with (h1 | ⟨hi, h2⟩) | ⟨hj, h3⟩
        · exact hneq _ _ h1
        · have hi' : i = compressIdx b a hab := of_decide_eq_true (by simpa using hi)
          subst hi'
          rw [deleteIdx_compressIdx, hab_eq]
          exact hneq _ _ h2
        · have hj' : j = compressIdx b a hab := of_decide_eq_true (by simpa using hj)
          subst hj'
          rw [deleteIdx_compressIdx, hab_eq]
          exact hneq _ _ h3
    · intro ψ _ hψ
      simp only [Bool.and_eq_true] at hψ
      have hhom := (isHomBool_eq_true_iff Hc G ψ).mp hψ.1
      have hneq := (isNeqOnBool_eq_true_iff Dc ψ).mp hψ.2
      -- Helper: any edge `K.adj u v = true` (with `K.adj a b = false`) maps to an edge of `contractPairGraph K`!
      have hmap_edge : ∀ (K : SimpleGraphN (m + 1)) (hK : K.adj a b = false) (u v : Fin (m + 1)),
          K.adj u v = true →
            p u ≠ p v ∧ (contractPairGraph K a b hab hK).adj (p u) (p v) = true := by
        intro K hK u v huv
        have hKba : K.adj b a = false := by rw [K.symm b a]; exact hK
        have hp_ne : p u ≠ p v := by
          intro hpeq
          have hu := deleteIdx_projContract a b hab u
          have hv := deleteIdx_projContract a b hab v
          change deleteIdx b (p u) = _ at hu
          change deleteIdx b (p v) = _ at hv
          rw [hpeq] at hu
          have heq_if : (if u = b then a else u) = (if v = b then a else v) := hu.symm.trans hv
          by_cases hub : u = b <;> by_cases hvb : v = b
          · rw [hub, hvb, K.loopless] at huv; cases huv
          · simp only [hub, hvb, ↓reduceIte] at heq_if
            rw [hub, ← heq_if, hKba] at huv; cases huv
          · simp only [hub, hvb, ↓reduceIte] at heq_if
            rw [hvb, heq_if, hK] at huv; cases huv
          · simp only [hub, hvb, ↓reduceIte] at heq_if
            rw [heq_if, K.loopless] at huv; cases huv
        refine ⟨hp_ne, ?_⟩
        unfold contractPairGraph; dsimp only
        have hu := deleteIdx_projContract a b hab u
        have hv := deleteIdx_projContract a b hab v
        change deleteIdx b (p u) = _ at hu
        change deleteIdx b (p v) = _ at hv
        by_cases hub : u = b <;> by_cases hvb : v = b
        · rw [hub, hvb, K.loopless] at huv; cases huv
        · have hpb : (p u == compressIdx b a hab) = true := by
            show (projContract a b hab u == compressIdx b a hab) = true
            rw [hub, projContract_b]; simp
          simp only [hvb, ↓reduceIte] at hv; rw [hv]; rw [hub] at huv; simp [hpb, huv]
        · have hpb : (p v == compressIdx b a hab) = true := by
            show (projContract a b hab v == compressIdx b a hab) = true
            rw [hvb, projContract_b]; simp
          simp only [hub, ↓reduceIte] at hu; rw [hu]; rw [hvb] at huv; simp [hpb, huv]
        · simp only [hub, hvb, ↓reduceIte] at hu hv; rw [hu, hv]; simp [huv]
      refine ⟨mem_allFinMaps _, ?_, ?_⟩
      · simp only [Bool.and_eq_true, decide_eq_true_eq]
        refine ⟨⟨(isHomBool_eq_true_iff H G _).mpr fun u v huv =>
                   hhom (p u) (p v) (hmap_edge H hHF u v huv).2,
                 (isNeqOnBool_eq_true_iff D _).mpr fun u v huv =>
                   hneq (p u) (p v) (hmap_edge D hd u v huv).2⟩, ?_⟩
        show (ψ (projContract a b hab a) == ψ (projContract a b hab b)) = true
        rw [projContract_a, projContract_b]; simp
      · funext i
        show ψ (projContract a b hab (deleteIdx b i)) = ψ i
        rw [projContract_deleteIdx]

/-! ### Step 4: Connected `injHomCount` → Connected `homCount` → All `homCount` → All `injHomCount` -/

theorem nonEdgeCount_addEdge_lt {k : Nat} (D : SimpleGraphN k) {a b : Fin k}
    (hab : a ≠ b) (hd : D.adj a b = false) :
    nonEdgeCount (addEdgeGraph D a b hab) < nonEdgeCount D := by
  unfold nonEdgeCount countWhere
  refine filter_length_lt_of_imp_of_witness ?_
    (x₀ := (a, b)) (mem_listProd.mpr ⟨mem_allFin a, mem_allFin b⟩) ?_ ?_
  · intro p _ hp
    simp only [Bool.and_eq_true] at hp ⊢
    refine ⟨hp.1, ?_⟩
    cases h : D.adj p.1 p.2
    · rfl
    · unfold addEdgeGraph at hp; simp [h] at hp
  · unfold addEdgeGraph; simp
  · have b : (a == b) = false :=
      Bool.eq_false_iff.mpr (fun e => hab (of_decide_eq_true (by simpa using e)))
    simp [b, hd]

theorem directedEdgeCount_removeEdge_lt {k : Nat} (D : SimpleGraphN k) {a b : Fin k}
    (hadj : D.adj a b = true) :
    directedEdgeCount (removeEdgeGraph D a b) < directedEdgeCount D := by
  unfold directedEdgeCount countWhere
  refine filter_length_lt_of_imp_of_witness ?_
    (x₀ := (a, b)) (mem_listProd.mpr ⟨mem_allFin a, mem_allFin b⟩) ?_ hadj
  · intro p _ hp
    unfold removeEdgeGraph at hp; dsimp only at hp
    simp only [Bool.and_eq_true] at hp
    exact hp.1.1
  · unfold removeEdgeGraph; simp

theorem exists_nonEdge_of_pos {k : Nat} {D : SimpleGraphN k}
    (hpos : 0 < nonEdgeCount D) :
    ∃ a b : Fin k, a ≠ b ∧ D.adj a b = false := by
  unfold nonEdgeCount countWhere at hpos
  cases hfilt : (listProd (allFin k) (allFin k)).filter
      (fun p => !(p.1 == p.2) && !D.adj p.1 p.2) with
  | nil => rw [hfilt] at hpos; simp at hpos
  | cons p _ =>
    have hp := (List.mem_filter.mp (hfilt ▸ List.mem_cons_self ..)).2
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hp
    refine ⟨p.1, p.2, fun e => ?_, hp.2⟩
    have b : (p.1 == p.2) = true := by simpa using decide_eq_true e
    rw [b] at hp; cases hp.1

theorem exists_edge_of_pos {k : Nat} {D : SimpleGraphN k}
    (hpos : 0 < directedEdgeCount D) :
    ∃ a b : Fin k, D.adj a b = true := by
  unfold directedEdgeCount countWhere at hpos
  cases hfilt : (listProd (allFin k) (allFin k)).filter (fun p => D.adj p.1 p.2) with
  | nil => rw [hfilt] at hpos; simp at hpos
  | cons p _ =>
    have hp := (List.mem_filter.mp (hfilt ▸ List.mem_cons_self ..)).2
    exact ⟨p.1, p.2, hp⟩

/-- Direction A: Equality of `injHomCount` on all connected graphs implies equality of
    `homCount` on all connected graphs (by nested strong induction on `k` and `nonEdgeCount D`). -/
theorem conn_injHom_imp_conn_hom {n₁ n₂ : Nat}
    {G₁ : SimpleGraphN n₁} {G₂ : SimpleGraphN n₂}
    (hinj : ∀ k (C : SimpleGraphN k), IsConnectedGraph C → injHomCount C G₁ = injHomCount C G₂) :
    ∀ k (H : SimpleGraphN k), IsConnectedGraph H → homCount H G₁ = homCount H G₂ := by
  have hmain : ∀ (kBound : Nat), ∀ k ≤ kBound, ∀ (neBound : Nat),
      ∀ (H D : SimpleGraphN k), IsConnectedGraph H → nonEdgeCount D ≤ neBound →
        constrainedHomCount H D G₁ = constrainedHomCount H D G₂ := by
    intro kBound
    induction kBound with
    | zero =>
      intro k hk _ H D hconn _
      have hk0 : k = 0 := by omega
      subst hk0
      rcases hconn.1 with ⟨u₀, _⟩
      exact u₀.elim0
    | succ kb ihk =>
      intro k hk neBound
      induction neBound with
      | zero =>
        intro H D hconn hne
        have hne0 : nonEdgeCount D = 0 := by omega
        -- Every distinct pair is an edge of D, so D = completeSimpleGraph k!
        have hD : D = completeSimpleGraph k := by
          apply SimpleGraphN.ext; funext u v
          by_cases huv : u = v
          · subst huv; simp [D.loopless, completeSimpleGraph]
          · have hfalse : ¬ (D.adj u v = false) := by
              intro hdf
              have hp : 0 < nonEdgeCount D := by
                refine countWhere_pos_of_witness (x₀ := (u, v))
                  (mem_listProd.mpr ⟨mem_allFin u, mem_allFin v⟩) ?_
                have b : (u == v) = false :=
                  Bool.eq_false_iff.mpr (fun e => huv (of_decide_eq_true (by simpa using e)))
                simp [b, hdf]
              omega
            have hdt : D.adj u v = true := by
              cases h : D.adj u v with
              | false => exact False.elim (hfalse h)
              | true => rfl
            unfold completeSimpleGraph
            have b : (u == v) = false :=
              Bool.eq_false_iff.mpr (fun e => huv (of_decide_eq_true (by simpa using e)))
            simp [hdt, b]
        rw [hD, constrainedHomCount_complete, constrainedHomCount_complete]
        exact hinj k H hconn
      | succ neb ihne =>
        intro H D hconn hne
        by_cases hpos : 0 < nonEdgeCount D
        · cases k with
          | zero => rcases hconn.1 with ⟨u₀, _⟩; exact u₀.elim0
          | succ m =>
            rcases exists_nonEdge_of_pos hpos with ⟨a, b, hab, hd⟩
            rw [constrainedHomCount_split H D G₁ a b hab hd,
                constrainedHomCount_split H D G₂ a b hab hd]
            have hlt := nonEdgeCount_addEdge_lt D hab hd
            have h1 := ihne H (addEdgeGraph D a b hab) hconn (by omega)
            rw [h1]
            congr 1
            by_cases hH : H.adj a b = true
            · simp [hH]
            · simp only [hH, ↓reduceDIte]
              have hHF := Bool.eq_false_iff.mpr hH
              have hconn_c := contractPairGraph_connected a b hab hHF hconn
              exact ihk m (by omega)
                (nonEdgeCount (contractPairGraph D a b hab hd))
                (contractPairGraph H a b hab hHF)
                (contractPairGraph D a b hab hd)
                hconn_c (Nat.le_refl _)
        · have hne0 : nonEdgeCount D = 0 := by omega
          exact ihne H D hconn (by omega)
  intro k H hconn
  rw [← constrainedHomCount_empty H G₁, ← constrainedHomCount_empty H G₂]
  exact hmain k k (Nat.le_refl k) (nonEdgeCount (emptySimpleGraph k)) H (emptySimpleGraph k)
    hconn (Nat.le_refl _)

/-! #### Component Peeling: Connected `homCount` Equality Implies ALL `homCount` Equality -/

/-- Enumerate the `true` elements of `S : Fin k → Bool` as an array/list of `Fin k`. -/
def subsetElems {k : Nat} (S : Fin k → Bool) : List (Fin k) :=
  (allFin k).filter S

theorem length_subsetElems {k : Nat} (S : Fin k → Bool) :
    (subsetElems S).length = subsetCard S := rfl

theorem nodup_subsetElems {k : Nat} (S : Fin k → Bool) : Nodup (subsetElems S) :=
  nodup_filter S (nodup_allFin k)

/-- `i`-th vertex of `S : Fin k → Bool` (`i : Fin (subsetCard S)`). -/
def enumSubset {k : Nat} (S : Fin k → Bool) (i : Fin (subsetCard S)) : Fin k :=
  (subsetElems S)[i.val]'(by rw [length_subsetElems]; exact i.isLt)

theorem getElem_eq_iff_of_nodup {α : Type u} {L : List α} (hnd : Nodup L)
    {i j : Nat} (hi : i < L.length) (hj : j < L.length) :
    L[i]'hi = L[j]'hj ↔ i = j := by
  induction L generalizing i j with
  | nil => cases hi
  | cons x xs ih =>
    cases hnd with
    | cons hx hxs =>
      cases i with
      | zero =>
        cases j with
        | zero => simp
        | succ j' =>
          simp only [List.getElem_cons_zero, List.getElem_cons_succ, Nat.zero_ne_add_one, iff_false]
          intro heq
          exact hx (heq ▸ List.getElem_mem _)
      | succ i' =>
        cases j with
        | zero =>
          simp only [List.getElem_cons_succ, List.getElem_cons_zero, Nat.add_one_ne_zero, iff_false]
          intro heq
          exact hx (heq.symm ▸ List.getElem_mem _)
        | succ j' =>
          simp only [List.getElem_cons_succ, Nat.succ.injEq]
          exact ih hxs _ _

theorem enumSubset_inj {k : Nat} (S : Fin k → Bool) {i j : Fin (subsetCard S)}
    (h : enumSubset S i = enumSubset S j) : i = j := by
  apply Fin.ext
  exact (getElem_eq_iff_of_nodup (nodup_subsetElems S) _ _).mp h

theorem enumSubset_mem {k : Nat} (S : Fin k → Bool) (i : Fin (subsetCard S)) :
    S (enumSubset S i) = true := by
  have hmem : enumSubset S i ∈ subsetElems S := List.getElem_mem _
  exact (List.mem_filter.mp hmem).2

theorem mem_range_enumSubset {k : Nat} (S : Fin k → Bool) {u : Fin k} (hu : S u = true) :
    ∃ i : Fin (subsetCard S), enumSubset S i = u := by
  have hmem : u ∈ subsetElems S := List.mem_filter.mpr ⟨mem_allFin u, hu⟩
  rcases List.getElem_of_mem hmem with ⟨idx, hlt, hget⟩
  refine ⟨⟨idx, by rw [← length_subsetElems]; exact hlt⟩, hget⟩

/-- Inverse index of `u : Fin k` (`S u = true`) in `subsetElems S`. -/
def unenumSubset {k : Nat} (S : Fin k → Bool) (u : Fin k) (hu : S u = true) : Fin (subsetCard S) :=
  match hfind : (allFin (subsetCard S)).find? (fun i => enumSubset S i == u) with
  | some i => i
  | none =>
    False.elim (by
      rcases mem_range_enumSubset S hu with ⟨i, hi⟩
      have := List.find?_eq_none.mp hfind i (mem_allFin i)
      simp [hi] at this)

theorem enumSubset_unenumSubset {k : Nat} (S : Fin k → Bool) (u : Fin k) (hu : S u = true) :
    enumSubset S (unenumSubset S u hu) = u := by
  unfold unenumSubset
  split
  · next _ hfind =>
    have hi := List.find?_some hfind
    exact of_decide_eq_true (by simpa using hi)
  · next => contradiction

theorem unenumSubset_enumSubset {k : Nat} (S : Fin k → Bool) (i : Fin (subsetCard S)) :
    unenumSubset S (enumSubset S i) (enumSubset_mem S i) = i :=
  enumSubset_inj S (enumSubset_unenumSubset S _ _)

/-- Induced subgraph `F[S]` as a `SimpleGraphN (subsetCard S)`. -/
def inducedSubgraph {k : Nat} (F : SimpleGraphN k) (S : Fin k → Bool) :
    SimpleGraphN (subsetCard S) where
  adj i j := F.adj (enumSubset S i) (enumSubset S j)
  loopless _ := F.loopless _
  symm _ _ := F.symm _ _

theorem homCount_component_split {m n : Nat} (F : SimpleGraphN (m + 1)) (G : SimpleGraphN n) :
    let S : Fin (m + 1) → Bool := fun u => reachBool F.adj (fun _ => true) 0 u
    let T : Fin (m + 1) → Bool := fun u => !S u
    IsConnectedGraph (inducedSubgraph F S) ∧
    subsetCard T < m + 1 ∧
    homCount F G = homCount (inducedSubgraph F S) G * homCount (inducedSubgraph F T) G := by
  intro S T
  have hS0 : S 0 = true := (reachBool_eq_true_iff F.adj _ 0 0).mpr (.refl rfl)
  -- No edge between S and T!
  have hno_cross : ∀ u v : Fin (m + 1), S u = true → S v = false → F.adj u v = false := by
    intro u v hSu hSv
    apply Bool.eq_false_iff.mpr; intro huv
    have hr0u := (reachBool_eq_true_iff F.adj _ 0 u).mp hSu
    have hr0v : ReachableIn F.adj (fun _ => true) 0 v :=
      hr0u.trans (.step rfl rfl huv (.refl rfl))
    have hSvT : S v = true := (reachBool_eq_true_iff F.adj _ 0 v).mpr hr0v
    rw [hSv] at hSvT; cases hSvT
  -- Every walk in `F` starting inside `S` stays inside `S` and lifts to `inducedSubgraph F S`!
  have hstay : ∀ u v : Fin (m + 1), ReachableIn F.adj (fun _ => true) u v →
      ∀ (hu : S u = true) (hv : S v = true),
        ReachableIn (inducedSubgraph F S).adj (fun _ => true)
          (unenumSubset S u hu) (unenumSubset S v hv) := by
    intro u v hr
    induction hr with
    | refl _ => intro hu _; exact .refl rfl
    | @step a b _ _ _ hab _ ih =>
      intro ha hc
      have hb : S b = true := by
        cases hSb : S b
        · have := hno_cross a b ha hSb; rw [hab] at this; cases this
        · rfl
      refine .step rfl rfl ?_ (ih hb hc)
      show F.adj (enumSubset S (unenumSubset S a ha)) (enumSubset S (unenumSubset S b hb)) = true
      rw [enumSubset_unenumSubset, enumSubset_unenumSubset]
      exact hab
  have hconnS : IsConnectedGraph (inducedSubgraph F S) := by
    refine ⟨⟨unenumSubset S 0 hS0, rfl⟩, fun i j _ _ => ?_⟩
    have hi := enumSubset_mem S i
    have hj := enumSubset_mem S j
    have hr0i := (reachBool_eq_true_iff F.adj _ 0 (enumSubset S i)).mp hi
    have hr0j := (reachBool_eq_true_iff F.adj _ 0 (enumSubset S j)).mp hj
    have hrij := (ReachableIn.symm_of_symm F.symm hr0i).trans hr0j
    have hm := hstay _ _ hrij hi hj
    rw [unenumSubset_enumSubset, unenumSubset_enumSubset] at hm
    exact hm
  have hT_lt : subsetCard T < m + 1 := by
    -- `T 0 = false`, whereas `(fun _ => true) 0 = true`, so `subsetCard T < m + 1`!
    have hlt := filter_length_lt_of_imp_of_witness (L := allFin (m + 1))
      (P := T) (Q := fun _ => true)
      (fun _ _ _ => rfl) (x₀ := 0) (mem_allFin 0)
      (by show (!S 0) = false; simp [hS0]) rfl
    rw [filter_const_true, length_allFin] at hlt
    exact hlt
  refine ⟨hconnS, hT_lt, ?_⟩
  unfold homCount
  rw [← countWhere_prod]
  refine countWhere_bij
    (fun φ => (fun i => φ (enumSubset S i), fun j => φ (enumSubset T j)))
    (fun p u => if hu : S u = true then p.1 (unenumSubset S u hu)
                else p.2 (unenumSubset T u (by show (!S u) = true; cases h : S u; rfl; exact False.elim (hu h))))
    (nodup_allFinMaps (m + 1) n)
    (nodup_listProd (nodup_allFinMaps (subsetCard S) n) (nodup_allFinMaps (subsetCard T) n))
    ?_ ?_
  · intro φ _ hφ
    have hhom := (isHomBool_eq_true_iff F G φ).mp hφ
    refine ⟨mem_listProd.mpr ⟨mem_allFinMaps _, mem_allFinMaps _⟩, ?_, ?_⟩
    · simp only [Bool.and_eq_true]
      exact ⟨(isHomBool_eq_true_iff _ G _).mpr fun i j hij => hhom _ _ hij,
             (isHomBool_eq_true_iff _ G _).mpr fun i j hij => hhom _ _ hij⟩
    · funext u
      by_cases hu : S u = true
      · simp [hu, enumSubset_unenumSubset]
      · simp [hu, enumSubset_unenumSubset]
  · rintro ⟨φ₁, φ₂⟩ _ hp
    simp only [Bool.and_eq_true] at hp
    have h1 := (isHomBool_eq_true_iff _ G φ₁).mp hp.1
    have h2 := (isHomBool_eq_true_iff _ G φ₂).mp hp.2
    refine ⟨mem_allFinMaps _, ?_, ?_⟩
    · rw [isHomBool_eq_true_iff]
      intro u v huv
      by_cases hu : S u = true <;> by_cases hv : S v = true
      · simp only [hu, hv, ↓reduceDIte]
        apply h1
        show F.adj (enumSubset S _) (enumSubset S _) = true
        rw [enumSubset_unenumSubset, enumSubset_unenumSubset]; exact huv
      · have hSvF : S v = false := Bool.eq_false_iff.mpr hv
        rw [hno_cross u v hu hSvF] at huv; cases huv
      · have hSuF : S u = false := Bool.eq_false_iff.mpr hu
        have hvu : F.adj v u = true := by rw [F.symm v u]; exact huv
        rw [hno_cross v u hv hSuF] at hvu; cases hvu
      · simp only [hu, hv, ↓reduceDIte]
        apply h2
        show F.adj (enumSubset T _) (enumSubset T _) = true
        rw [enumSubset_unenumSubset, enumSubset_unenumSubset]; exact huv
    · apply Prod.ext
      · funext i
        dsimp only
        have hi := enumSubset_mem S i
        simp only [hi, ↓reduceDIte]
        exact congrArg φ₁ (unenumSubset_enumSubset S i)
      · funext i
        dsimp only
        have hi := enumSubset_mem T i
        change (!S (enumSubset T i)) = true at hi
        have hnot : ¬ (S (enumSubset T i) = true) := by
          intro hS; simp [hS] at hi
        simp [hnot, unenumSubset_enumSubset]

theorem conn_hom_imp_all_hom {n₁ n₂ : Nat}
    {G₁ : SimpleGraphN n₁} {G₂ : SimpleGraphN n₂}
    (hhom : ∀ k (C : SimpleGraphN k), IsConnectedGraph C → homCount C G₁ = homCount C G₂) :
    ∀ k (F : SimpleGraphN k), homCount F G₁ = homCount F G₂ := by
  have hmain : ∀ kBound k, k ≤ kBound → ∀ F : SimpleGraphN k, homCount F G₁ = homCount F G₂ := by
    intro kBound
    induction kBound with
    | zero =>
      intro k hk F
      have hk0 : k = 0 := by omega
      subst hk0
      have h0 : ∀ {n} (G : SimpleGraphN n), homCount F G = 1 := by
        intro n G
        unfold homCount allFinMaps allFinFns countWhere
        have : isHomBool F G (fun i => i.elim0) = true :=
          (isHomBool_eq_true_iff F G _).mpr fun u => u.elim0
        simp [this]
      rw [h0 G₁, h0 G₂]
    | succ kb ih =>
      intro k hk F
      cases k with
      | zero => exact ih 0 (Nat.zero_le _) F
      | succ m =>
        rcases homCount_component_split F G₁ with ⟨hconnS, hTlt, hsplit1⟩
        rcases homCount_component_split F G₂ with ⟨_, _, hsplit2⟩
        rw [hsplit1, hsplit2,
            hhom _ _ hconnS,
            ih _ (by omega) _]
  intro k F
  exact hmain k k (Nat.le_refl k) F

/-- Direction B: Equality of `homCount` on ALL graphs implies equality of `injHomCount`
    on ALL graphs (by nested strong induction on `k` and `directedEdgeCount D`). -/
theorem all_hom_imp_all_injHom {n₁ n₂ : Nat}
    {G₁ : SimpleGraphN n₁} {G₂ : SimpleGraphN n₂}
    (hhom : ∀ k (F : SimpleGraphN k), homCount F G₁ = homCount F G₂) :
    ∀ k (F : SimpleGraphN k), injHomCount F G₁ = injHomCount F G₂ := by
  have hmain : ∀ (kBound : Nat), ∀ k ≤ kBound, ∀ (eBound : Nat),
      ∀ (F D : SimpleGraphN k), directedEdgeCount D ≤ eBound →
        constrainedHomCount F D G₁ = constrainedHomCount F D G₂ := by
    intro kBound
    induction kBound with
    | zero =>
      intro k hk _ F D _
      have hk0 : k = 0 := by omega
      subst hk0
      have hD : D = emptySimpleGraph 0 := SimpleGraphN.ext (funext fun u => u.elim0)
      rw [hD, constrainedHomCount_empty, constrainedHomCount_empty]
      exact hhom 0 F
    | succ kb ihk =>
      intro k hk eBound
      induction eBound with
      | zero =>
        intro F D he
        have he0 : directedEdgeCount D = 0 := by omega
        have hD : D = emptySimpleGraph k := by
          apply SimpleGraphN.ext; funext u v
          cases h : D.adj u v
          · rfl
          · exfalso
            have hp : 0 < directedEdgeCount D :=
              countWhere_pos_of_witness (x₀ := (u, v))
                (mem_listProd.mpr ⟨mem_allFin u, mem_allFin v⟩) h
            omega
        rw [hD, constrainedHomCount_empty, constrainedHomCount_empty]
        exact hhom k F
      | succ eb ihe =>
        intro F D he
        by_cases hpos : 0 < directedEdgeCount D
        · cases k with
          | zero =>
            rcases exists_edge_of_pos hpos with ⟨a, _⟩
            exact a.elim0
          | succ m =>
            rcases exists_edge_of_pos hpos with ⟨a, b, hadj⟩
            rcases addEdge_removeEdge D hadj with ⟨hab, hD_eq⟩
            let D' := removeEdgeGraph D a b
            have hd' : D'.adj a b = false := by unfold D' removeEdgeGraph; simp
            have hlt := directedEdgeCount_removeEdge_lt D hadj
            have hrec1 := constrainedHomCount_split F D' G₁ a b hab hd'
            have hrec2 := constrainedHomCount_split F D' G₂ a b hab hd'
            rw [hD_eq] at hrec1 hrec2
            have hbase := ihe F D' (by dsimp [D']; omega)
            have htail :
                (if hF : F.adj a b = true then 0
                 else constrainedHomCount
                   (contractPairGraph F a b hab (Bool.eq_false_iff.mpr hF))
                   (contractPairGraph D' a b hab hd') G₁) =
                (if hF : F.adj a b = true then 0
                 else constrainedHomCount
                   (contractPairGraph F a b hab (Bool.eq_false_iff.mpr hF))
                   (contractPairGraph D' a b hab hd') G₂) := by
              by_cases hF : F.adj a b = true
              · simp [hF]
              · simp only [hF, ↓reduceDIte]
                exact ihk m (by omega)
                  (directedEdgeCount (contractPairGraph D' a b hab hd'))
                  (contractPairGraph F a b hab (Bool.eq_false_iff.mpr hF))
                  (contractPairGraph D' a b hab hd')
                  (Nat.le_refl _)
            omega
        · exact ihe F D (by omega)
  intro k F
  rw [← constrainedHomCount_complete F G₁, ← constrainedHomCount_complete F G₂]
  exact hmain k k (Nat.le_refl k) (directedEdgeCount (completeSimpleGraph k)) F
    (completeSimpleGraph k) (Nat.le_refl _)

/-! ### Step 5: Lovász's Endgame (`all_injHom_imp_graphIso`) -/

theorem filter_eq_self_of_all {α : Type u} (L : List α) (P : α → Bool)
    (h : ∀ x ∈ L, P x = true) : L.filter P = L := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
    have hx := h x (List.mem_cons_self ..)
    have ih' := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp [List.filter, hx, ih']

theorem injHomCount_K1 {n : Nat} (G : SimpleGraphN n) :
    injHomCount (emptySimpleGraph 1) G = n := by
  unfold injHomCount countWhere
  have hall : ∀ φ ∈ allFinMaps 1 n, (isInjBool φ && isHomBool (emptySimpleGraph 1) G φ) = true := by
    intro φ _
    simp only [Bool.and_eq_true]
    exact ⟨(isInjBool_eq_true_iff φ).mpr fun i j _ => Fin.ext (by omega),
           (isHomBool_eq_true_iff _ G φ).mpr fun _ _ h => by cases h⟩
  rw [filter_eq_self_of_all _ _ hall]
  unfold allFinMaps allFinFns
  change ((listProd (allFin n) [fun i : Fin 0 => i.elim0]).map _).length = n
  have hlen : ∀ (L : List (Fin n)) (u₀ : Fin 0 → Fin n),
      (listProd L [u₀]).length = L.length := by
    intro L u₀
    induction L with
    | nil => rfl
    | cons _ xs ih => simp [listProd, ih]
  rw [List.length_map, hlen, length_allFin]

theorem injHomCount_K2 {n : Nat} (G : SimpleGraphN n) :
    injHomCount (completeSimpleGraph 2) G = directedEdgeCount G := by
  unfold injHomCount directedEdgeCount
  refine countWhere_bij
    (fun φ => (φ 0, φ 1))
    (fun p (i : Fin 2) => if i.val = 0 then p.1 else p.2)
    (nodup_allFinMaps 2 n)
    (nodup_listProd (nodup_allFin n) (nodup_allFin n))
    ?_ ?_
  · intro φ _ hφ
    simp only [Bool.and_eq_true] at hφ
    have hhom := (isHomBool_eq_true_iff _ G φ).mp hφ.2
    have h01 : (completeSimpleGraph 2).adj 0 1 = true := by decide
    refine ⟨mem_listProd.mpr ⟨mem_allFin _, mem_allFin _⟩, hhom 0 1 h01, ?_⟩
    funext i
    have hil := i.isLt
    by_cases hi0 : i.val = 0
    · have : i = 0 := Fin.ext hi0; subst this; simp
    · have : i = 1 := Fin.ext (by omega); subst this; simp
  · rintro ⟨u, v⟩ _ huv
    have hne : u ≠ v := fun e => by subst e; rw [G.loopless] at huv; cases huv
    refine ⟨mem_allFinMaps _, ?_, by simp⟩
    simp only [Bool.and_eq_true]
    refine ⟨(isInjBool_eq_true_iff _).mpr ?_, (isHomBool_eq_true_iff _ G _).mpr ?_⟩
    · intro i j hij
      have hil := i.isLt; have hjl := j.isLt
      by_cases hi0 : i.val = 0 <;> by_cases hj0 : j.val = 0
      · exact Fin.ext (by omega)
      · simp [hi0, hj0] at hij; exact False.elim (hne hij)
      · simp [hi0, hj0] at hij; exact False.elim (hne hij.symm)
      · exact Fin.ext (by omega)
    · intro i j hij
      have hil := i.isLt; have hjl := j.isLt
      by_cases hi0 : i.val = 0 <;> by_cases hj0 : j.val = 0
      · have : i = j := Fin.ext (by omega); subst this
        rw [(completeSimpleGraph 2).loopless] at hij; cases hij
      · simp [hi0, hj0, huv]
      · simp only [hi0, hj0, ↓reduceIte]; rw [G.symm v u]; exact huv
      · have : i = j := Fin.ext (by omega); subst this
        rw [(completeSimpleGraph 2).loopless] at hij; cases hij

theorem all_injHom_imp_graphIso {n₁ n₂ : Nat}
    {G₁ : SimpleGraphN n₁} {G₂ : SimpleGraphN n₂}
    (hinj : ∀ k (F : SimpleGraphN k), injHomCount F G₁ = injHomCount F G₂) :
    GraphIso G₁ G₂ := by
  have hn : n₁ = n₂ := by
    rw [← injHomCount_K1 G₁, ← injHomCount_K1 G₂]
    exact hinj 1 (emptySimpleGraph 1)
  subst hn
  have hedge : directedEdgeCount G₁ = directedEdgeCount G₂ := by
    rw [← injHomCount_K2 G₁, ← injHomCount_K2 G₂]
    exact hinj 2 (completeSimpleGraph 2)
  have hpos1 : 0 < injHomCount G₁ G₁ := by
    refine countWhere_pos_of_witness (x₀ := id) (mem_allFinMaps id) ?_
    simp only [Bool.and_eq_true]
    exact ⟨(isInjBool_eq_true_iff id).mpr fun _ _ h => h,
           (isHomBool_eq_true_iff G₁ G₁ id).mpr fun _ _ h => h⟩
  have hpos2 : 0 < injHomCount G₁ G₂ := hinj n₁ G₁ ▸ hpos1
  unfold injHomCount countWhere at hpos2
  cases hfilt : (allFinMaps n₁ n₁).filter (fun φ => isInjBool φ && isHomBool G₁ G₂ φ) with
  | nil => rw [hfilt] at hpos2; simp at hpos2
  | cons φ _ =>
    have hφ := (List.mem_filter.mp (hfilt ▸ List.mem_cons_self ..)).2
    simp only [Bool.and_eq_true] at hφ
    have hinjφ := (isInjBool_eq_true_iff φ).mp hφ.1
    have hhomφ := (isHomBool_eq_true_iff G₁ G₂ φ).mp hφ.2
    -- Since φ : Fin n₁ → Fin n₁ is injective, every y ∈ Fin n₁ lies in imageMask φ!
    have hmemφ : ∀ y : Fin n₁, imageMask φ y = true := by
      intro y
      by_cases hy : imageMask φ y = true
      · exact hy
      · exfalso
        have hyF := Bool.eq_false_iff.mpr hy
        have hnd := nodup_map_of_inj_on (nodup_allFin n₁) (fun a _ b _ h => hinjφ a b h)
        have hsub : ∀ z ∈ (allFin n₁).map φ, z ∈ removeOne y (allFin n₁) := by
          intro z hz
          rcases List.mem_map.mp hz with ⟨i, _, rfl⟩
          refine mem_removeOne_of_ne ?_ (mem_allFin (φ i))
          intro heq
          have : imageMask φ y = true := (imageMask_eq_true_iff φ y).mpr ⟨i, heq⟩
          rw [hyF] at this; cases this
        have hle := nodup_length_le_of_subset hnd hsub
        have hrem := length_removeOne_of_mem (mem_allFin y)
        rw [List.length_map, length_allFin] at hle
        rw [length_allFin] at hrem
        omega
    let ψ : Fin n₁ → Fin n₁ := pullbackPerm φ id
    have hφψ : ∀ y, φ (ψ y) = y := pullbackPerm_spec (fun y => hmemφ y)
    have hψφ : ∀ x, ψ (φ x) = x := fun x => hinjφ _ _ (hφψ (φ x))
    -- Reindex `directedEdgeCount G₂` along `(u, v) ↦ (φ u, φ v)`
    have hreidx : directedEdgeCount G₂ =
        countWhere (listProd (allFin n₁) (allFin n₁)) (fun p => G₂.adj (φ p.1) (φ p.2)) := by
      unfold directedEdgeCount
      refine countWhere_bij
        (fun p => (ψ p.1, ψ p.2))
        (fun q => (φ q.1, φ q.2))
        (nodup_listProd (nodup_allFin n₁) (nodup_allFin n₁))
        (nodup_listProd (nodup_allFin n₁) (nodup_allFin n₁)) ?_ ?_
      · rintro ⟨a, b⟩ _ hab
        refine ⟨mem_listProd.mpr ⟨mem_allFin _, mem_allFin _⟩, ?_, by simp [hφψ]⟩
        dsimp only; rw [hφψ, hφψ]; exact hab
      · rintro ⟨u, v⟩ _ huv
        exact ⟨mem_listProd.mpr ⟨mem_allFin _, mem_allFin _⟩, huv, by simp [hψφ]⟩
    -- Prove `G₁.adj u v = G₂.adj (φ u) (φ v)` by edge-count equality!
    refine ⟨{
      toFun := φ
      invFun := ψ
      left_inv := hψφ
      right_inv := hφψ
      map_adj := fun u v => by
        cases h1 : G₁.adj u v
        · cases h2 : G₂.adj (φ u) (φ v)
          · rfl
          · exfalso
            have hlt := filter_length_lt_of_imp_of_witness
              (L := listProd (allFin n₁) (allFin n₁))
              (P := fun p => G₁.adj p.1 p.2)
              (Q := fun p => G₂.adj (φ p.1) (φ p.2))
              (fun p _ hp => hhomφ p.1 p.2 hp)
              (x₀ := (u, v))
              (mem_listProd.mpr ⟨mem_allFin u, mem_allFin v⟩)
              h1 h2
            change directedEdgeCount G₁ < countWhere _ _ at hlt
            rw [← hreidx] at hlt
            omega
        · exact (hhomφ u v h1).symm
    }⟩

/-! ### Master Theorems for Reading III (Induced & Non-Induced Connected Iso Counts) -/

/-- **Theorem III.A (Induced Connected Subgraph Reconstruction):**
    If `indIsoCount H G₁ = indIsoCount H G₂` for every connected graph `H`,
    then `G₁ ≅ G₂`! -/
theorem conn_indIsoCount_imp_graphIso {n₁ n₂ : Nat}
    {G₁ : SimpleGraphN n₁} {G₂ : SimpleGraphN n₂}
    (h : ∀ k (H : SimpleGraphN k), IsConnectedGraph H → indIsoCount H G₁ = indIsoCount H G₂) :
    GraphIso G₁ G₂ := by
  have hemb : ∀ k (H : SimpleGraphN k), IsConnectedGraph H →
      indEmbCount H G₁ = indEmbCount H G₂ := by
    intro k H hconn
    rw [← autCount_mul_indIsoCount H G₁, ← autCount_mul_indIsoCount H G₂, h k H hconn]
  exact all_injHom_imp_graphIso
    (all_hom_imp_all_injHom (conn_hom_imp_all_hom (conn_injHom_imp_conn_hom
      (conn_indEmb_imp_conn_injHom hemb))))

/-- **Theorem III.B (Non-Induced Connected Subgraph Reconstruction):**
    If `subIsoCount H G₁ = subIsoCount H G₂` for every connected graph `H`,
    then `G₁ ≅ G₂`! -/
theorem conn_subIsoCount_imp_graphIso {n₁ n₂ : Nat}
    {G₁ : SimpleGraphN n₁} {G₂ : SimpleGraphN n₂}
    (h : ∀ k (H : SimpleGraphN k), IsConnectedGraph H → subIsoCount H G₁ = subIsoCount H G₂) :
    GraphIso G₁ G₂ := by
  have hinj : ∀ k (H : SimpleGraphN k), IsConnectedGraph H →
      injHomCount H G₁ = injHomCount H G₂ := by
    intro k H hconn
    rw [← autCount_mul_subIsoCount H G₁, ← autCount_mul_subIsoCount H G₂, h k H hconn]
  exact all_injHom_imp_graphIso
    (all_hom_imp_all_injHom (conn_hom_imp_all_hom (conn_injHom_imp_conn_hom hinj)))

/-- **Corollary III.A:** No two graphs of ANY order `n` can have identical connected induced
    subgraph isomorphism counts `N_ind(H, ·)` while differing in adjacency spectrum! -/
theorem no_conn_indIsoCount_spectrum_separation :
    ¬ ∃ (n : Nat) (G₁ G₂ : SimpleGraphN n),
      (∀ k (H : SimpleGraphN k), IsConnectedGraph H → indIsoCount H G₁ = indIsoCount H G₂) ∧
      charPoly G₁ ≠ charPoly G₂ := by
  rintro ⟨_, G₁, G₂, hcounts, hneq⟩
  exact hneq (conn_indIsoCount_imp_graphIso hcounts).charPoly_eq

/-- **Corollary III.B:** No two graphs of ANY order `n` can have identical connected subgraph
    isomorphism counts `N_sub(H, ·)` while differing in adjacency spectrum! -/
theorem no_conn_subIsoCount_spectrum_separation :
    ¬ ∃ (n : Nat) (G₁ G₂ : SimpleGraphN n),
      (∀ k (H : SimpleGraphN k), IsConnectedGraph H → subIsoCount H G₁ = subIsoCount H G₂) ∧
      charPoly G₁ ≠ charPoly G₂ := by
  rintro ⟨_, G₁, G₂, hcounts, hneq⟩
  exact hneq (conn_subIsoCount_imp_graphIso hcounts).charPoly_eq

end Conjecture00000003970
