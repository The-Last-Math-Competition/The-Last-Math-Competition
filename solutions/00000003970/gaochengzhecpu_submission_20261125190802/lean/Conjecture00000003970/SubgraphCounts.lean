/-
  Conjecture 00000003970 — Subgraph Count Vectors (Induced & Edge-Subset)
  and Graph Isomorphism Invariance
  Pure Core Lean 4.19.0 (zero external dependencies).
-/

import Conjecture00000003970.CharPoly

namespace Conjecture00000003970

/-! ### Reading I: Connected Induced Subgraph Count Vector `c^ind(G)` -/

/-- Number of vertex subsets `S ⊆ Fin n` of order `|S| = k` whose induced subgraph `G[S]`
    is connected (`IsConnectedSubgraph G.adj S`). -/
def connInducedCount {n : Nat} (G : SimpleGraphN n) (k : Nat) : Nat :=
  countWhere (allSubsets n) (fun S => decide (subsetCard S = k) && isConnectedSubgraphBool G.adj S)

/-- Connected induced subgraph count vector `(c^ind_1(G), ..., c^ind_n(G))`. -/
def connInducedVec {n : Nat} (G : SimpleGraphN n) : List Nat :=
  (List.range n).map (fun i => connInducedCount G (i + 1))

theorem length_connInducedVec {n : Nat} (G : SimpleGraphN n) :
    (connInducedVec G).length = n := by
  simp [connInducedVec]

/-- Specification theorem linking `connInducedCount` directly to propositional `IsConnectedSubgraph`. -/
theorem connInducedCount_spec {n : Nat} (G : SimpleGraphN n) (k : Nat) :
    connInducedCount G k =
      ((allSubsets n).filter (fun S =>
        decide (subsetCard S = k ∧ IsConnectedSubgraph G.adj S))).length := by
  unfold connInducedCount countWhere
  congr 1
  refine List.filter_congr ?_
  intro S _
  by_cases hk : subsetCard S = k
  · simp only [hk, decide_true, Bool.true_and, true_and]
    by_cases hc : IsConnectedSubgraph G.adj S
    · have hb := (isConnectedSubgraphBool_eq_true_iff G.adj S).mpr hc
      simp [hc, hb]
    · have hb : isConnectedSubgraphBool G.adj S = false :=
        Bool.eq_false_iff.mpr (fun h => hc ((isConnectedSubgraphBool_eq_true_iff G.adj S).mp h))
      simp [hc, hb]
  · simp [hk]

theorem IsoWitness.subsetCard_map {n m : Nat} {G₁ : SimpleGraphN n} {G₂ : SimpleGraphN m}
    (w : IsoWitness G₁ G₂) (S : Fin n → Bool) :
    subsetCard (fun y => S (w.invFun y)) = subsetCard S := by
  unfold subsetCard
  refine countWhere_bij w.invFun w.toFun (nodup_allFin m) (nodup_allFin n) ?_ ?_
  · intro y _ hy
    exact ⟨mem_allFin _, hy, w.right_inv y⟩
  · intro x _ hx
    refine ⟨mem_allFin _, ?_, w.left_inv x⟩
    rw [w.left_inv x]
    exact hx

theorem IsoWitness.reachableIn_map {n m : Nat} {G₁ : SimpleGraphN n} {G₂ : SimpleGraphN m}
    (w : IsoWitness G₁ G₂) {S : Fin n → Bool} {u v : Fin n}
    (h : ReachableIn G₁.adj S u v) :
    ReachableIn G₂.adj (fun y => S (w.invFun y)) (w.toFun u) (w.toFun v) := by
  induction h with
  | @refl z hSz =>
    refine .refl ?_
    rw [w.left_inv z]; exact hSz
  | @step a b _ hSa hSb hab _ ih =>
    refine .step ?_ ?_ ?_ ih
    · rw [w.left_inv a]; exact hSa
    · rw [w.left_inv b]; exact hSb
    · rw [← w.map_adj a b]; exact hab

theorem IsoWitness.isConnectedSubgraph_map {n m : Nat} {G₁ : SimpleGraphN n} {G₂ : SimpleGraphN m}
    (w : IsoWitness G₁ G₂) (S : Fin n → Bool) :
    IsConnectedSubgraph G₁.adj S ↔
      IsConnectedSubgraph G₂.adj (fun y => S (w.invFun y)) := by
  constructor
  · rintro ⟨⟨u₀, hu₀⟩, hconn⟩
    refine ⟨⟨w.toFun u₀, by dsimp; rw [w.left_inv]; exact hu₀⟩, ?_⟩
    intro y₁ y₂ hy₁ hy₂
    have hr := w.reachableIn_map (hconn (w.invFun y₁) (w.invFun y₂) hy₁ hy₂)
    rw [w.right_inv y₁, w.right_inv y₂] at hr
    exact hr
  · rintro ⟨⟨y₀, hy₀⟩, hconn⟩
    refine ⟨⟨w.invFun y₀, hy₀⟩, ?_⟩
    intro u₁ u₂ hu₁ hu₂
    have hy₁ : (fun y => S (w.invFun y)) (w.toFun u₁) = true := by
      dsimp; rw [w.left_inv]; exact hu₁
    have hy₂ : (fun y => S (w.invFun y)) (w.toFun u₂) = true := by
      dsimp; rw [w.left_inv]; exact hu₂
    have hr := w.symm.reachableIn_map (hconn (w.toFun u₁) (w.toFun u₂) hy₁ hy₂)
    have hS : (fun x => S (w.invFun (w.symm.invFun x))) = S := by
      funext x; show S (w.invFun (w.toFun x)) = S x; rw [w.left_inv]
    change ReachableIn G₁.adj (fun x => S (w.invFun (w.symm.invFun x)))
      (w.invFun (w.toFun u₁)) (w.invFun (w.toFun u₂)) at hr
    rw [hS, w.left_inv, w.left_inv] at hr
    exact hr

theorem IsoWitness.connInducedCount_eq {n m : Nat} {G₁ : SimpleGraphN n} {G₂ : SimpleGraphN m}
    (w : IsoWitness G₁ G₂) (k : Nat) :
    connInducedCount G₁ k = connInducedCount G₂ k := by
  unfold connInducedCount
  refine countWhere_bij
    (fun S y => S (w.invFun y))
    (fun T x => T (w.toFun x))
    (nodup_allSubsets n) (nodup_allSubsets m) ?_ ?_
  · intro S _ hS
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hS
    refine ⟨mem_allSubsets _, ?_, ?_⟩
    · simp only [Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨(w.subsetCard_map S).trans hS.1, ?_⟩
      exact (isConnectedSubgraphBool_eq_true_iff _ _).mpr
        ((w.isConnectedSubgraph_map S).mp ((isConnectedSubgraphBool_eq_true_iff _ _).mp hS.2))
    · funext x; exact congrArg S (w.left_inv x)
  · intro T _ hT
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hT
    refine ⟨mem_allSubsets _, ?_, ?_⟩
    · simp only [Bool.and_eq_true, decide_eq_true_eq]
      have hcard := w.symm.subsetCard_map T
      change subsetCard (fun x => T (w.toFun x)) = subsetCard T at hcard
      refine ⟨hcard.trans hT.1, ?_⟩
      have hconn := (w.symm.isConnectedSubgraph_map T).mp
        ((isConnectedSubgraphBool_eq_true_iff _ _).mp hT.2)
      exact (isConnectedSubgraphBool_eq_true_iff _ _).mpr hconn
    · funext y; exact congrArg T (w.right_inv y)

theorem GraphIso.connInducedVec_eq {n m : Nat} {G₁ : SimpleGraphN n} {G₂ : SimpleGraphN m}
    (h : GraphIso G₁ G₂) : connInducedVec G₁ = connInducedVec G₂ := by
  rcases h with ⟨w⟩
  unfold connInducedVec
  have hrange : List.range n = List.range m := congrArg List.range w.card_eq
  rw [hrange]
  exact List.map_congr_left fun i _ => w.connInducedCount_eq (i + 1)

/-! ### Reading II: Connected Edge-Subset Subgraph Count Vector `c^sub(G)` & Total `s^sub(G)` -/

/-- Empty graph on `0` vertices. -/
def emptyGraph0 : SimpleGraphN 0 where
  adj := fun u => u.elim0
  loopless := fun u => u.elim0
  symm := fun u => u.elim0

/-- Extend `G₀ : SimpleGraphN k` to `Fin (k + 1)` by attaching vertex `.last k` to `nb : Fin k → Bool`. -/
def extendGraph {k : Nat} (G₀ : SimpleGraphN k) (nb : Fin k → Bool) : SimpleGraphN (k + 1) where
  adj u v :=
    if hu : u.val < k then
      if hv : v.val < k then G₀.adj ⟨u.val, hu⟩ ⟨v.val, hv⟩
      else nb ⟨u.val, hu⟩
    else
      if hv : v.val < k then nb ⟨v.val, hv⟩
      else false
  loopless u := by
    by_cases hu : u.val < k
    · simp [hu, G₀.loopless ⟨u.val, hu⟩]
    · simp [hu]
  symm u v := by
    by_cases hu : u.val < k <;> by_cases hv : v.val < k
    · simp [hu, hv, G₀.symm]
    · simp [hu, hv]
    · simp [hu, hv]
    · simp [hu, hv]

/-- Induced subgraph of `G : SimpleGraphN (k + 1)` on the first `k` vertices `Fin k`. -/
def initGraph {k : Nat} (G : SimpleGraphN (k + 1)) : SimpleGraphN k where
  adj i j := G.adj i.castSucc j.castSucc
  loopless i := G.loopless i.castSucc
  symm i j := G.symm i.castSucc j.castSucc

/-- Neighbor indicator of `.last k` on `Fin k`. -/
def lastNeighbors {k : Nat} (G : SimpleGraphN (k + 1)) (i : Fin k) : Bool :=
  G.adj i.castSucc (.last k)

theorem extendGraph_init_last {k : Nat} (G : SimpleGraphN (k + 1)) :
    extendGraph (initGraph G) (lastNeighbors G) = G := by
  apply SimpleGraphN.ext
  funext u v
  unfold extendGraph initGraph lastNeighbors
  dsimp only
  have hul := u.isLt
  have hvl := v.isLt
  by_cases hu : u.val < k <;> by_cases hv : v.val < k
  · simp only [hu, hv, ↓reduceDIte]
    rfl
  · simp only [hu, hv, ↓reduceDIte]
    have hvl' : v = .last k := Fin.ext (by simp [Fin.last]; omega)
    rw [hvl']; rfl
  · simp only [hu, hv, ↓reduceDIte]
    have hul' : u = .last k := Fin.ext (by simp [Fin.last]; omega)
    rw [hul', G.symm (.last k) v]; rfl
  · simp only [hu, hv, ↓reduceDIte]
    have hul' : u = .last k := Fin.ext (by simp [Fin.last]; omega)
    have hvl' : v = .last k := Fin.ext (by simp [Fin.last]; omega)
    rw [hul', hvl', G.loopless]

theorem extendGraph_inj {k : Nat} {G₁ G₂ : SimpleGraphN k} {nb₁ nb₂ : Fin k → Bool}
    (h : extendGraph G₁ nb₁ = extendGraph G₂ nb₂) : G₁ = G₂ ∧ nb₁ = nb₂ := by
  have hadj := congrArg SimpleGraphN.adj h
  constructor
  · apply SimpleGraphN.ext
    funext i j
    have := congrFun (congrFun hadj i.castSucc) j.castSucc
    simpa [extendGraph, i.isLt, j.isLt] using this
  · funext i
    have hnot : ¬ ((Fin.last k).val < k) := by simp [Fin.last]
    have := congrFun (congrFun hadj i.castSucc) (.last k)
    simpa [extendGraph, i.isLt, hnot] using this

/-- Complete duplicate-free enumeration of all `SimpleGraphN n`. -/
def allSimpleGraphs : (n : Nat) → List (SimpleGraphN n)
  | 0 => [emptyGraph0]
  | k + 1 =>
    (listProd (allSimpleGraphs k) (allSubsets k)).map (fun p => extendGraph p.1 p.2)

theorem mem_allSimpleGraphs : ∀ {n : Nat} (G : SimpleGraphN n), G ∈ allSimpleGraphs n
  | 0, G => by
    have : G = emptyGraph0 := SimpleGraphN.ext (funext fun u => u.elim0)
    rw [this]
    exact List.mem_singleton_self _
  | k + 1, G => by
    unfold allSimpleGraphs
    rw [List.mem_map]
    refine ⟨(initGraph G, lastNeighbors G), ?_, extendGraph_init_last G⟩
    exact mem_listProd.mpr ⟨mem_allSimpleGraphs (initGraph G), mem_allSubsets _⟩

theorem nodup_allSimpleGraphs : ∀ (n : Nat), Nodup (allSimpleGraphs n)
  | 0 => .cons (by simp) .nil
  | k + 1 => by
    unfold allSimpleGraphs
    refine nodup_map_of_inj_on (nodup_listProd (nodup_allSimpleGraphs k) (nodup_allSubsets k)) ?_
    intro p₁ _ p₂ _ heq
    have ⟨h1, h2⟩ := extendGraph_inj heq
    cases p₁; cases p₂
    simp_all

/-- Boolean predicate testing whether `H` is an edge-subset subgraph of `G` supported on `S`:
    every edge of `H` connects two vertices in `S` and is present in `G`. -/
def isSpanningSubgraphOn {n : Nat} (G : SimpleGraphN n) (S : Fin n → Bool)
    (H : SimpleGraphN n) : Bool :=
  (allFin n).all (fun u => (allFin n).all (fun v => !H.adj u v || (S u && S v && G.adj u v)))

theorem isSpanningSubgraphOn_eq_true_iff {n : Nat} (G : SimpleGraphN n) (S : Fin n → Bool)
    (H : SimpleGraphN n) :
    isSpanningSubgraphOn G S H = true ↔
      (∀ u v : Fin n, H.adj u v = true → S u = true ∧ S v = true ∧ G.adj u v = true) := by
  unfold isSpanningSubgraphOn
  constructor
  · intro hall u v huv
    have h1 := List.all_eq_true.mp hall u (mem_allFin u)
    have h2 := List.all_eq_true.mp h1 v (mem_allFin v)
    simp only [huv, Bool.not_true, Bool.false_or, Bool.and_eq_true] at h2
    exact ⟨h2.1.1, h2.1.2, h2.2⟩
  · intro h
    apply List.all_eq_true.mpr
    intro u _
    apply List.all_eq_true.mpr
    intro v _
    cases huv : H.adj u v
    · simp
    · rcases h u v huv with ⟨h1, h2, h3⟩
      simp [h1, h2, h3]

/-- Number of ALL edge-subset spanning subgraphs `(S, H)` of `G[S]`. -/
def spanningSubgraphCount {n : Nat} (G : SimpleGraphN n) (S : Fin n → Bool) : Nat :=
  countWhere (allSimpleGraphs n) (fun H => isSpanningSubgraphOn G S H)

/-- Number of CONNECTED edge-subset spanning subgraphs `(S, H)` of `G[S]`. -/
def connSpanningSubgraphCount {n : Nat} (G : SimpleGraphN n) (S : Fin n → Bool) : Nat :=
  countWhere (allSimpleGraphs n)
    (fun H => isSpanningSubgraphOn G S H && isConnectedSubgraphBool H.adj S)

/-- Total number of edge-subset subgraphs `(S, H)` of `G` of vertex order `|S| = k`. -/
def allEdgeSubgraphCount {n : Nat} (G : SimpleGraphN n) (k : Nat) : Nat :=
  listSum (((allSubsets n).filter (fun S => subsetCard S == k)).map (spanningSubgraphCount G))

/-- Number of CONNECTED edge-subset subgraphs `(S, H)` of `G` of vertex order `|S| = k`. -/
def connEdgeSubgraphCount {n : Nat} (G : SimpleGraphN n) (k : Nat) : Nat :=
  listSum (((allSubsets n).filter (fun S => subsetCard S == k)).map (connSpanningSubgraphCount G))

/-- Unrestricted (total) subgraph count vector `(s^sub_1(G), ..., s^sub_n(G))`. -/
def allEdgeSubgraphVec {n : Nat} (G : SimpleGraphN n) : List Nat :=
  (List.range n).map (fun i => allEdgeSubgraphCount G (i + 1))

/-- Connected edge-subset subgraph count vector `(c^sub_1(G), ..., c^sub_n(G))`. -/
def connEdgeSubgraphVec {n : Nat} (G : SimpleGraphN n) : List Nat :=
  (List.range n).map (fun i => connEdgeSubgraphCount G (i + 1))

/-- Pushforward a `SimpleGraphN n` along an `IsoWitness G₁ G₂`. -/
def pushGraph {n m : Nat} {G₁ : SimpleGraphN n} {G₂ : SimpleGraphN m}
    (w : IsoWitness G₁ G₂) (H : SimpleGraphN n) : SimpleGraphN m where
  adj y₁ y₂ := H.adj (w.invFun y₁) (w.invFun y₂)
  loopless y := H.loopless (w.invFun y)
  symm y₁ y₂ := H.symm (w.invFun y₁) (w.invFun y₂)

def IsoWitness.toPushGraph {n m : Nat} {G₁ : SimpleGraphN n} {G₂ : SimpleGraphN m}
    (w : IsoWitness G₁ G₂) (H : SimpleGraphN n) :
    IsoWitness H (pushGraph w H) where
  toFun := w.toFun
  invFun := w.invFun
  left_inv := w.left_inv
  right_inv := w.right_inv
  map_adj u v := by
    unfold pushGraph
    dsimp only
    rw [w.left_inv, w.left_inv]

theorem IsoWitness.spanningSubgraphCount_eq {n m : Nat} {G₁ : SimpleGraphN n} {G₂ : SimpleGraphN m}
    (w : IsoWitness G₁ G₂) (S : Fin n → Bool) :
    spanningSubgraphCount G₁ S = spanningSubgraphCount G₂ (fun y => S (w.invFun y)) := by
  unfold spanningSubgraphCount
  refine countWhere_bij (pushGraph w) (pushGraph w.symm)
    (nodup_allSimpleGraphs n) (nodup_allSimpleGraphs m) ?_ ?_
  · intro H _ hH
    refine ⟨mem_allSimpleGraphs _, ?_, ?_⟩
    · rw [isSpanningSubgraphOn_eq_true_iff] at hH ⊢
      intro y₁ y₂ hy
      unfold pushGraph at hy; dsimp only at hy
      rcases hH _ _ hy with ⟨h1, h2, h3⟩
      refine ⟨h1, h2, ?_⟩
      have := w.map_adj (w.invFun y₁) (w.invFun y₂)
      rw [w.right_inv, w.right_inv] at this
      rw [← this]; exact h3
    · apply SimpleGraphN.ext; funext u v
      show H.adj (w.invFun (w.toFun u)) (w.invFun (w.toFun v)) = H.adj u v
      rw [w.left_inv, w.left_inv]
  · intro K _ hK
    refine ⟨mem_allSimpleGraphs _, ?_, ?_⟩
    · rw [isSpanningSubgraphOn_eq_true_iff] at hK ⊢
      intro u₁ u₂ hu
      unfold pushGraph at hu; dsimp only [IsoWitness.symm] at hu
      rcases hK _ _ hu with ⟨h1, h2, h3⟩
      rw [w.left_inv] at h1 h2
      refine ⟨h1, h2, ?_⟩
      rw [w.map_adj]; exact h3
    · apply SimpleGraphN.ext; funext y₁ y₂
      show K.adj (w.toFun (w.invFun y₁)) (w.toFun (w.invFun y₂)) = K.adj y₁ y₂
      rw [w.right_inv, w.right_inv]

theorem IsoWitness.connSpanningSubgraphCount_eq {n m : Nat}
    {G₁ : SimpleGraphN n} {G₂ : SimpleGraphN m}
    (w : IsoWitness G₁ G₂) (S : Fin n → Bool) :
    connSpanningSubgraphCount G₁ S =
      connSpanningSubgraphCount G₂ (fun y => S (w.invFun y)) := by
  unfold connSpanningSubgraphCount
  refine countWhere_bij (pushGraph w) (pushGraph w.symm)
    (nodup_allSimpleGraphs n) (nodup_allSimpleGraphs m) ?_ ?_
  · intro H _ hH
    simp only [Bool.and_eq_true] at hH
    refine ⟨mem_allSimpleGraphs _, ?_, ?_⟩
    · simp only [Bool.and_eq_true]
      constructor
      · rw [isSpanningSubgraphOn_eq_true_iff] at *
        intro y₁ y₂ hy
        rcases hH.1 _ _ hy with ⟨h1, h2, h3⟩
        have hm := w.map_adj (w.invFun y₁) (w.invFun y₂)
        rw [w.right_inv, w.right_inv] at hm
        exact ⟨h1, h2, hm ▸ h3⟩
      · let hwH := w.toPushGraph H
        exact (isConnectedSubgraphBool_eq_true_iff _ _).mpr
          ((hwH.isConnectedSubgraph_map S).mp ((isConnectedSubgraphBool_eq_true_iff _ _).mp hH.2))
    · apply SimpleGraphN.ext; funext u v
      show H.adj (w.invFun (w.toFun u)) (w.invFun (w.toFun v)) = H.adj u v
      rw [w.left_inv, w.left_inv]
  · intro K _ hK
    simp only [Bool.and_eq_true] at hK
    refine ⟨mem_allSimpleGraphs _, ?_, ?_⟩
    · simp only [Bool.and_eq_true]
      constructor
      · rw [isSpanningSubgraphOn_eq_true_iff] at *
        intro u₁ u₂ hu
        rcases hK.1 _ _ hu with ⟨h1, h2, h3⟩
        dsimp only [IsoWitness.symm] at h1 h2 h3
        rw [w.left_inv] at h1 h2
        exact ⟨h1, h2, (w.map_adj u₁ u₂).trans h3⟩
      · let hwK := w.symm.toPushGraph K
        have hconn := (hwK.isConnectedSubgraph_map (fun y => S (w.invFun y))).mp
          ((isConnectedSubgraphBool_eq_true_iff _ _).mp hK.2)
        have hS : (fun x => S (w.invFun (w.toFun x))) = S := by
          funext x; rw [w.left_inv]
        change IsConnectedSubgraph (pushGraph w.symm K).adj
          (fun x => S (w.invFun (w.toFun x))) at hconn
        rw [hS] at hconn
        exact (isConnectedSubgraphBool_eq_true_iff _ _).mpr hconn
    · apply SimpleGraphN.ext; funext y₁ y₂
      show K.adj (w.toFun (w.invFun y₁)) (w.toFun (w.invFun y₂)) = K.adj y₁ y₂
      rw [w.right_inv, w.right_inv]

/-- Sum of `F S` over a duplicate-free list of subsets is invariant under bijection. -/
theorem listSum_bij_nat {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]
    {L₁ : List α} {L₂ : List β} (hnd₁ : Nodup L₁) (hnd₂ : Nodup L₂)
    (π : α → β) (π_inv : β → α)
    (h1 : ∀ x ∈ L₁, π x ∈ L₂ ∧ π_inv (π x) = x)
    (h2 : ∀ y ∈ L₂, π_inv y ∈ L₁ ∧ π (π_inv y) = y)
    (f : α → Nat) (g : β → Nat)
    (hfg : ∀ x ∈ L₁, f x = g (π x)) :
    listSum (L₁.map f) = listSum (L₂.map g) := by
  induction hnd₁ generalizing L₂ with
  | nil =>
    cases L₂ with
    | nil => rfl
    | cons y _ => cases (h2 y (List.mem_cons_self ..)).1
  | @cons x xs hx _ ih =>
    have hπx : π x ∈ L₂ := (h1 x (List.mem_cons_self ..)).1
    have hrem : ∀ (a : β) (M : List β), a ∈ M →
        listSum (M.map g) = g a + listSum ((removeOne a M).map g) := by
      intro a M ha
      induction M with
      | nil => cases ha
      | cons z zs ihM =>
        unfold removeOne
        by_cases hza : z = a
        · subst hza; simp [listSum]
        · simp only [hza, ↓reduceIte, List.map, listSum]
          rcases List.mem_cons.mp ha with rfl | hzs
          · exact False.elim (hza rfl)
          · rw [ihM hzs]; omega
    rw [hrem (π x) L₂ hπx]
    simp only [List.map, listSum]
    rw [hfg x (List.mem_cons_self ..)]
    congr 1
    refine ih (nodup_removeOne (π x) hnd₂) ?_ ?_ (fun a ha => hfg a (List.mem_cons_of_mem _ ha))
    · intro a ha
      have ha1 := h1 a (List.mem_cons_of_mem _ ha)
      refine ⟨mem_removeOne_of_ne ?_ ha1.1, ha1.2⟩
      intro heq
      have hax : a = x := by rw [← ha1.2, heq, (h1 x (List.mem_cons_self ..)).2]
      exact hx (hax ▸ ha)
    · intro b hb
      have hb2 := h2 b (mem_of_mem_removeOne hb)
      rcases List.mem_cons.mp hb2.1 with heq | hxs
      · have hb_eq : b = π x := by rw [← hb2.2, heq]
        exact False.elim (not_mem_removeOne_self hnd₂ (hb_eq ▸ hb))
      · exact ⟨hxs, hb2.2⟩

theorem IsoWitness.connEdgeSubgraphCount_eq {n m : Nat}
    {G₁ : SimpleGraphN n} {G₂ : SimpleGraphN m}
    (w : IsoWitness G₁ G₂) (k : Nat) :
    connEdgeSubgraphCount G₁ k = connEdgeSubgraphCount G₂ k := by
  unfold connEdgeSubgraphCount
  refine listSum_bij_nat
    (nodup_filter _ (nodup_allSubsets n))
    (nodup_filter _ (nodup_allSubsets m))
    (fun S y => S (w.invFun y))
    (fun T x => T (w.toFun x)) ?_ ?_
    (connSpanningSubgraphCount G₁) (connSpanningSubgraphCount G₂)
    (fun S _ => w.connSpanningSubgraphCount_eq S)
  · intro S hS
    have hS' := List.mem_filter.mp hS
    have hk : subsetCard S = k := of_decide_eq_true (by simpa using hS'.2)
    refine ⟨List.mem_filter.mpr ⟨mem_allSubsets _, ?_⟩, ?_⟩
    · have hc := (w.subsetCard_map S).trans hk
      simpa using decide_eq_true hc
    · funext x; exact congrArg S (w.left_inv x)
  · intro T hT
    have hT' := List.mem_filter.mp hT
    have hk : subsetCard T = k := of_decide_eq_true (by simpa using hT'.2)
    refine ⟨List.mem_filter.mpr ⟨mem_allSubsets _, ?_⟩, ?_⟩
    · have hc := (w.symm.subsetCard_map T).trans hk
      simpa using decide_eq_true hc
    · funext y; exact congrArg T (w.right_inv y)

theorem IsoWitness.allEdgeSubgraphCount_eq {n m : Nat}
    {G₁ : SimpleGraphN n} {G₂ : SimpleGraphN m}
    (w : IsoWitness G₁ G₂) (k : Nat) :
    allEdgeSubgraphCount G₁ k = allEdgeSubgraphCount G₂ k := by
  unfold allEdgeSubgraphCount
  refine listSum_bij_nat
    (nodup_filter _ (nodup_allSubsets n))
    (nodup_filter _ (nodup_allSubsets m))
    (fun S y => S (w.invFun y))
    (fun T x => T (w.toFun x)) ?_ ?_
    (spanningSubgraphCount G₁) (spanningSubgraphCount G₂)
    (fun S _ => w.spanningSubgraphCount_eq S)
  · intro S hS
    have hS' := List.mem_filter.mp hS
    have hk : subsetCard S = k := of_decide_eq_true (by simpa using hS'.2)
    refine ⟨List.mem_filter.mpr ⟨mem_allSubsets _, ?_⟩, ?_⟩
    · have hc := (w.subsetCard_map S).trans hk
      simpa using decide_eq_true hc
    · funext x; exact congrArg S (w.left_inv x)
  · intro T hT
    have hT' := List.mem_filter.mp hT
    have hk : subsetCard T = k := of_decide_eq_true (by simpa using hT'.2)
    refine ⟨List.mem_filter.mpr ⟨mem_allSubsets _, ?_⟩, ?_⟩
    · have hc := (w.symm.subsetCard_map T).trans hk
      simpa using decide_eq_true hc
    · funext y; exact congrArg T (w.right_inv y)

theorem GraphIso.connEdgeSubgraphVec_eq {n m : Nat} {G₁ : SimpleGraphN n} {G₂ : SimpleGraphN m}
    (h : GraphIso G₁ G₂) : connEdgeSubgraphVec G₁ = connEdgeSubgraphVec G₂ := by
  rcases h with ⟨w⟩
  unfold connEdgeSubgraphVec
  have hrange : List.range n = List.range m := congrArg List.range w.card_eq
  rw [hrange]
  exact List.map_congr_left fun i _ => w.connEdgeSubgraphCount_eq (i + 1)

theorem GraphIso.allEdgeSubgraphVec_eq {n m : Nat} {G₁ : SimpleGraphN n} {G₂ : SimpleGraphN m}
    (h : GraphIso G₁ G₂) : allEdgeSubgraphVec G₁ = allEdgeSubgraphVec G₂ := by
  rcases h with ⟨w⟩
  unfold allEdgeSubgraphVec
  have hrange : List.range n = List.range m := congrArg List.range w.card_eq
  rw [hrange]
  exact List.map_congr_left fun i _ => w.allEdgeSubgraphCount_eq (i + 1)

end Conjecture00000003970
