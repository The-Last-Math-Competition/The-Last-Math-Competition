/-
  Conjecture 00000003970 — Simple Graphs, Graph Isomorphism, and Walk Connectivity
  Pure Core Lean 4.19.0 (zero external dependencies).
-/

import Conjecture00000003970.CountList

namespace Conjecture00000003970

/-- A finite simple (undirected, loopless) graph on `n` vertices `Fin n`. -/
structure SimpleGraphN (n : Nat) where
  adj : Fin n → Fin n → Bool
  loopless : ∀ u : Fin n, adj u u = false
  symm : ∀ u v : Fin n, adj u v = adj v u

theorem SimpleGraphN.ext {n : Nat} {G₁ G₂ : SimpleGraphN n}
    (h : G₁.adj = G₂.adj) : G₁ = G₂ := by
  cases G₁; cases G₂
  simp only [mk.injEq]
  exact h

instance instDecidableEqSimpleGraphN {n : Nat} : DecidableEq (SimpleGraphN n) :=
  fun G₁ G₂ =>
    if h : G₁.adj = G₂.adj then isTrue (SimpleGraphN.ext h)
    else isFalse (fun heq => h (congrArg SimpleGraphN.adj heq))

/-- Explicit graph isomorphism witness between `G₁ : SimpleGraphN n` and `G₂ : SimpleGraphN m`. -/
structure IsoWitness {n m : Nat} (G₁ : SimpleGraphN n) (G₂ : SimpleGraphN m) where
  toFun : Fin n → Fin m
  invFun : Fin m → Fin n
  left_inv : ∀ u : Fin n, invFun (toFun u) = u
  right_inv : ∀ v : Fin m, toFun (invFun v) = v
  map_adj : ∀ u v : Fin n, G₁.adj u v = G₂.adj (toFun u) (toFun v)

/-- Propositional graph isomorphism `G₁ ≅ G₂`. -/
def GraphIso {n m : Nat} (G₁ : SimpleGraphN n) (G₂ : SimpleGraphN m) : Prop :=
  Nonempty (IsoWitness G₁ G₂)

theorem GraphIso.refl {n : Nat} (G : SimpleGraphN n) : GraphIso G G :=
  ⟨{ toFun := id
     invFun := id
     left_inv := fun _ => rfl
     right_inv := fun _ => rfl
     map_adj := fun _ _ => rfl }⟩

def IsoWitness.symm {n m : Nat} {G₁ : SimpleGraphN n} {G₂ : SimpleGraphN m}
    (w : IsoWitness G₁ G₂) : IsoWitness G₂ G₁ where
  toFun := w.invFun
  invFun := w.toFun
  left_inv := w.right_inv
  right_inv := w.left_inv
  map_adj := fun u v => by
    have := w.map_adj (w.invFun u) (w.invFun v)
    rw [w.right_inv u, w.right_inv v] at this
    exact this.symm

theorem GraphIso.symm {n m : Nat} {G₁ : SimpleGraphN n} {G₂ : SimpleGraphN m}
    (h : GraphIso G₁ G₂) : GraphIso G₂ G₁ :=
  let ⟨w⟩ := h
  ⟨w.symm⟩

def IsoWitness.trans {n m k : Nat}
    {G₁ : SimpleGraphN n} {G₂ : SimpleGraphN m} {G₃ : SimpleGraphN k}
    (w₁ : IsoWitness G₁ G₂) (w₂ : IsoWitness G₂ G₃) : IsoWitness G₁ G₃ where
  toFun := fun u => w₂.toFun (w₁.toFun u)
  invFun := fun v => w₁.invFun (w₂.invFun v)
  left_inv := fun u => by rw [w₂.left_inv, w₁.left_inv]
  right_inv := fun v => by rw [w₁.right_inv, w₂.right_inv]
  map_adj := fun u v => by rw [w₁.map_adj, w₂.map_adj]

theorem GraphIso.trans {n m k : Nat}
    {G₁ : SimpleGraphN n} {G₂ : SimpleGraphN m} {G₃ : SimpleGraphN k}
    (h₁ : GraphIso G₁ G₂) (h₂ : GraphIso G₂ G₃) : GraphIso G₁ G₃ :=
  let ⟨w₁⟩ := h₁
  let ⟨w₂⟩ := h₂
  ⟨w₁.trans w₂⟩

theorem filter_const_true {α : Type u} (L : List α) :
    L.filter (fun _ => true) = L := by
  induction L with
  | nil => rfl
  | cons x xs ih => simp [List.filter, ih]

theorem IsoWitness.card_eq {n m : Nat} {G₁ : SimpleGraphN n} {G₂ : SimpleGraphN m}
    (w : IsoWitness G₁ G₂) : n = m := by
  have hbij := countWhere_bij (L₁ := allFin n) (L₂ := allFin m)
    (P₁ := fun _ => true) (P₂ := fun _ => true)
    w.toFun w.invFun (nodup_allFin n) (nodup_allFin m)
    (fun x _ _ => ⟨mem_allFin _, rfl, w.left_inv x⟩)
    (fun y _ _ => ⟨mem_allFin _, rfl, w.right_inv y⟩)
  have h1 : countWhere (allFin n) (fun _ => true) = n := by
    simp [countWhere, filter_const_true, length_allFin]
  have h2 : countWhere (allFin m) (fun _ => true) = m := by
    simp [countWhere, filter_const_true, length_allFin]
  omega

theorem GraphIso.card_eq {n m : Nat} {G₁ : SimpleGraphN n} {G₂ : SimpleGraphN m}
    (h : GraphIso G₁ G₂) : n = m :=
  let ⟨w⟩ := h
  w.card_eq

/-- Vertex degree in a `SimpleGraphN n`. -/
def vertexDeg {n : Nat} (G : SimpleGraphN n) (u : Fin n) : Nat :=
  countWhere (allFin n) (fun v => G.adj u v)

theorem IsoWitness.deg_eq {n m : Nat} {G₁ : SimpleGraphN n} {G₂ : SimpleGraphN m}
    (w : IsoWitness G₁ G₂) (u : Fin n) :
    vertexDeg G₁ u = vertexDeg G₂ (w.toFun u) := by
  unfold vertexDeg
  refine countWhere_bij w.toFun w.invFun (nodup_allFin n) (nodup_allFin m) ?_ ?_
  · intro v _ hv
    refine ⟨mem_allFin _, ?_, w.left_inv v⟩
    rw [← w.map_adj u v]
    exact hv
  · intro y _ hy
    refine ⟨mem_allFin _, ?_, w.right_inv y⟩
    rw [w.map_adj u (w.invFun y), w.right_inv y]
    exact hy

/-! ### Propositional Walk Connectivity & Verified Decidability -/

/-- Textbook walk reachability inside vertex subset `S` along adjacency `adj`. -/
inductive ReachableIn {n : Nat} (adj : Fin n → Fin n → Bool) (S : Fin n → Bool) :
    Fin n → Fin n → Prop where
  | refl {u : Fin n} : S u = true → ReachableIn adj S u u
  | step {u v w : Fin n} :
      S u = true → S v = true → adj u v = true →
      ReachableIn adj S v w → ReachableIn adj S u w

theorem ReachableIn.left_mem {n : Nat} {adj : Fin n → Fin n → Bool} {S : Fin n → Bool}
    {u v : Fin n} (h : ReachableIn adj S u v) : S u = true := by
  cases h with
  | refl hs => exact hs
  | step hsu _ _ _ => exact hsu

theorem ReachableIn.right_mem {n : Nat} {adj : Fin n → Fin n → Bool} {S : Fin n → Bool}
    {u v : Fin n} (h : ReachableIn adj S u v) : S v = true := by
  induction h with
  | refl hs => exact hs
  | step _ _ _ _ ih => exact ih

theorem ReachableIn.trans {n : Nat} {adj : Fin n → Fin n → Bool} {S : Fin n → Bool}
    {u v w : Fin n} (h₁ : ReachableIn adj S u v) (h₂ : ReachableIn adj S v w) :
    ReachableIn adj S u w := by
  induction h₁ with
  | refl _ => exact h₂
  | step hsu hsv hadj _ ih => exact .step hsu hsv hadj (ih h₂)

theorem ReachableIn.symm_of_symm {n : Nat} {adj : Fin n → Fin n → Bool}
    (hsym : ∀ a b : Fin n, adj a b = adj b a) {S : Fin n → Bool}
    {u v : Fin n} (h : ReachableIn adj S u v) : ReachableIn adj S v u := by
  induction h with
  | refl hs => exact .refl hs
  | @step a b _ hsa hsb hab _ ih =>
    have hba : adj b a = true := by rw [hsym b a]; exact hab
    exact ih.trans (.step hsb hsa hba (.refl hsa))

theorem ReachableIn.mono_adj {n : Nat} {adj₁ adj₂ : Fin n → Fin n → Bool} {S : Fin n → Bool}
    (hmono : ∀ a b, S a = true → S b = true → adj₁ a b = true → adj₂ a b = true)
    {u v : Fin n} (h : ReachableIn adj₁ S u v) : ReachableIn adj₂ S u v := by
  induction h with
  | refl hs => exact .refl hs
  | step hsa hsb hab _ ih =>
    exact .step hsa hsb (hmono _ _ hsa hsb hab) ih

/-- Textbook propositional connectedness of `(S, adj)`: `S` is nonempty and every pair of
    vertices in `S` is joined by a walk inside `S`. -/
def IsConnectedSubgraph {n : Nat} (adj : Fin n → Fin n → Bool) (S : Fin n → Bool) : Prop :=
  (∃ u : Fin n, S u = true) ∧
  (∀ u v : Fin n, S u = true → S v = true → ReachableIn adj S u v)

/-- Connectedness of the whole graph `G : SimpleGraphN n`. -/
def IsConnectedGraph {n : Nat} (G : SimpleGraphN n) : Prop :=
  IsConnectedSubgraph G.adj (fun _ => true)

/-! #### Verified Boolean Fixed-Point Decision Procedure for `ReachableIn` -/

/-- One backward reachability step inside `S`. -/
def stepReachBack {n : Nat} (adj : Fin n → Fin n → Bool) (S : Fin n → Bool)
    (R : Fin n → Bool) (x : Fin n) : Bool :=
  R x || (S x && (allFin n).any (fun y => adj x y && R y))

/-- Iterate `stepReachBack` `k` times. -/
def iterReachBack {n : Nat} (adj : Fin n → Fin n → Bool) (S : Fin n → Bool) :
    Nat → (Fin n → Bool) → (Fin n → Bool)
  | 0, R => R
  | k + 1, R => iterReachBack adj S k (stepReachBack adj S R)

/-- Boolean decision procedure for `ReachableIn adj S u w`. -/
def reachBool {n : Nat} (adj : Fin n → Fin n → Bool) (S : Fin n → Bool)
    (u w : Fin n) : Bool :=
  iterReachBack adj S n (fun x => S w && decide (x = w)) u

/-- Cardinality of a boolean subset `R : Fin n → Bool`. -/
def subsetCard {n : Nat} (R : Fin n → Bool) : Nat :=
  countWhere (allFin n) R

theorem filter_length_le {α : Type u} (L : List α) (P : α → Bool) :
    (L.filter P).length ≤ L.length := by
  induction L with
  | nil => exact Nat.zero_le _
  | cons _ xs ih =>
    unfold List.filter
    split <;> simp only [List.length] <;> omega

theorem subsetCard_le {n : Nat} (R : Fin n → Bool) : subsetCard R ≤ n := by
  unfold subsetCard countWhere
  have := filter_length_le (allFin n) R
  rw [length_allFin] at this
  exact this

theorem filter_length_le_of_imp {α : Type u} {L : List α} {P Q : α → Bool}
    (himp : ∀ z ∈ L, P z = true → Q z = true) :
    (L.filter P).length ≤ (L.filter Q).length := by
  induction L with
  | nil => exact Nat.zero_le _
  | cons z zs ih =>
    have hz_imp := himp z (List.mem_cons_self ..)
    have hle := ih (fun w hw => himp w (List.mem_cons_of_mem _ hw))
    by_cases hPz : P z = true
    · have hQz := hz_imp hPz
      simp only [List.filter, hPz, hQz, List.length]
      omega
    · have hPzF : P z = false := Bool.eq_false_iff.mpr hPz
      by_cases hQz : Q z = true
      · simp only [List.filter, hPzF, hQz, List.length]; omega
      · have hQzF : Q z = false := Bool.eq_false_iff.mpr hQz
        simp only [List.filter, hPzF, hQzF]; exact hle

theorem filter_length_lt_of_imp_of_witness {α : Type u} {L : List α} {P Q : α → Bool}
    (himp : ∀ z ∈ L, P z = true → Q z = true)
    {x₀ : α} (hx₀ : x₀ ∈ L) (hP₀ : P x₀ = false) (hQ₀ : Q x₀ = true) :
    (L.filter P).length < (L.filter Q).length := by
  induction L with
  | nil => cases hx₀
  | cons x xs ih =>
    rcases List.mem_cons.mp hx₀ with rfl | hxs
    · have hle := filter_length_le_of_imp (L := xs)
        (fun z hz => himp z (List.mem_cons_of_mem _ hz))
      simp only [List.filter, hP₀, hQ₀, List.length]
      omega
    · have hlt := ih (fun z hz => himp z (List.mem_cons_of_mem _ hz)) hxs
      have hx_imp := himp x (List.mem_cons_self ..)
      by_cases hPx : P x = true
      · have hQx := hx_imp hPx
        simp only [List.filter, hPx, hQx, List.length]
        omega
      · have hPxF : P x = false := Bool.eq_false_iff.mpr hPx
        by_cases hQx : Q x = true
        · simp only [List.filter, hPxF, hQx, List.length]; omega
        · have hQxF : Q x = false := Bool.eq_false_iff.mpr hQx
          simp only [List.filter, hPxF, hQxF]; exact hlt

theorem stepReachBack_infl {n : Nat} (adj : Fin n → Fin n → Bool) (S : Fin n → Bool)
    (R : Fin n → Bool) (x : Fin n) (h : R x = true) :
    stepReachBack adj S R x = true := by
  simp [stepReachBack, h]

theorem iterReachBack_infl {n : Nat} (adj : Fin n → Fin n → Bool) (S : Fin n → Bool) :
    ∀ (k : Nat) (R : Fin n → Bool) (x : Fin n),
      R x = true → iterReachBack adj S k R x = true
  | 0, _, _, h => h
  | k + 1, R, x, h =>
    iterReachBack_infl adj S k (stepReachBack adj S R) x (stepReachBack_infl adj S R x h)

theorem stepReachBack_card_lt_of_ne {n : Nat} (adj : Fin n → Fin n → Bool) (S : Fin n → Bool)
    {R : Fin n → Bool} (hne : stepReachBack adj S R ≠ R) :
    subsetCard R < subsetCard (stepReachBack adj S R) := by
  have hex : ∃ x : Fin n, R x = false ∧ stepReachBack adj S R x = true := by
    by_cases hall : ∀ x : Fin n, stepReachBack adj S R x = R x
    · exact False.elim (hne (funext hall))
    · have hnotall : ¬ ((allFin n).all (fun x => stepReachBack adj S R x == R x) = true) := by
        intro ha
        apply hall
        intro x
        have hx := List.all_eq_true.mp ha x (mem_allFin x)
        exact eq_of_beq hx
      have hfalse : (allFin n).all (fun x => stepReachBack adj S R x == R x) = false :=
        Bool.eq_false_iff.mpr hnotall
      rcases List.all_eq_false.mp hfalse with ⟨x, _, hx⟩
      cases hRx : R x
      · cases hSx : stepReachBack adj S R x
        · simp [hRx, hSx] at hx
        · exact ⟨x, hRx, hSx⟩
      · have hSx := stepReachBack_infl adj S R x hRx
        simp [hRx, hSx] at hx
  rcases hex with ⟨x₀, hR₀, hS₀⟩
  exact filter_length_lt_of_imp_of_witness
    (fun z _ hz => stepReachBack_infl adj S R z hz)
    (mem_allFin x₀) hR₀ hS₀

theorem iterReachBack_card_growth {n : Nat} (adj : Fin n → Fin n → Bool) (S : Fin n → Bool) :
    ∀ (k : Nat) (R : Fin n → Bool),
      stepReachBack adj S (iterReachBack adj S k R) ≠ iterReachBack adj S k R →
      subsetCard R + (k + 1) ≤ subsetCard (stepReachBack adj S (iterReachBack adj S k R))
  | 0, R, hne => by
    unfold iterReachBack at hne ⊢
    have := stepReachBack_card_lt_of_ne adj S hne
    omega
  | k + 1, R, hne => by
    have hne_prev : stepReachBack adj S R ≠ R := by
      intro heq
      apply hne
      have hfixed : ∀ t, iterReachBack adj S t R = R := by
        intro t
        induction t with
        | zero => rfl
        | succ t iht =>
          unfold iterReachBack
          rw [heq, iht]
      rw [hfixed (k + 1), heq]
    have h1 := stepReachBack_card_lt_of_ne adj S hne_prev
    have h2 := iterReachBack_card_growth adj S k (stepReachBack adj S R) hne
    unfold iterReachBack
    omega

theorem iterReachBack_fixed {n : Nat} (adj : Fin n → Fin n → Bool) (S : Fin n → Bool)
    (R : Fin n → Bool) :
    stepReachBack adj S (iterReachBack adj S n R) = iterReachBack adj S n R := by
  by_cases h : stepReachBack adj S (iterReachBack adj S n R) = iterReachBack adj S n R
  · exact h
  · have hgrow := iterReachBack_card_growth adj S n R h
    have hbound := subsetCard_le (stepReachBack adj S (iterReachBack adj S n R))
    omega

theorem iterReachBack_sound {n : Nat} (adj : Fin n → Fin n → Bool) (S : Fin n → Bool) (w : Fin n) :
    ∀ (k : Nat) {R : Fin n → Bool},
      (∀ x, R x = true → ReachableIn adj S x w) →
      ∀ x, iterReachBack adj S k R x = true → ReachableIn adj S x w
  | 0, _, hR, x, hx => hR x hx
  | k + 1, R, hR, x, hx => by
    refine iterReachBack_sound adj S w k (R := stepReachBack adj S R) ?_ x hx
    intro u hu
    unfold stepReachBack at hu
    simp only [Bool.or_eq_true, Bool.and_eq_true] at hu
    rcases hu with hRu | ⟨hSu, hany⟩
    · exact hR u hRu
    · rcases List.any_eq_true.mp hany with ⟨v, _, hv⟩
      simp only [Bool.and_eq_true] at hv
      rcases hv with ⟨hadj, hRv⟩
      have hvw := hR v hRv
      exact .step hSu hvw.left_mem hadj hvw

theorem reachBool_eq_true_iff {n : Nat} (adj : Fin n → Fin n → Bool) (S : Fin n → Bool)
    (u w : Fin n) :
    reachBool adj S u w = true ↔ ReachableIn adj S u w := by
  constructor
  · intro hb
    unfold reachBool at hb
    refine iterReachBack_sound adj S w n ?_ u hb
    intro x hx
    simp only [Bool.and_eq_true] at hx
    rcases hx with ⟨hSw, hxw⟩
    have hxw' : x = w := of_decide_eq_true hxw
    subst hxw'
    exact .refl hSw
  · intro hreach
    unfold reachBool
    let R₀ : Fin n → Bool := fun x => S w && decide (x = w)
    let Rstar := iterReachBack adj S n R₀
    have hfix : stepReachBack adj S Rstar = Rstar := iterReachBack_fixed adj S R₀
    change Rstar u = true
    induction hreach with
    | @refl z hSz =>
      have h0 : R₀ z = true := by simp [R₀, hSz]
      exact iterReachBack_infl adj S n R₀ z h0
    | @step a b _ hSa _ hab _ ih =>
      have ih' : Rstar b = true := ih hfix
      have hstep : stepReachBack adj S Rstar a = true := by
        unfold stepReachBack
        simp only [Bool.or_eq_true, Bool.and_eq_true]
        right
        refine ⟨hSa, List.any_eq_true.mpr ⟨b, mem_allFin b, ?_⟩⟩
        simp [hab, ih']
      rw [hfix] at hstep
      exact hstep

instance instDecidableReachableIn {n : Nat} (adj : Fin n → Fin n → Bool) (S : Fin n → Bool)
    (u w : Fin n) : Decidable (ReachableIn adj S u w) :=
  if h : reachBool adj S u w = true then
    isTrue ((reachBool_eq_true_iff adj S u w).mp h)
  else
    isFalse (fun hr => h ((reachBool_eq_true_iff adj S u w).mpr hr))

/-- Boolean decision procedure for `IsConnectedSubgraph adj S`. -/
def isConnectedSubgraphBool {n : Nat} (adj : Fin n → Fin n → Bool) (S : Fin n → Bool) : Bool :=
  (allFin n).any S &&
  (allFin n).all (fun u => !S u || (allFin n).all (fun v => !S v || reachBool adj S u v))

theorem isConnectedSubgraphBool_eq_true_iff {n : Nat}
    (adj : Fin n → Fin n → Bool) (S : Fin n → Bool) :
    isConnectedSubgraphBool adj S = true ↔ IsConnectedSubgraph adj S := by
  unfold isConnectedSubgraphBool IsConnectedSubgraph
  constructor
  · intro h
    simp only [Bool.and_eq_true] at h
    rcases h with ⟨hany, hall⟩
    rcases List.any_eq_true.mp hany with ⟨u₀, _, hu₀⟩
    refine ⟨⟨u₀, hu₀⟩, ?_⟩
    intro u v hu hv
    have hu' := List.all_eq_true.mp hall u (mem_allFin u)
    simp only [hu, Bool.not_true, Bool.false_or] at hu'
    have hv' := List.all_eq_true.mp hu' v (mem_allFin v)
    simp only [hv, Bool.not_true, Bool.false_or] at hv'
    exact (reachBool_eq_true_iff adj S u v).mp hv'
  · rintro ⟨⟨u₀, hu₀⟩, hconn⟩
    simp only [Bool.and_eq_true]
    refine ⟨List.any_eq_true.mpr ⟨u₀, mem_allFin u₀, hu₀⟩, List.all_eq_true.mpr ?_⟩
    intro u _
    cases hSu : S u
    · simp
    · simp only [Bool.not_true, Bool.false_or]
      apply List.all_eq_true.mpr
      intro v _
      cases hSv : S v
      · simp
      · simp only [Bool.not_true, Bool.false_or]
        exact (reachBool_eq_true_iff adj S u v).mpr (hconn u v hSu hSv)

instance instDecidableIsConnectedSubgraph {n : Nat}
    (adj : Fin n → Fin n → Bool) (S : Fin n → Bool) :
    Decidable (IsConnectedSubgraph adj S) :=
  if h : isConnectedSubgraphBool adj S = true then
    isTrue ((isConnectedSubgraphBool_eq_true_iff adj S).mp h)
  else
    isFalse (fun hc => h ((isConnectedSubgraphBool_eq_true_iff adj S).mpr hc))

instance instDecidableIsConnectedGraph {n : Nat} (G : SimpleGraphN n) :
    Decidable (IsConnectedGraph G) :=
  instDecidableIsConnectedSubgraph G.adj (fun _ => true)

end Conjecture00000003970
