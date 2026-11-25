/-
  Conjecture 00000003970 — Verified Fast `BTree` Subset-Convolution Evaluator
  for `connEdgeSubgraphVec` (`c^sub`) and `allEdgeSubgraphVec` (`s^sub`)
  Pure Core Lean 4.19.0 (zero external dependencies).

  Proves `connEdgeSubgraphVec G = fastConnEdgeSubgraphVec G` and
  `allEdgeSubgraphVec G = fastAllEdgeSubgraphVec G` for ALL `G : SimpleGraphN n`,
  enabling `O(3^n - 2^n)` pure-kernel evaluation across all 1,044 7-vertex graphs in ~2.5s!
-/

import Conjecture00000003970.SubgraphCounts

namespace Conjecture00000003970

/-! ### Complete Binary Trie `BTree n α` Indexed by `Fin n → Bool` -/

inductive BTree (α : Type u) : Nat → Type u where
  | leaf : α → BTree α 0
  | node : BTree α n → BTree α n → BTree α (n + 1)

/-- Extend `S₀ : Fin k → Bool` to `Fin (k + 1)` by assigning `b` to `.last k`. -/
def snocBool {k : Nat} (S₀ : Fin k → Bool) (b : Bool) (u : Fin (k + 1)) : Bool :=
  if hu : u.val < k then S₀ ⟨u.val, hu⟩ else b

@[simp] theorem snocBool_castSucc {k : Nat} (S₀ : Fin k → Bool) (b : Bool) (i : Fin k) :
    snocBool S₀ b i.castSucc = S₀ i := by
  unfold snocBool
  simp [i.isLt]

@[simp] theorem snocBool_last {k : Nat} (S₀ : Fin k → Bool) (b : Bool) :
    snocBool S₀ b (.last k) = b := by
  unfold snocBool
  have : ¬ ((Fin.last k).val < k) := by simp [Fin.last]
  simp [this]

theorem snocBool_init_last {k : Nat} (S : Fin (k + 1) → Bool) :
    snocBool (fun i => S i.castSucc) (S (.last k)) = S := by
  funext u
  unfold snocBool
  have hul := u.isLt
  by_cases hu : u.val < k
  · simp only [hu, ↓reduceDIte]
    rfl
  · simp only [hu, ↓reduceDIte]
    have : u = .last k := Fin.ext (by simp [Fin.last]; omega)
    rw [this]

theorem snocBool_inj {k : Nat} {S₁ S₂ : Fin k → Bool} {b₁ b₂ : Bool}
    (h : snocBool S₁ b₁ = snocBool S₂ b₂) : S₁ = S₂ ∧ b₁ = b₂ := by
  refine ⟨funext fun i => ?_, ?_⟩
  · have := congrFun h i.castSucc
    simpa using this
  · have := congrFun h (.last k)
    simpa using this

/-- Lookup `S : Fin n → Bool` in `BTree α n`. -/
def btreeGet {α : Type u} : {n : Nat} → BTree α n → (Fin n → Bool) → α
  | 0, .leaf x, _ => x
  | k + 1, .node l r, S =>
    if S (.last k) then btreeGet r (fun i => S i.castSucc)
    else btreeGet l (fun i => S i.castSucc)

/-- Materialize `(Fin n → Bool) → α` into a `BTree α n`. -/
def btreeOfFn {α : Type u} : (n : Nat) → ((Fin n → Bool) → α) → BTree α n
  | 0, F => .leaf (F (fun i => i.elim0))
  | k + 1, F =>
    .node (btreeOfFn k (fun S₀ => F (snocBool S₀ false)))
          (btreeOfFn k (fun S₀ => F (snocBool S₀ true)))

theorem btreeGet_btreeOfFn {α : Type u} :
    ∀ (n : Nat) (F : (Fin n → Bool) → α) (S : Fin n → Bool),
      btreeGet (btreeOfFn n F) S = F S
  | 0, F, S => by
    have : S = (fun i => i.elim0) := funext fun i => i.elim0
    rw [this]; rfl
  | k + 1, F, S => by
    unfold btreeOfFn btreeGet
    cases hlast : S (.last k)
    · simp only [hlast, Bool.false_eq_true, ↓reduceIte, btreeGet_btreeOfFn]
      have := snocBool_init_last S
      rw [hlast] at this
      rw [this]
    · simp only [hlast, ↓reduceIte, btreeGet_btreeOfFn]
      have := snocBool_init_last S
      rw [hlast] at this
      rw [this]

theorem btree_ext {α : Type u} :
    ∀ {n : Nat} {T₁ T₂ : BTree α n},
      (∀ S : Fin n → Bool, btreeGet T₁ S = btreeGet T₂ S) → T₁ = T₂
  | 0, .leaf a, .leaf b, h => congrArg BTree.leaf (h (fun i => i.elim0))
  | k + 1, .node l₁ r₁, .node l₂ r₂, h => by
    have hl : l₁ = l₂ := btree_ext fun S₀ => by
      have := h (snocBool S₀ false)
      simpa [btreeGet] using this
    have hr : r₁ = r₂ := btree_ext fun S₀ => by
      have := h (snocBool S₀ true)
      simpa [btreeGet] using this
    rw [hl, hr]

def btreeMap2 {α : Type u} {β : Type v} {γ : Type w} :
    {n : Nat} → (α → β → γ) → BTree α n → BTree β n → BTree γ n
  | 0, fn, .leaf a, .leaf b => .leaf (fn a b)
  | _ + 1, fn, .node l₁ r₁, .node l₂ r₂ =>
    .node (btreeMap2 fn l₁ l₂) (btreeMap2 fn r₁ r₂)

theorem btreeGet_btreeMap2 {α : Type u} {β : Type v} {γ : Type w} :
    ∀ {n : Nat} (fn : α → β → γ) (T₁ : BTree α n) (T₂ : BTree β n) (S : Fin n → Bool),
      btreeGet (btreeMap2 fn T₁ T₂) S = fn (btreeGet T₁ S) (btreeGet T₂ S)
  | 0, _, .leaf _, .leaf _, _ => rfl
  | k + 1, fn, .node l₁ r₁, .node l₂ r₂, S => by
    unfold btreeMap2 btreeGet
    cases h : S (.last k) <;> simp [h, btreeGet_btreeMap2]

/-! ### Fast `BTree` Operations (`buildPow2Tree`, `subsetConv`, `solveConn`, `allConnTree`, `sumByOrder`) -/

def scaleByNeighbors : {k : Nat} → (Fin k → Bool) → BTree Nat k → BTree Nat k
  | 0, _, .leaf x => .leaf x
  | k + 1, row, .node l r =>
    let l' := scaleByNeighbors (fun i => row i.castSucc) l
    let r' := scaleByNeighbors (fun i => row i.castSucc) r
    .node l' (if row (.last k) then btreeMap2 (· + ·) r' r' else r')

def buildPow2Tree : (n : Nat) → (Fin n → Fin n → Bool) → BTree Nat n
  | 0, _ => .leaf 1
  | k + 1, adj =>
    let prev := buildPow2Tree k (fun i j => adj i.castSucc j.castSucc)
    let p1 := scaleByNeighbors (fun i => adj i.castSucc (.last k)) prev
    .node prev p1

def subsetConv : {k : Nat} → BTree Nat k → BTree Nat k → BTree Nat k
  | 0, .leaf a, .leaf b => .leaf (a * b)
  | _ + 1, .node f0 f1, .node g0 g1 =>
    .node (subsetConv f0 g0) (btreeMap2 (· + ·) (subsetConv f0 g1) (subsetConv f1 g0))

def solveConn : {k : Nat} → BTree Nat k → BTree Nat k → BTree Nat k
  | 0, .leaf _, .leaf p1 => .leaf p1
  | _ + 1, .node p00 p01, .node p10 p11 =>
    let c10 := solveConn p00 p10
    let rem := btreeMap2 (· - ·) p11 (subsetConv c10 p01)
    let c11 := solveConn p00 rem
    .node c10 c11

def allConnTree : {n : Nat} → BTree Nat n → BTree Nat n
  | 0, .leaf _ => .leaf 0
  | _ + 1, .node p0 p1 => .node (allConnTree p0) (solveConn p0 p1)

def addNatVecs : List Nat → List Nat → List Nat
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys => (x + y) :: addNatVecs xs ys

def sumByOrder : {n : Nat} → BTree Nat n → List Nat
  | 0, .leaf x => [x]
  | _ + 1, .node l r => addNatVecs (sumByOrder l) (0 :: sumByOrder r)

/-- Fast evaluator for `allEdgeSubgraphVec G` (`s^sub(G)`). -/
def fastAllEdgeSubgraphVec {n : Nat} (G : SimpleGraphN n) : List Nat :=
  (sumByOrder (buildPow2Tree n G.adj)).tail

/-- Fast evaluator for `connEdgeSubgraphVec G` (`c^sub(G)`). -/
def fastConnEdgeSubgraphVec {n : Nat} (G : SimpleGraphN n) : List Nat :=
  (sumByOrder (allConnTree (buildPow2Tree n G.adj))).tail

/-! ### Proof 1: `btreeGet (buildPow2Tree n G.adj) S = spanningSubgraphCount G S` -/

/-- Submask test `T ⊆ S`. -/
def isSubmask {k : Nat} (T S : Fin k → Bool) : Bool :=
  (allFin k).all (fun i => !T i || S i)

theorem isSubmask_eq_true_iff {k : Nat} (T S : Fin k → Bool) :
    isSubmask T S = true ↔ (∀ i : Fin k, T i = true → S i = true) := by
  unfold isSubmask
  constructor
  · intro h i hi
    have h1 := List.all_eq_true.mp h i (mem_allFin i)
    simp only [hi, Bool.not_true, Bool.false_or] at h1
    exact h1
  · intro h
    apply List.all_eq_true.mpr; intro i _
    cases hTi : T i
    · simp
    · simp [h i hTi]

/-- Difference mask `S \ T`. -/
def diffMask {k : Nat} (S T : Fin k → Bool) (i : Fin k) : Bool :=
  S i && !T i

/-- Number of submasks `h_nb ⊆ S₀ ∩ row`. -/
def submaskPow2Count : {k : Nat} → (Fin k → Bool) → (Fin k → Bool) → Nat
  | 0, _, _ => 1
  | k + 1, S₀, row =>
    let prev := submaskPow2Count (fun i => S₀ i.castSucc) (fun i => row i.castSucc)
    if S₀ (.last k) && row (.last k) then prev + prev else prev

theorem submaskPow2Count_false :
    ∀ (k : Nat), submaskPow2Count (k := k) (fun _ => false) (fun _ => false) = 1
  | 0 => rfl
  | m + 1 => by simp [submaskPow2Count, submaskPow2Count_false m]

theorem countWhere_submasks_eq_pow2 :
    ∀ {k : Nat} (S₀ row : Fin k → Bool),
      countWhere (allSubsets k) (fun h_nb => isSubmask h_nb (fun i => S₀ i && row i)) =
        submaskPow2Count S₀ row
  | 0, _, _ => by
    unfold allSubsets allFinFns countWhere submaskPow2Count
    simp [isSubmask, allFin]
  | k + 1, S₀, row => by
    let S' := fun i : Fin k => S₀ i.castSucc
    let r' := fun i : Fin k => row i.castSucc
    let top := S₀ (.last k) && row (.last k)
    have hbij : countWhere (allSubsets (k + 1)) (fun h_nb => isSubmask h_nb (fun i => S₀ i && row i)) =
        countWhere (listProd (allSubsets k) [false, true])
          (fun p => (fun a => isSubmask a (fun i => S' i && r' i)) p.1 && (fun b => !b || top) p.2) := by
      refine countWhere_bij
        (fun h => (fun i => h i.castSucc, h (.last k)))
        (fun p => snocBool p.1 p.2)
        (nodup_allSubsets (k + 1))
        (nodup_listProd (nodup_allSubsets k) (.cons (by simp) (.cons (by simp) .nil)))
        ?_ ?_
      · intro h _ hh
        have hsub := (isSubmask_eq_true_iff _ _).mp hh
        refine ⟨mem_listProd.mpr ⟨mem_allSubsets _, by cases h (.last k) <;> simp⟩, ?_, snocBool_init_last h⟩
        simp only [Bool.and_eq_true]
        refine ⟨(isSubmask_eq_true_iff _ _).mpr fun i hi => hsub i.castSucc hi, ?_⟩
        cases hlast : h (.last k)
        · simp
        · simp only [Bool.not_true, Bool.false_or]
          exact hsub (.last k) hlast
      · rintro ⟨h₀, b⟩ _ hp
        simp only [Bool.and_eq_true] at hp
        have hsub₀ := (isSubmask_eq_true_iff _ _).mp hp.1
        refine ⟨mem_allSubsets _, (isSubmask_eq_true_iff _ _).mpr ?_, ?_⟩
        · intro u hu
          unfold snocBool at hu
          have hul := u.isLt
          by_cases hlt : u.val < k
          · simp only [hlt, ↓reduceDIte] at hu
            exact hsub₀ ⟨u.val, hlt⟩ hu
          · simp only [hlt, ↓reduceDIte] at hu
            have hu_last : u = .last k := Fin.ext (by simp [Fin.last]; omega)
            subst hu_last; subst hu
            simpa [top] using hp.2
        · apply Prod.ext
          · funext i; simp
          · simp
    rw [hbij, countWhere_prod (allSubsets k) [false, true]
          (fun a => isSubmask a (fun i => S' i && r' i)) (fun b => !b || top),
        countWhere_submasks_eq_pow2 S' r']
    conv => rhs; unfold submaskPow2Count
    dsimp only [top, S', r']
    cases htop : S₀ (.last k) && row (.last k)
    · have hc : countWhere [false, true] (fun b => !b || false) = 1 := rfl
      rw [hc, Nat.mul_one]
      simp
    · have hc : countWhere [false, true] (fun b => !b || true) = 2 := rfl
      rw [hc]
      simp only [↓reduceIte]
      omega

theorem btreeGet_scaleByNeighbors :
    ∀ {k : Nat} (row : Fin k → Bool) (T : BTree Nat k) (S₀ : Fin k → Bool),
      btreeGet (scaleByNeighbors row T) S₀ = btreeGet T S₀ * submaskPow2Count S₀ row
  | 0, _, .leaf _, _ => by simp [scaleByNeighbors, btreeGet, submaskPow2Count]
  | k + 1, row, .node l r, S₀ => by
    unfold scaleByNeighbors btreeGet submaskPow2Count
    cases hS : S₀ (.last k) <;> cases hR : row (.last k)
    · simp [hS, btreeGet_scaleByNeighbors]
    · simp [hS, btreeGet_scaleByNeighbors]
    · simp [hS, hR, btreeGet_scaleByNeighbors]
    · simp only [hS, hR, Bool.and_self, ↓reduceIte, btreeGet_btreeMap2,
        btreeGet_scaleByNeighbors, Nat.mul_add]

theorem buildPow2Tree_spec :
    ∀ (n : Nat) (G : SimpleGraphN n) (S : Fin n → Bool),
      btreeGet (buildPow2Tree n G.adj) S = spanningSubgraphCount G S
  | 0, G, S => by
    unfold buildPow2Tree btreeGet spanningSubgraphCount allSimpleGraphs countWhere
    have : isSpanningSubgraphOn G S emptyGraph0 = true :=
      (isSpanningSubgraphOn_eq_true_iff G S emptyGraph0).mpr fun u => u.elim0
    simp [this]
  | k + 1, G, S => by
    let G₀ := initGraph G
    let g_nb := lastNeighbors G
    let S₀ := fun i : Fin k => S i.castSucc
    unfold buildPow2Tree btreeGet
    have ih := buildPow2Tree_spec k G₀ S₀
    have hadj₀ : (fun i j : Fin k => G.adj i.castSucc j.castSucc) = G₀.adj := rfl
    have hprod : spanningSubgraphCount G S =
        spanningSubgraphCount G₀ S₀ *
          countWhere (allSubsets k) (fun h_nb =>
            (allFin k).all (fun i => !h_nb i || (S₀ i && S (.last k) && g_nb i))) := by
      unfold spanningSubgraphCount
      rw [← countWhere_prod]
      refine countWhere_bij
        (fun H => (initGraph H, lastNeighbors H))
        (fun p => extendGraph p.1 p.2)
        (nodup_allSimpleGraphs (k + 1))
        (nodup_listProd (nodup_allSimpleGraphs k) (nodup_allSubsets k))
        ?_ ?_
      · intro H _ hH
        have hsp := (isSpanningSubgraphOn_eq_true_iff G S H).mp hH
        refine ⟨mem_listProd.mpr ⟨mem_allSimpleGraphs _, mem_allSubsets _⟩, ?_, extendGraph_init_last H⟩
        simp only [Bool.and_eq_true]
        refine ⟨(isSpanningSubgraphOn_eq_true_iff G₀ S₀ _).mpr fun i j hij => ?_, ?_⟩
        · exact hsp i.castSucc j.castSucc hij
        · apply List.all_eq_true.mpr; intro i _
          cases hnb : lastNeighbors H i
          · simp
          · rcases hsp i.castSucc (.last k) hnb with ⟨h1, h2, h3⟩
            simp [S₀, g_nb, lastNeighbors, h1, h2, h3]
      · rintro ⟨H₀, h_nb⟩ _ hp
        simp only [Bool.and_eq_true] at hp
        have hsp₀ := (isSpanningSubgraphOn_eq_true_iff G₀ S₀ H₀).mp hp.1
        refine ⟨mem_allSimpleGraphs _, (isSpanningSubgraphOn_eq_true_iff G S _).mpr ?_, ?_⟩
        · intro u v huv
          unfold extendGraph at huv; dsimp only at huv
          have hul := u.isLt; have hvl := v.isLt
          by_cases hu : u.val < k <;> by_cases hv : v.val < k
          · simp only [hu, hv, ↓reduceDIte] at huv
            rcases hsp₀ ⟨u.val, hu⟩ ⟨v.val, hv⟩ huv with ⟨h1, h2, h3⟩
            have hu_eq : (⟨u.val, hu⟩ : Fin k).castSucc = u := Fin.ext rfl
            have hv_eq : (⟨v.val, hv⟩ : Fin k).castSucc = v := Fin.ext rfl
            dsimp only [S₀, G₀, initGraph] at h1 h2 h3
            rw [hu_eq] at h1 h3; rw [hv_eq] at h2 h3
            exact ⟨h1, h2, h3⟩
          · simp only [hu, hv, ↓reduceDIte] at huv
            have hv_last : v = .last k := Fin.ext (by simp [Fin.last]; omega)
            have hi := List.all_eq_true.mp hp.2 ⟨u.val, hu⟩ (mem_allFin _)
            simp only [huv, Bool.not_true, Bool.false_or, Bool.and_eq_true] at hi
            have hu_eq : (⟨u.val, hu⟩ : Fin k).castSucc = u := Fin.ext rfl
            dsimp only [S₀, g_nb, lastNeighbors] at hi
            rw [hu_eq, ← hv_last] at hi
            exact ⟨hi.1.1, hv_last ▸ hi.1.2, hi.2⟩
          · simp only [hu, hv, ↓reduceDIte] at huv
            have hu_last : u = .last k := Fin.ext (by simp [Fin.last]; omega)
            have hi := List.all_eq_true.mp hp.2 ⟨v.val, hv⟩ (mem_allFin _)
            simp only [huv, Bool.not_true, Bool.false_or, Bool.and_eq_true] at hi
            have hv_eq : (⟨v.val, hv⟩ : Fin k).castSucc = v := Fin.ext rfl
            dsimp only [S₀, g_nb, lastNeighbors] at hi
            rw [hv_eq, ← hu_last] at hi
            exact ⟨hu_last ▸ hi.1.2, hi.1.1, by rw [G.symm u v]; exact hi.2⟩
          · simp [hu, hv] at huv
        · have ⟨e1, e2⟩ := extendGraph_inj (rfl : extendGraph H₀ h_nb = extendGraph H₀ h_nb)
          apply Prod.ext
          · apply SimpleGraphN.ext; funext i j
            unfold initGraph extendGraph; simp [i.isLt, j.isLt]
          · funext i
            unfold lastNeighbors extendGraph
            have hnot : ¬ ((Fin.last k).val < k) := by simp [Fin.last]
            simp [i.isLt, hnot]
    rw [hprod]
    cases hlast : S (.last k)
    · simp only [hlast, Bool.false_eq_true, ↓reduceIte]
      rw [hadj₀, ih]
      have hcnt1 : countWhere (allSubsets k)
          (fun h_nb => (allFin k).all (fun i => !h_nb i || (S₀ i && false && g_nb i))) = 1 := by
        have heq : countWhere (allSubsets k)
            (fun h_nb => (allFin k).all (fun i => !h_nb i || (S₀ i && false && g_nb i))) =
          countWhere (allSubsets k)
            (fun h_nb => isSubmask h_nb (fun _ => false && false)) := by
          unfold countWhere isSubmask; congr 1
          refine List.filter_congr ?_; intro h_nb _
          simp
        rw [heq, countWhere_submasks_eq_pow2 (fun _ => false) (fun _ => false),
            submaskPow2Count_false k]
      rw [hcnt1, Nat.mul_one]
    · simp only [hlast, ↓reduceIte, hadj₀]
      change btreeGet (scaleByNeighbors g_nb (buildPow2Tree k G₀.adj)) S₀ = _
      rw [btreeGet_scaleByNeighbors, ih]
      congr 1
      have heq : countWhere (allSubsets k)
          (fun h_nb => (allFin k).all (fun i => !h_nb i || (S₀ i && true && g_nb i))) =
        countWhere (allSubsets k) (fun h_nb => isSubmask h_nb (fun i => S₀ i && g_nb i)) := by
        unfold countWhere isSubmask; congr 1
        refine List.filter_congr ?_; intro h_nb _
        simp
      rw [heq, countWhere_submasks_eq_pow2]

/-! ### Proof 2: `btreeGet (allConnTree (buildPow2Tree n G.adj)) S = connSpanningSubgraphCount G S` -/

def leftmostLeaf : {k : Nat} → BTree Nat k → Nat
  | 0, .leaf x => x
  | _ + 1, .node l _ => leftmostLeaf l

def btreeLeft {α : Type u} {k : Nat} : BTree α (k + 1) → BTree α k
  | .node l _ => l

def btreeRight {α : Type u} {k : Nat} : BTree α (k + 1) → BTree α k
  | .node _ r => r

theorem leftmostLeaf_buildPow2Tree :
    ∀ (n : Nat) (adj : Fin n → Fin n → Bool), leftmostLeaf (buildPow2Tree n adj) = 1
  | 0, _ => rfl
  | k + 1, _ => leftmostLeaf_buildPow2Tree k _

/-- Uniqueness & exactness of `solveConn` whenever `leftmostLeaf P₀ = 1` and `subsetConv C P₀ = P₁`! -/
theorem solveConn_eq_of_subsetConv :
    ∀ {k : Nat} {P₀ P₁ C : BTree Nat k},
      leftmostLeaf P₀ = 1 → subsetConv C P₀ = P₁ → solveConn P₀ P₁ = C
  | 0, .leaf p0, .leaf p1, .leaf c, h1, hconv => by
    unfold leftmostLeaf at h1; subst h1
    unfold subsetConv at hconv
    cases hconv
    unfold solveConn
    congr 1; omega
  | _ + 1, .node p00 p01, .node p10 p11, .node c0 c1, h1, hconv => by
    have h1' : leftmostLeaf p00 = 1 := h1
    have hleft : subsetConv c0 p00 = p10 := congrArg btreeLeft hconv
    have hright : btreeMap2 (· + ·) (subsetConv c0 p01) (subsetConv c1 p00) = p11 :=
      congrArg btreeRight hconv
    have hc0 : solveConn p00 p10 = c0 := solveConn_eq_of_subsetConv h1' hleft
    change BTree.node (solveConn p00 p10)
      (solveConn p00 (btreeMap2 (· - ·) p11 (subsetConv (solveConn p00 p10) p01))) =
      BTree.node c0 c1
    rw [hc0]
    congr 1
    refine solveConn_eq_of_subsetConv h1' ?_
    apply btree_ext; intro S₀
    rw [← hright, btreeGet_btreeMap2, btreeGet_btreeMap2]
    omega

theorem allSubsets_snoc_bij {k : Nat} (F : (Fin (k + 1) → Bool) → Nat) :
    listSum ((allSubsets (k + 1)).map F) =
      listSum ((allSubsets k).map (fun S₀ => F (snocBool S₀ false))) +
      listSum ((allSubsets k).map (fun S₀ => F (snocBool S₀ true))) := by
  have hbij := listSum_bij_nat
    (L₁ := allSubsets (k + 1))
    (L₂ := listProd (allSubsets k) [false, true])
    (nodup_allSubsets (k + 1))
    (nodup_listProd (nodup_allSubsets k) (.cons (by simp) (.cons (by simp) .nil)))
    (fun S => (fun i => S i.castSucc, S (.last k)))
    (fun p => snocBool p.1 p.2)
    (fun S _ => ⟨mem_listProd.mpr ⟨mem_allSubsets _, by
      dsimp only; cases S (.last k) <;> simp⟩, snocBool_init_last S⟩)
    (fun p _ => ⟨mem_allSubsets _, by cases p; apply Prod.ext <;> simp⟩)
    F (fun p => F (snocBool p.1 p.2))
    (fun S _ => by dsimp only; rw [snocBool_init_last])
  rw [hbij]
  clear hbij
  induction (allSubsets k) with
  | nil => rfl
  | cons S₀ Ss ih =>
    simp only [listProd, List.map_append, listSum_append, List.map, listSum, ih]
    omega

theorem btreeGet_subsetConv :
    ∀ {k : Nat} (A B : BTree Nat k) (S₀ : Fin k → Bool),
      btreeGet (subsetConv A B) S₀ =
        listSum ((allSubsets k).map (fun T₀ =>
          if isSubmask T₀ S₀ then btreeGet A T₀ * btreeGet B (diffMask S₀ T₀) else 0))
  | 0, .leaf a, .leaf b, S₀ => by
    unfold subsetConv btreeGet allSubsets allFinFns
    have hsub : isSubmask (fun i : Fin 0 => i.elim0) S₀ = true := rfl
    simp [listSum, hsub]
  | k + 1, .node a0 a1, .node b0 b1, S₀ => by
    rw [allSubsets_snoc_bij]
    conv => lhs; unfold subsetConv btreeGet
    let S' := fun i : Fin k => S₀ i.castSucc
    cases hlast : S₀ (.last k)
    · simp only [hlast, Bool.false_eq_true, ↓reduceIte]
      rw [btreeGet_subsetConv a0 b0]
      have hzero : listSum ((allSubsets k).map (fun T₀ =>
          if isSubmask (snocBool T₀ true) S₀ then
            btreeGet (.node a0 a1) (snocBool T₀ true) *
              btreeGet (.node b0 b1) (diffMask S₀ (snocBool T₀ true))
          else 0)) = 0 := by
        rw [listSum_congr (g := fun _ => 0)]
        · exact listSum_const_zero _
        · intro T₀ _
          have hns : isSubmask (snocBool T₀ true) S₀ = false := by
            apply Bool.eq_false_iff.mpr; intro hs
            have := (isSubmask_eq_true_iff _ _).mp hs (.last k) (by simp)
            rw [hlast] at this; cases this
          simp [hns]
      rw [hzero, Nat.add_zero]
      refine listSum_congr ?_; intro T₀ _
      have hsub_eq : isSubmask (snocBool T₀ false) S₀ = isSubmask T₀ S' := by
        by_cases hs : isSubmask T₀ S' = true
        · have hs' := (isSubmask_eq_true_iff _ _).mp hs
          have lhs : isSubmask (snocBool T₀ false) S₀ = true :=
            (isSubmask_eq_true_iff _ _).mpr fun u hu => by
              unfold snocBool at hu
              by_cases hlt : u.val < k
              · simp only [hlt, ↓reduceDIte] at hu
                exact hs' ⟨u.val, hlt⟩ hu
              · simp [hlt] at hu
          rw [lhs, hs]
        · have hsf := Bool.eq_false_iff.mpr hs
          have lhsf : isSubmask (snocBool T₀ false) S₀ = false := by
            apply Bool.eq_false_iff.mpr; intro h1
            have h1' := (isSubmask_eq_true_iff _ _).mp h1
            apply hs; rw [isSubmask_eq_true_iff]
            intro i hi; exact h1' i.castSucc (by simpa using hi)
          rw [lhsf, hsf]
      dsimp only [S'] at hsub_eq
      rw [hsub_eq]
      split
      · have hd_last : diffMask S₀ (snocBool T₀ false) (.last k) = false := by
          simp [diffMask, hlast]
        have hd_init : (fun i : Fin k => diffMask S₀ (snocBool T₀ false) i.castSucc) = diffMask S' T₀ := by
          funext i; simp [diffMask, S']
        simp [btreeGet, hd_last, hd_init, S']
      · rfl
    · simp only [hlast, ↓reduceIte, btreeGet_btreeMap2]
      rw [btreeGet_subsetConv a0 b1, btreeGet_subsetConv a1 b0]
      congr 1
      · refine listSum_congr ?_; intro T₀ _
        have hsub_eq : isSubmask (snocBool T₀ false) S₀ = isSubmask T₀ S' := by
          by_cases hs : isSubmask T₀ S' = true
          · have hs' := (isSubmask_eq_true_iff _ _).mp hs
            have lhs : isSubmask (snocBool T₀ false) S₀ = true :=
              (isSubmask_eq_true_iff _ _).mpr fun u hu => by
                unfold snocBool at hu
                by_cases hlt : u.val < k
                · simp only [hlt, ↓reduceDIte] at hu
                  exact hs' ⟨u.val, hlt⟩ hu
                · simp [hlt] at hu
            rw [lhs, hs]
          · have hsf := Bool.eq_false_iff.mpr hs
            have lhsf : isSubmask (snocBool T₀ false) S₀ = false := by
              apply Bool.eq_false_iff.mpr; intro h1
              have h1' := (isSubmask_eq_true_iff _ _).mp h1
              apply hs; rw [isSubmask_eq_true_iff]
              intro i hi; exact h1' i.castSucc (by simpa using hi)
            rw [lhsf, hsf]
        dsimp only [S'] at hsub_eq
        rw [hsub_eq]
        split
        · have hd_last : diffMask S₀ (snocBool T₀ false) (.last k) = true := by
            simp [diffMask, hlast]
          have hd_init : (fun i : Fin k => diffMask S₀ (snocBool T₀ false) i.castSucc) = diffMask S' T₀ := by
            funext i; simp [diffMask, S']
          simp [btreeGet, hd_last, hd_init, S']
        · rfl
      · refine listSum_congr ?_; intro T₀ _
        have hsub_eq : isSubmask (snocBool T₀ true) S₀ = isSubmask T₀ S' := by
          by_cases hs : isSubmask T₀ S' = true
          · have hs' := (isSubmask_eq_true_iff _ _).mp hs
            have lhs : isSubmask (snocBool T₀ true) S₀ = true :=
              (isSubmask_eq_true_iff _ _).mpr fun u hu => by
                unfold snocBool at hu
                have hul := u.isLt
                by_cases hlt : u.val < k
                · simp only [hlt, ↓reduceDIte] at hu
                  exact hs' ⟨u.val, hlt⟩ hu
                · have u_eq : u = .last k := Fin.ext (by simp [Fin.last]; omega)
                  rw [u_eq]; exact hlast
            rw [lhs, hs]
          · have hsf := Bool.eq_false_iff.mpr hs
            have lhsf : isSubmask (snocBool T₀ true) S₀ = false := by
              apply Bool.eq_false_iff.mpr; intro h1
              have h1' := (isSubmask_eq_true_iff _ _).mp h1
              apply hs; rw [isSubmask_eq_true_iff]
              intro i hi; exact h1' i.castSucc (by simpa using hi)
            rw [lhsf, hsf]
        dsimp only [S'] at hsub_eq
        rw [hsub_eq]
        split
        · have hd_last : diffMask S₀ (snocBool T₀ true) (.last k) = false := by
            simp [diffMask, hlast]
          have hd_init : (fun i : Fin k => diffMask S₀ (snocBool T₀ true) i.castSucc) = diffMask S' T₀ := by
            funext i; simp [diffMask, S']
          simp [btreeGet, hd_last, hd_init, S']
        · rfl

/-- Restrict edges of `H : SimpleGraphN n` to a vertex mask `M : Fin n → Bool`. -/
def maskGraph {n : Nat} (H : SimpleGraphN n) (M : Fin n → Bool) : SimpleGraphN n where
  adj u v := M u && M v && H.adj u v
  loopless u := by simp [H.loopless]
  symm u v := by rw [H.symm u v]; cases M u <;> cases M v <;> simp

/-- Union of two simple graphs on `Fin n`. -/
def unionSimpleGraph {n : Nat} (H₁ H₂ : SimpleGraphN n) : SimpleGraphN n where
  adj u v := H₁.adj u v || H₂.adj u v
  loopless u := by simp [H₁.loopless, H₂.loopless]
  symm u v := by rw [H₁.symm u v, H₂.symm u v]

theorem reachableIn_snoc_false_iff {k : Nat} (H₀ : SimpleGraphN k) (S₀ : Fin k → Bool)
    (i j : Fin k) :
    ReachableIn (extendGraph H₀ (fun _ => false)).adj (snocBool S₀ false) i.castSucc j.castSucc ↔
      ReachableIn H₀.adj S₀ i j := by
  constructor
  · intro hr
    generalize hu : i.castSucc = u at hr
    generalize hv : j.castSucc = v at hr
    induction hr generalizing i j with
    | @refl z hSz =>
      subst hu
      have hij : i = j := Fin.ext (by simpa using congrArg Fin.val hv.symm)
      subst hij
      simpa using ReachableIn.refl (by simpa using hSz)
    | @step a b c hSa hSb hab _ ih =>
      subst hu
      have hbl : b.val < k := by
        by_cases hlt : b.val < k
        · exact hlt
        · unfold snocBool at hSb; simp [hlt] at hSb
      let b₀ : Fin k := ⟨b.val, hbl⟩
      have hb_eq : b₀.castSucc = b := Fin.ext rfl
      have hab₀ : H₀.adj i b₀ = true := by
        rw [← hb_eq] at hab
        unfold extendGraph at hab; dsimp only at hab
        simpa [i.isLt, b₀.isLt] using hab
      exact .step (by simpa using hSa) (by rw [← hb_eq] at hSb; simpa using hSb)
        hab₀ (ih b₀ j hb_eq hv)
  · intro hr
    induction hr with
    | @refl z hSz => exact .refl (by simpa using hSz)
    | @step a b _ hSa hSb hab _ ih =>
      refine .step (by simpa using hSa) (by simpa using hSb) ?_ ih
      unfold extendGraph; simp [a.isLt, b.isLt, hab]

theorem connSpanning_snoc_false {k : Nat} (G : SimpleGraphN (k + 1)) (S₀ : Fin k → Bool) :
    connSpanningSubgraphCount G (snocBool S₀ false) =
      connSpanningSubgraphCount (initGraph G) S₀ := by
  unfold connSpanningSubgraphCount
  refine countWhere_bij
    initGraph
    (fun H₀ => extendGraph H₀ (fun _ => false))
    (nodup_allSimpleGraphs (k + 1))
    (nodup_allSimpleGraphs k) ?_ ?_
  · intro H _ hH
    simp only [Bool.and_eq_true] at hH
    have hsp := (isSpanningSubgraphOn_eq_true_iff G _ H).mp hH.1
    have hconn := (isConnectedSubgraphBool_eq_true_iff _ _).mp hH.2
    -- Note `lastNeighbors H = fun _ => false` since `snocBool S₀ false (.last k) = false`!
    have hnb : lastNeighbors H = (fun _ => false) := by
      funext i
      cases h : lastNeighbors H i
      · rfl
      · have := (hsp i.castSucc (.last k) h).2.1
        simp at this
    have hH_eq : extendGraph (initGraph H) (fun _ => false) = H := by
      rw [← hnb, extendGraph_init_last]
    refine ⟨mem_allSimpleGraphs _, ?_, hH_eq⟩
    simp only [Bool.and_eq_true]
    refine ⟨(isSpanningSubgraphOn_eq_true_iff _ S₀ _).mpr fun i j hij => ?_,
            (isConnectedSubgraphBool_eq_true_iff _ _).mpr ?_⟩
    · rcases hsp i.castSucc j.castSucc hij with ⟨h1, h2, h3⟩
      exact ⟨by simpa using h1, by simpa using h2, h3⟩
    · rcases hconn with ⟨⟨u₀, hu₀⟩, hwalk⟩
      have hu₀_lt : u₀.val < k := by
        by_cases hlt : u₀.val < k; exact hlt
        unfold snocBool at hu₀; simp [hlt] at hu₀
      refine ⟨⟨⟨u₀.val, hu₀_lt⟩, by unfold snocBool at hu₀; simpa [hu₀_lt] using hu₀⟩, ?_⟩
      intro i j hi hj
      have hw := hwalk i.castSucc j.castSucc (by simpa using hi) (by simpa using hj)
      rw [← hH_eq] at hw
      exact (reachableIn_snoc_false_iff (initGraph H) S₀ i j).mp hw
  · intro H₀ _ hH₀
    simp only [Bool.and_eq_true] at hH₀
    have hsp₀ := (isSpanningSubgraphOn_eq_true_iff _ S₀ H₀).mp hH₀.1
    have hconn₀ := (isConnectedSubgraphBool_eq_true_iff _ _).mp hH₀.2
    refine ⟨mem_allSimpleGraphs _, ?_, ?_⟩
    · simp only [Bool.and_eq_true]
      refine ⟨(isSpanningSubgraphOn_eq_true_iff G _ _).mpr ?_,
              (isConnectedSubgraphBool_eq_true_iff _ _).mpr ?_⟩
      · intro u v huv
        unfold extendGraph at huv; dsimp only at huv
        by_cases hu : u.val < k <;> by_cases hv : v.val < k
        · simp only [hu, hv, ↓reduceDIte] at huv
          rcases hsp₀ ⟨u.val, hu⟩ ⟨v.val, hv⟩ huv with ⟨h1, h2, h3⟩
          exact ⟨by unfold snocBool; simp [hu, h1],
                 by unfold snocBool; simp [hv, h2], h3⟩
        · simp [hu, hv] at huv
        · simp [hu, hv] at huv
        · simp [hu, hv] at huv
      · rcases hconn₀ with ⟨⟨i₀, hi₀⟩, hwalk₀⟩
        refine ⟨⟨i₀.castSucc, by simpa using hi₀⟩, fun u v hu hv => ?_⟩
        have hul : u.val < k := by by_cases h : u.val < k; exact h; unfold snocBool at hu; simp [h] at hu
        have hvl : v.val < k := by by_cases h : v.val < k; exact h; unfold snocBool at hv; simp [h] at hv
        let i : Fin k := ⟨u.val, hul⟩
        let j : Fin k := ⟨v.val, hvl⟩
        have hi : S₀ i = true := by unfold snocBool at hu; simpa [hul] using hu
        have hj : S₀ j = true := by unfold snocBool at hv; simpa [hvl] using hv
        have hr := (reachableIn_snoc_false_iff H₀ S₀ i j).mpr (hwalk₀ i j hi hj)
        have hui : i.castSucc = u := Fin.ext rfl
        have hvj : j.castSucc = v := Fin.ext rfl
        rw [hui, hvj] at hr; exact hr
    · apply SimpleGraphN.ext; funext i j
      unfold initGraph extendGraph; simp [i.isLt, j.isLt]

/-- Combinatorial component-of-last decomposition on `S = snocBool S₀ true`! -/
theorem spanning_snoc_true_decomp {k : Nat} (G : SimpleGraphN (k + 1)) (S₀ : Fin k → Bool) :
    spanningSubgraphCount G (snocBool S₀ true) =
      listSum ((allSubsets k).map (fun T₀ =>
        if isSubmask T₀ S₀ then
          connSpanningSubgraphCount G (snocBool T₀ true) *
            spanningSubgraphCount (initGraph G) (diffMask S₀ T₀)
        else 0)) := by
  let S := snocBool S₀ true
  let compLast (H : SimpleGraphN (k + 1)) : Fin k → Bool :=
    fun i => reachBool H.adj S i.castSucc (.last k)
  unfold spanningSubgraphCount
  rw [countWhere_partition (nodup_allSubsets k) compLast (fun _ _ _ => mem_allSubsets _)]
  refine listSum_congr ?_
  intro T₀ _
  by_cases hsub : isSubmask T₀ S₀ = true
  · simp only [hsub, ↓reduceIte]
    have hsub' := (isSubmask_eq_true_iff T₀ S₀).mp hsub
    let T := snocBool T₀ true
    let R₀ := diffMask S₀ T₀
    let R := snocBool R₀ false
    -- Partition properties of `T` and `R` inside `S`:
    have hTR_disj : ∀ u : Fin (k + 1), T u = true → R u = true → False := by
      intro u hTu hRu
      dsimp only [T, R, R₀] at hTu hRu
      unfold snocBool at hTu hRu
      unfold diffMask at hRu
      by_cases hu : u.val < k
      · simp only [hu, ↓reduceDIte, Bool.and_eq_true, Bool.not_eq_true'] at hTu hRu
        rw [hTu] at hRu; cases hRu.2
      · simp [hu] at hRu
    have hS_or : ∀ u : Fin (k + 1), S u = true → T u = true ∨ R u = true := by
      intro u hSu
      dsimp only [S, T, R, R₀] at hSu ⊢
      unfold snocBool at hSu ⊢
      unfold diffMask
      by_cases hu : u.val < k
      · simp only [hu, ↓reduceDIte] at hSu ⊢
        cases hT : T₀ ⟨u.val, hu⟩
        · right; simp [hSu, hT]
        · left; rfl
      · left; simp [hu]
    have hT_sub_S : ∀ u : Fin (k + 1), T u = true → S u = true := by
      intro u hTu
      dsimp only [S, T] at hTu ⊢
      unfold snocBool at hTu ⊢
      by_cases hu : u.val < k
      · simp only [hu, ↓reduceDIte] at hTu ⊢; exact hsub' _ hTu
      · simp [hu]
    unfold connSpanningSubgraphCount
    rw [← countWhere_prod]
    refine countWhere_bij
      (fun H => (maskGraph H T, initGraph (maskGraph H R)))
      (fun p => unionSimpleGraph p.1 (extendGraph p.2 (fun _ => false)))
      (nodup_allSimpleGraphs (k + 1))
      (nodup_listProd (nodup_allSimpleGraphs (k + 1)) (nodup_allSimpleGraphs k))
      ?_ ?_
    · intro H _ hH
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hH
      have hsp := (isSpanningSubgraphOn_eq_true_iff G S H).mp hH.1
      have hcomp : compLast H = T₀ := hH.2
      -- Key observation: `reachBool H.adj S u (.last k) = T u` for ALL `u : Fin (k + 1)`!
      have hreachT : ∀ u : Fin (k + 1), reachBool H.adj S u (.last k) = T u := by
        intro u
        have hul := u.isLt
        by_cases hu : u.val < k
        · have heq : u = (⟨u.val, hu⟩ : Fin k).castSucc := Fin.ext rfl
          rw [heq]
          have hc := congrFun hcomp ⟨u.val, hu⟩
          simpa [compLast, T, snocBool, hu] using hc
        · have hu_last : u = .last k := Fin.ext (by simp [Fin.last]; omega)
          rw [hu_last]
          have hr : reachBool H.adj S (.last k) (.last k) = true :=
            (reachBool_eq_true_iff H.adj S _ _).mpr (.refl (by simp [S]))
          simpa [T] using hr
      -- Hence NO edge of `H` crosses between `T` and `R`!
      have hno_cross : ∀ u v : Fin (k + 1), H.adj u v = true →
          (T u = true ∧ T v = true) ∨ (R u = true ∧ R v = true) := by
        intro u v huv
        rcases hsp u v huv with ⟨hSu, hSv, _⟩
        rcases hS_or u hSu with hTu | hRu <;> rcases hS_or v hSv with hTv | hRv
        · exact Or.inl ⟨hTu, hTv⟩
        · exfalso
          have hvu : H.adj v u = true := by rw [H.symm v u]; exact huv
          have hru : ReachableIn H.adj S u (.last k) :=
            (reachBool_eq_true_iff _ _ _ _).mp (by rw [hreachT u]; exact hTu)
          have hrv : ReachableIn H.adj S v (.last k) := .step hSv hSu hvu hru
          have hTv : T v = true := by
            rw [← hreachT v]; exact (reachBool_eq_true_iff _ _ _ _).mpr hrv
          exact hTR_disj v hTv hRv
        · exfalso
          have hrv : ReachableIn H.adj S v (.last k) :=
            (reachBool_eq_true_iff _ _ _ _).mp (by rw [hreachT v]; exact hTv)
          have hru : ReachableIn H.adj S u (.last k) := .step hSu hSv huv hrv
          have hTu : T u = true := by
            rw [← hreachT u]; exact (reachBool_eq_true_iff _ _ _ _).mpr hru
          exact hTR_disj u hTu hRu
        · exact Or.inr ⟨hRu, hRv⟩
      -- Any walk in `(S, H.adj)` starting inside `T` stays inside `T` and lifts to `(T, (maskGraph H T).adj)`!
      have hwalk_in_T : ∀ u v : Fin (k + 1), ReachableIn H.adj S u v → T u = true →
          ReachableIn (maskGraph H T).adj T u v := by
        intro u v hr
        induction hr with
        | refl _ => intro hTu; exact .refl hTu
        | @step a b _ _ _ hab _ ih =>
          intro hTa
          have hTb : T b = true := by
            rcases hno_cross a b hab with ⟨_, hTb⟩ | ⟨hRa, _⟩
            · exact hTb
            · exact False.elim (hTR_disj a hTa hRa)
          refine .step hTa hTb ?_ (ih hTb)
          unfold maskGraph; simp [hTa, hTb, hab]
      refine ⟨mem_listProd.mpr ⟨mem_allSimpleGraphs _, mem_allSimpleGraphs _⟩, ?_, ?_⟩
      · simp only [Bool.and_eq_true]
        refine ⟨⟨(isSpanningSubgraphOn_eq_true_iff G T _).mpr ?_,
                 (isConnectedSubgraphBool_eq_true_iff _ _).mpr ?_⟩,
                (isSpanningSubgraphOn_eq_true_iff (initGraph G) R₀ _).mpr ?_⟩
        · intro u v huv
          unfold maskGraph at huv; dsimp only at huv
          simp only [Bool.and_eq_true] at huv
          exact ⟨huv.1.1, huv.1.2, (hsp u v huv.2).2.2⟩
        · refine ⟨⟨.last k, by simp [T]⟩, fun u v hTu hTv => ?_⟩
          have hru : ReachableIn H.adj S u (.last k) :=
            (reachBool_eq_true_iff _ _ _ _).mp (by rw [hreachT u]; exact hTu)
          have hrv : ReachableIn H.adj S v (.last k) :=
            (reachBool_eq_true_iff _ _ _ _).mp (by rw [hreachT v]; exact hTv)
          have hruv := hru.trans (ReachableIn.symm_of_symm H.symm hrv)
          exact hwalk_in_T u v hruv hTu
        · intro i j hij
          unfold initGraph maskGraph at hij; dsimp only at hij
          simp only [Bool.and_eq_true] at hij
          exact ⟨by simpa [R] using hij.1.1,
                 by simpa [R] using hij.1.2,
                 (hsp i.castSucc j.castSucc hij.2).2.2⟩
      · -- Reconstruct `H`:
        apply SimpleGraphN.ext; funext u v
        unfold unionSimpleGraph maskGraph extendGraph initGraph; dsimp only
        cases huv : H.adj u v
        · by_cases hu : u.val < k <;> by_cases hv : v.val < k
          · have h1 : H.adj (⟨u.val, hu⟩ : Fin k).castSucc (⟨v.val, hv⟩ : Fin k).castSucc = false := huv
            simp [hu, hv, huv, h1]
          · simp [hu, hv, huv]
          · simp [hu, hv, huv]
          · simp [hu, hv, huv]
        · rcases hno_cross u v huv with ⟨hTu, hTv⟩ | ⟨hRu, hRv⟩
          · simp [hTu, hTv, huv]
          · have hul : u.val < k := by by_cases h : u.val < k; exact h; unfold R snocBool at hRu; simp [h] at hRu
            have hvl : v.val < k := by by_cases h : v.val < k; exact h; unfold R snocBool at hRv; simp [h] at hRv
            simp [hul, hvl, hRu, hRv, huv]
    · rintro ⟨H₁, H₂⟩ _ hp
      simp only [Bool.and_eq_true] at hp
      have hsp₁ := (isSpanningSubgraphOn_eq_true_iff G T H₁).mp hp.1.1
      have hconn₁ := (isConnectedSubgraphBool_eq_true_iff _ _).mp hp.1.2
      have hsp₂ := (isSpanningSubgraphOn_eq_true_iff (initGraph G) R₀ H₂).mp hp.2
      let H₂' := extendGraph H₂ (fun _ => false)
      let H := unionSimpleGraph H₁ H₂'
      have hH₂'_R : ∀ u v : Fin (k + 1), H₂'.adj u v = true →
          R u = true ∧ R v = true ∧ G.adj u v = true := by
        intro u v huv
        unfold H₂' extendGraph at huv; dsimp only at huv
        by_cases hu : u.val < k <;> by_cases hv : v.val < k
        · simp only [hu, hv, ↓reduceDIte] at huv
          rcases hsp₂ ⟨u.val, hu⟩ ⟨v.val, hv⟩ huv with ⟨h1, h2, h3⟩
          exact ⟨by unfold R snocBool; simp [hu, h1],
                 by unfold R snocBool; simp [hv, h2], h3⟩
        · simp [hu, hv] at huv
        · simp [hu, hv] at huv
        · simp [hu, hv] at huv
      have hR_sub_S : ∀ u : Fin (k + 1), R u = true → S u = true := by
        intro u hRu
        dsimp only [S, R, R₀] at hRu ⊢
        unfold snocBool at hRu ⊢
        by_cases hu : u.val < k
        · simp only [hu, ↓reduceDIte, diffMask, Bool.and_eq_true] at hRu ⊢
          exact hRu.1
        · simp [hu] at hRu
      refine ⟨mem_allSimpleGraphs _, ?_, ?_⟩
      · simp only [Bool.and_eq_true, decide_eq_true_eq]
        refine ⟨(isSpanningSubgraphOn_eq_true_iff G S H).mpr ?_, ?_⟩
        · intro u v huv
          unfold H unionSimpleGraph at huv; dsimp only at huv
          simp only [Bool.or_eq_true] at huv
          rcases huv with h1 | h2
          · rcases hsp₁ u v h1 with ⟨hTu, hTv, hG⟩
            exact ⟨hT_sub_S u hTu, hT_sub_S v hTv, hG⟩
          · rcases hH₂'_R u v h2 with ⟨hRu, hRv, hG⟩
            exact ⟨hR_sub_S u hRu, hR_sub_S v hRv, hG⟩
        · -- Show `compLast H = T₀`!
          have hlift_walk : ∀ u w : Fin (k + 1),
              ReachableIn H₁.adj T u w → ReachableIn H.adj S u w := by
            intro u w hw
            induction hw with
            | @refl z hTz => exact .refl (hT_sub_S z hTz)
            | @step a b _ hTa hTb hab _ ih =>
              refine .step (hT_sub_S a hTa) (hT_sub_S b hTb) ?_ ih
              unfold H unionSimpleGraph; simp [hab]
          funext i
          by_cases hTi : T₀ i = true
          · have hr₁ := hconn₁.2 i.castSucc (.last k) (by simpa [T] using hTi) (by simp [T])
            have hrH := hlift_walk _ _ hr₁
            exact ((reachBool_eq_true_iff H.adj S _ _).mpr hrH).trans hTi.symm
          · have hTiF := Bool.eq_false_iff.mpr hTi
            rw [hTiF]
            apply Bool.eq_false_iff.mpr; intro hr
            have hr' := (reachBool_eq_true_iff H.adj S _ _).mp hr
            have hendT : ∀ u w : Fin (k + 1), ReachableIn H.adj S u w → T w = true → T u = true := by
              intro u w hw
              induction hw with
              | refl _ => intro hTw; exact hTw
              | @step a b _ _ _ hab _ ih =>
                intro hTw
                have hTb := ih hTw
                unfold H unionSimpleGraph at hab; dsimp only at hab
                simp only [Bool.or_eq_true] at hab
                rcases hab with h1 | h2
                · exact (hsp₁ a b h1).1
                · exact False.elim (hTR_disj b hTb (hH₂'_R a b h2).2.1)
            have hT_cast := hendT i.castSucc (.last k) hr' (by simp [T])
            simp [T, hTiF] at hT_cast
      · apply Prod.ext
        · apply SimpleGraphN.ext; funext u v
          dsimp only
          change (maskGraph H T).adj u v = H₁.adj u v
          unfold maskGraph H unionSimpleGraph; dsimp only
          cases h1 : H₁.adj u v
          · cases h2 : H₂'.adj u v
            · simp
            · rcases hH₂'_R u v h2 with ⟨hRu, _, _⟩
              cases hTu : T u
              · simp
              · exact False.elim (hTR_disj u hTu hRu)
          · rcases hsp₁ u v h1 with ⟨hTu, hTv, _⟩
            simp [hTu, hTv]
        · apply SimpleGraphN.ext; funext i j
          dsimp only
          change (initGraph (maskGraph H R)).adj i j = H₂.adj i j
          unfold initGraph maskGraph H unionSimpleGraph; dsimp only
          cases h2 : H₂.adj i j
          · have h2' : H₂'.adj i.castSucc j.castSucc = false := by
              unfold H₂' extendGraph; simp [i.isLt, j.isLt, h2]
            cases h1 : H₁.adj i.castSucc j.castSucc
            · simp [h2']
            · rcases hsp₁ _ _ h1 with ⟨hTi, _, _⟩
              cases hRi : R i.castSucc
              · simp
              · exact False.elim (hTR_disj _ hTi hRi)
          · have h2' : H₂'.adj i.castSucc j.castSucc = true := by
              unfold H₂' extendGraph; simp [i.isLt, j.isLt, h2]
            rcases hsp₂ i j h2 with ⟨hRi, hRj, _⟩
            have hRi' : R i.castSucc = true := by simpa [R] using hRi
            have hRj' : R j.castSucc = true := by simpa [R] using hRj
            simp [hRi', hRj', h2']
  · have hsubF := Bool.eq_false_iff.mpr hsub
    simp only [hsubF, Bool.false_eq_true, ↓reduceIte]
    -- Fiber is empty because `isSubmask (compLast H) S₀ = true` for every `H`!
    unfold countWhere
    suffices hnil : (allSimpleGraphs (k + 1)).filter
        (fun H => isSpanningSubgraphOn G S H && decide (compLast H = T₀)) = [] by
      rw [hnil]; rfl
    apply List.filter_eq_nil_iff.mpr
    intro H _ htrue
    simp only [Bool.and_eq_true, decide_eq_true_eq] at htrue
    apply hsub
    rw [← htrue.2, isSubmask_eq_true_iff]
    intro i hi
    have hr := (reachBool_eq_true_iff H.adj S _ _).mp hi
    have hmem := hr.left_mem
    simpa [S] using hmem

theorem allConnTree_spec :
    ∀ (n : Nat) (G : SimpleGraphN n) (S : Fin n → Bool),
      btreeGet (allConnTree (buildPow2Tree n G.adj)) S = connSpanningSubgraphCount G S
  | 0, G, S => by
    unfold allConnTree buildPow2Tree btreeGet connSpanningSubgraphCount countWhere
    suffices hnil : (allSimpleGraphs 0).filter
        (fun H => isSpanningSubgraphOn G S H && isConnectedSubgraphBool H.adj S) = [] by
      rw [hnil]; rfl
    apply List.filter_eq_nil_iff.mpr
    intro H _ h
    simp only [Bool.and_eq_true] at h
    rcases (isConnectedSubgraphBool_eq_true_iff H.adj S).mp h.2 with ⟨⟨u₀, _⟩, _⟩
    exact u₀.elim0
  | k + 1, G, S => by
    let G₀ := initGraph G
    let S₀ := fun i : Fin k => S i.castSucc
    have hp0 : buildPow2Tree k (fun i j => G.adj i.castSucc j.castSucc) = buildPow2Tree k G₀.adj := rfl
    unfold buildPow2Tree allConnTree btreeGet
    rw [hp0]
    cases hlast : S (.last k)
    · simp only [hlast, Bool.false_eq_true, ↓reduceIte]
      rw [allConnTree_spec k G₀ S₀]
      have hS_eq : S = snocBool S₀ false := by
        have := (snocBool_init_last S).symm
        rw [hlast] at this; exact this
      rw [hS_eq, connSpanning_snoc_false]
    · simp only [hlast, ↓reduceIte]
      let P₀ := buildPow2Tree k G₀.adj
      let P₁ := scaleByNeighbors (lastNeighbors G) P₀
      let C_true := btreeOfFn k (fun T₀ => connSpanningSubgraphCount G (snocBool T₀ true))
      have hconv : subsetConv C_true P₀ = P₁ := by
        apply btree_ext; intro U₀
        rw [btreeGet_subsetConv]
        have hp1 : btreeGet P₁ U₀ = spanningSubgraphCount G (snocBool U₀ true) := by
          have := buildPow2Tree_spec (k + 1) G (snocBool U₀ true)
          simpa [buildPow2Tree, btreeGet, P₁, P₀, lastNeighbors, initGraph] using this
        rw [hp1, spanning_snoc_true_decomp G U₀]
        refine listSum_congr ?_; intro T₀ _
        split
        · rw [btreeGet_btreeOfFn, buildPow2Tree_spec k G₀ (diffMask U₀ T₀)]
        · rfl
      have hsolve : solveConn P₀ P₁ = C_true :=
        solveConn_eq_of_subsetConv (leftmostLeaf_buildPow2Tree k G₀.adj) hconv
      change btreeGet (solveConn P₀ P₁) S₀ = _
      rw [hsolve, btreeGet_btreeOfFn]
      have hS_eq : S = snocBool S₀ true := by
        have := (snocBool_init_last S).symm
        rw [hlast] at this; exact this
      rw [← hS_eq]

/-! ### Proof 3: `sumByOrder` Sums Entries by `subsetCard S = d` -/

theorem subsetCard_snocBool {k : Nat} (S₀ : Fin k → Bool) (b : Bool) :
    subsetCard (snocBool S₀ b) = subsetCard S₀ + (if b then 1 else 0) := by
  -- Use `allFin (k + 1)` vs `allFin k` via bijection with `(allFin k).map Fin.castSucc ++ [.last k]`!
  have hbij := countWhere_bij (L₁ := allFin (k + 1))
    (L₂ := (allFin k).map Fin.castSucc ++ [.last k])
    (P₁ := snocBool S₀ b) (P₂ := snocBool S₀ b)
    id id
    (nodup_allFin (k + 1))
    (nodup_append
      (nodup_map_of_inj_on (nodup_allFin k) fun i _ j _ h =>
        Fin.ext (by simpa using congrArg Fin.val h))
      (.cons (by simp) .nil)
      (fun z hz1 hz2 => by
        rcases List.mem_map.mp hz1 with ⟨i, _, rfl⟩
        simp only [List.mem_singleton] at hz2
        have := congrArg Fin.val hz2
        have hil := i.isLt
        simp [Fin.last] at this; omega))
    (fun u _ hu => ⟨by
      have hul := u.isLt
      by_cases hlt : u.val < k
      · exact List.mem_append_left _ (List.mem_map_of_mem (mem_allFin ⟨u.val, hlt⟩))
      · have : u = .last k := Fin.ext (by simp [Fin.last]; omega)
        rw [this]; exact List.mem_append_right _ (List.mem_singleton_self _)
    , hu, rfl⟩)
    (fun u _ hu => ⟨mem_allFin u, hu, rfl⟩)
  unfold subsetCard
  rw [hbij]
  unfold countWhere
  rw [List.filter_append, List.length_append]
  have hleft : (((allFin k).map Fin.castSucc).filter (snocBool S₀ b)).length =
      ((allFin k).filter S₀).length := by
    clear hbij
    induction (allFin k) with
    | nil => rfl
    | cons i is ih =>
      cases hSi : S₀ i <;> simp [List.filter, hSi, ih]
  rw [hleft]
  cases b <;> simp [List.filter]

theorem getD_addNatVecs (xs ys : List Nat) (d : Nat) :
    (addNatVecs xs ys).getD d 0 = xs.getD d 0 + ys.getD d 0 := by
  induction xs generalizing ys d with
  | nil => simp [addNatVecs]
  | cons x xs ih =>
    cases ys with
    | nil => simp [addNatVecs]
    | cons y ys =>
      cases d with
      | zero => simp [addNatVecs]
      | succ d' =>
        simp only [addNatVecs, List.getD_cons_succ]
        exact ih ys d'

theorem length_addNatVecs (xs ys : List Nat) :
    (addNatVecs xs ys).length = max xs.length ys.length := by
  induction xs generalizing ys with
  | nil => simp [addNatVecs]
  | cons x xs ih =>
    cases ys with
    | nil => simp [addNatVecs]
    | cons y ys =>
      simp only [addNatVecs, List.length, ih]
      omega

theorem length_sumByOrder : ∀ {n : Nat} (T : BTree Nat n), (sumByOrder T).length = n + 1
  | 0, .leaf _ => rfl
  | k + 1, .node l r => by
    simp only [sumByOrder, length_addNatVecs, length_sumByOrder l, List.length, length_sumByOrder r]
    omega

theorem sumByOrder_spec :
    ∀ {n : Nat} (T : BTree Nat n) (d : Nat),
      (sumByOrder T).getD d 0 =
        listSum (((allSubsets n).filter (fun S => subsetCard S == d)).map (btreeGet T))
  | 0, .leaf x, d => by
    unfold sumByOrder allSubsets allFinFns
    have hcard : subsetCard (fun i : Fin 0 => i.elim0) = 0 := rfl
    have hget : btreeGet (.leaf x) = (fun _ : Fin 0 → Bool => x) := rfl
    rw [hget]
    cases d with
    | zero => simp [hcard, listSum]
    | succ d' => simp [hcard, listSum]
  | k + 1, .node l r, d => by
    have hfilter_sum : ∀ {α : Type} (L : List α) (P : α → Bool) (f : α → Nat),
        listSum ((L.filter P).map f) = listSum (L.map (fun a => if P a then f a else 0)) := by
      intro α L P f
      induction L with
      | nil => rfl
      | cons a as iha =>
        cases hPa : P a <;> simp [List.filter, hPa, listSum, iha]
    rw [hfilter_sum, allSubsets_snoc_bij]
    change (addNatVecs (sumByOrder l) (0 :: sumByOrder r)).getD d 0 = _
    rw [getD_addNatVecs, sumByOrder_spec l d, hfilter_sum]
    cases d with
    | zero =>
      simp only [List.getD_cons_zero, Nat.add_zero]
      have hzero : listSum ((allSubsets k).map (fun S₀ =>
          if subsetCard (snocBool S₀ true) == 0 then btreeGet (.node l r) (snocBool S₀ true) else 0)) = 0 := by
        rw [listSum_congr (g := fun _ => 0)]
        · exact listSum_const_zero _
        · intro S₀ _
          have : (subsetCard (snocBool S₀ true) == 0) = false := by
            rw [subsetCard_snocBool]; simp
          simp [this]
      rw [hzero, Nat.add_zero]
      refine listSum_congr ?_; intro S₀ _
      rw [subsetCard_snocBool]
      simp [btreeGet]
    | succ d' =>
      simp only [List.getD_cons_succ, sumByOrder_spec r d', hfilter_sum]
      congr 1
      · refine listSum_congr ?_; intro S₀ _
        rw [subsetCard_snocBool]
        simp [btreeGet]
      · refine listSum_congr ?_; intro S₀ _
        have hbeq : (subsetCard (snocBool S₀ true) == d' + 1) = (subsetCard S₀ == d') := by
          rw [subsetCard_snocBool]; simp
        rw [hbeq]
        simp [btreeGet]

theorem tail_eq_map_getD (L : List Nat) (n : Nat) (hlen : L.length = n + 1) :
    L.tail = (List.range n).map (fun i => L.getD (i + 1) 0) := by
  cases L with
  | nil => simp at hlen
  | cons x xs =>
    simp only [List.length] at hlen
    have hxs : xs.length = n := by omega
    simp only [List.tail]
    apply List.ext_getElem
    · simp [hxs]
    · intro i h1 h2
      simp only [List.getElem_map, List.getElem_range]
      clear hlen hxs h2
      induction xs generalizing i x with
      | nil => simp at h1
      | cons y ys ih =>
        cases i with
        | zero => rfl
        | succ i' => exact ih y i' (by simp only [List.length] at h1; omega)

/-- **Exact Equivalence Theorem for `allEdgeSubgraphVec` (`s^sub`)**: -/
theorem allEdgeSubgraphVec_eq_fast {n : Nat} (G : SimpleGraphN n) :
    allEdgeSubgraphVec G = fastAllEdgeSubgraphVec G := by
  unfold fastAllEdgeSubgraphVec allEdgeSubgraphVec allEdgeSubgraphCount
  let T := buildPow2Tree n G.adj
  rw [tail_eq_map_getD (sumByOrder T) n (length_sumByOrder T)]
  refine List.map_congr_left ?_
  intro i _
  rw [sumByOrder_spec T (i + 1)]
  refine listSum_congr ?_
  intro S _
  exact (buildPow2Tree_spec n G S).symm

/-- **Exact Equivalence Theorem for `connEdgeSubgraphVec` (`c^sub`)**: -/
theorem connEdgeSubgraphVec_eq_fast {n : Nat} (G : SimpleGraphN n) :
    connEdgeSubgraphVec G = fastConnEdgeSubgraphVec G := by
  unfold fastConnEdgeSubgraphVec connEdgeSubgraphVec connEdgeSubgraphCount
  let T := allConnTree (buildPow2Tree n G.adj)
  rw [tail_eq_map_getD (sumByOrder T) n (length_sumByOrder T)]
  refine List.map_congr_left ?_
  intro i _
  rw [sumByOrder_spec T (i + 1)]
  refine listSum_congr ?_
  intro S _
  exact (allConnTree_spec n G S).symm

end Conjecture00000003970
