/-
  Conjecture 00000003970 — Canonical Simple Graph Reduction (1 ≤ n ≤ 7)
  and Verified Binary-Search-Tree Injectivity Checker
  Pure Core Lean 4.19.0 (zero external dependencies).
-/

import Conjecture00000003970.FastSubgraphEval
import Conjecture00000003970.CanonCertsData

namespace Conjecture00000003970

/-! ### `NatBST` Membership Soundness -/

def bstContains : NatBST → Nat → Bool
  | .empty, _ => false
  | .branch v l r, x =>
    if x == v then true
    else if x < v then bstContains l x
    else bstContains r x

def bstToList : NatBST → List Nat
  | .empty => []
  | .branch v l r => v :: (bstToList l ++ bstToList r)

theorem mem_bstToList_of_bstContains :
    ∀ {t : NatBST} {x : Nat}, bstContains t x = true → x ∈ bstToList t
  | .empty, _, h => by cases h
  | .branch v l r, x, h => by
    unfold bstContains at h
    by_cases hxv : x == v
    · have hxv' : x = v := of_decide_eq_true (by simpa using hxv)
      subst hxv'
      exact List.mem_cons_self ..
    · simp only [hxv, Bool.false_eq_true, ↓reduceIte] at h
      by_cases hlt : x < v
      · simp only [hlt, ↓reduceIte] at h
        exact List.mem_cons_of_mem _ (List.mem_append_left _ (mem_bstToList_of_bstContains h))
      · simp only [hlt, ↓reduceIte] at h
        exact List.mem_cons_of_mem _ (List.mem_append_right _ (mem_bstToList_of_bstContains h))

/-! ### Bit-Packing & Adjacency Bitmask Representation of `SimpleGraphN n` -/

def testBitNat (m k : Nat) : Bool :=
  ((m >>> k) &&& 1) == 1

theorem shiftRight_add_one (m k : Nat) : m >>> (k + 1) = (m / 2) >>> k := by
  induction k generalizing m with
  | zero =>
    change m >>> 1 = m / 2
    exact Nat.shiftRight_eq_div_pow m 1
  | succ k' ih =>
    rw [Nat.shiftRight_succ, ih m, Nat.shiftRight_succ]

theorem and_one_eq_mod_two (m : Nat) : (m &&& 1) = m % 2 := by
  change Nat.land m (2 ^ 1 - 1) = m % 2 ^ 1
  exact Nat.and_two_pow_sub_one_eq_mod m 1

theorem testBitNat_zero (m : Nat) : testBitNat m 0 = (m % 2 == 1) := by
  unfold testBitNat
  change ((m &&& 1) == 1) = (m % 2 == 1)
  rw [and_one_eq_mod_two]

theorem testBitNat_succ (m k : Nat) : testBitNat m (k + 1) = testBitNat (m / 2) k := by
  unfold testBitNat
  rw [shiftRight_add_one]

def packBools : List Bool → Nat
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * packBools bs

theorem packBools_lt_pow2 : ∀ (bs : List Bool), packBools bs < 2 ^ bs.length
  | [] => by decide
  | b :: bs => by
    have ih := packBools_lt_pow2 bs
    simp only [packBools, List.length, Nat.pow_succ]
    cases b <;> simp <;> omega

theorem testBitNat_packBools :
    ∀ (bs : List Bool) (k : Nat) (hk : k < bs.length),
      testBitNat (packBools bs) k = bs[k]'hk
  | [], _, hk => by cases hk
  | b :: bs, 0, _ => by
    rw [testBitNat_zero]
    unfold packBools
    cases b
    · have : (0 + 2 * packBools bs) % 2 = 0 := by omega
      simp [this]
    · have : (1 + 2 * packBools bs) % 2 = 1 := by omega
      simp [this]
  | b :: bs, k + 1, hk => by
    rw [testBitNat_succ]
    unfold packBools
    have hdiv : ((if b then 1 else 0) + 2 * packBools bs) / 2 = packBools bs := by
      cases b <;> simp <;> omega
    rw [hdiv]
    exact testBitNat_packBools bs k (by simp only [List.length] at hk; omega)

/-- Pure `Nat` edge query on an `n × n` adjacency bitmask. -/
def hasMaskEdge (n mask u v : Nat) : Bool :=
  !(u == v) && (testBitNat mask (u * n + v) || testBitNat mask (v * n + u))

/-- Decode an `n × n` adjacency bitmask into a `SimpleGraphN n`. -/
def graphOfAdjMask (n mask : Nat) : SimpleGraphN n where
  adj u v := hasMaskEdge n mask u.val v.val
  loopless u := by simp [hasMaskEdge]
  symm u v := by
    unfold hasMaskEdge
    by_cases huv : u.val = v.val
    · simp [huv]
    · have hvu : v.val ≠ u.val := fun e => huv e.symm
      have b1 : (u.val == v.val) = false := Bool.eq_false_iff.mpr (fun e => huv (of_decide_eq_true (by simpa using e)))
      have b2 : (v.val == u.val) = false := Bool.eq_false_iff.mpr (fun e => hvu (of_decide_eq_true (by simpa using e)))
      simp only [b1, b2, Bool.not_false, Bool.true_and]
      exact Bool.or_comm _ _

/-- Encode ANY `G : SimpleGraphN n` into its `n × n` adjacency bitmask. -/
def adjMaskOfGraph {n : Nat} (G : SimpleGraphN n) : Nat :=
  packBools ((List.range (n * n)).map (fun k =>
    if h : k / n < n ∧ k % n < n then G.adj ⟨k / n, h.1⟩ ⟨k % n, h.2⟩ else false))

theorem mul_add_div_mod {n : Nat} (u v : Fin n) :
    (u.val * n + v.val) < n * n ∧
    (u.val * n + v.val) / n = u.val ∧
    (u.val * n + v.val) % n = v.val := by
  have hul := u.isLt
  have hvl := v.isLt
  have hn : 0 < n := by omega
  have hlt : u.val * n + v.val < n * n := by
    have h1 : (u.val + 1) * n ≤ n * n := Nat.mul_le_mul_right n (by omega)
    have h2 : (u.val + 1) * n = u.val * n + n := Nat.add_one_mul u.val n
    omega
  have hdiv : (u.val * n + v.val) / n = u.val := by
    rw [Nat.mul_comm u.val n, Nat.mul_add_div hn, Nat.div_eq_of_lt hvl, Nat.add_zero]
  have hmod : (u.val * n + v.val) % n = v.val := by
    rw [Nat.mul_comm u.val n, Nat.mul_add_mod, Nat.mod_eq_of_lt hvl]
  exact ⟨hlt, hdiv, hmod⟩

theorem graphOfAdjMask_adjMaskOfGraph {n : Nat} (G : SimpleGraphN n) :
    graphOfAdjMask n (adjMaskOfGraph G) = G := by
  apply SimpleGraphN.ext; funext u v
  unfold graphOfAdjMask hasMaskEdge adjMaskOfGraph; dsimp only
  by_cases huv : u = v
  · subst huv; simp [G.loopless]
  · have b : (u.val == v.val) = false :=
      Bool.eq_false_iff.mpr (fun e => huv (Fin.ext (of_decide_eq_true (by simpa using e))))
    simp only [b, Bool.not_false, Bool.true_and]
    have ⟨hlt1, hdiv1, hmod1⟩ := mul_add_div_mod u v
    have ⟨hlt2, hdiv2, hmod2⟩ := mul_add_div_mod v u
    let bs := (List.range (n * n)).map (fun k =>
      if h : k / n < n ∧ k % n < n then G.adj ⟨k / n, h.1⟩ ⟨k % n, h.2⟩ else false)
    have ht1 : testBitNat (packBools bs) (u.val * n + v.val) = G.adj u v := by
      rw [testBitNat_packBools bs _ (by simp [bs, hlt1])]
      simp only [bs, List.getElem_map, List.getElem_range]
      have hcond : (u.val * n + v.val) / n < n ∧ (u.val * n + v.val) % n < n :=
        ⟨by rw [hdiv1]; exact u.isLt, by rw [hmod1]; exact v.isLt⟩
      rw [dif_pos hcond]
      congr 1
      · exact Fin.ext hdiv1
      · exact Fin.ext hmod1
    have ht2 : testBitNat (packBools bs) (v.val * n + u.val) = G.adj v u := by
      rw [testBitNat_packBools bs _ (by simp [bs, hlt2])]
      simp only [bs, List.getElem_map, List.getElem_range]
      have hcond : (v.val * n + u.val) / n < n ∧ (v.val * n + u.val) % n < n :=
        ⟨by rw [hdiv2]; exact v.isLt, by rw [hmod2]; exact u.isLt⟩
      rw [dif_pos hcond]
      congr 1
      · exact Fin.ext hdiv2
      · exact Fin.ext hmod2
    rw [ht1, ht2, G.symm v u, Bool.or_self]

/-! ### Minimum-Degree Vertex & Inductive Certificate Verification (`n → n + 1`) -/

theorem exists_min_on_list {α : Type u} (f : α → Nat) :
    ∀ {L : List α}, L ≠ [] → ∃ x ∈ L, ∀ y ∈ L, f x ≤ f y
  | [], h => False.elim (h rfl)
  | [x], _ => ⟨x, List.mem_singleton_self _, fun y hy => by
      rcases List.mem_singleton.mp hy with rfl; exact Nat.le_refl _⟩
  | x :: y :: ys, _ => by
    rcases exists_min_on_list f (L := y :: ys) (by simp) with ⟨m, hm, hmin⟩
    by_cases hxm : f x ≤ f m
    · refine ⟨x, List.mem_cons_self .., fun z hz => ?_⟩
      rcases List.mem_cons.mp hz with rfl | hzs
      · exact Nat.le_refl _
      · exact Nat.le_trans hxm (hmin z hzs)
    · refine ⟨m, List.mem_cons_of_mem _ hm, fun z hz => ?_⟩
      rcases List.mem_cons.mp hz with rfl | hzs
      · omega
      · exact hmin z hzs

theorem exists_min_deg_vertex {n : Nat} (G : SimpleGraphN (n + 1)) :
    ∃ v : Fin (n + 1), ∀ u : Fin (n + 1), vertexDeg G v ≤ vertexDeg G u := by
  rcases exists_min_on_list (vertexDeg G) (L := allFin (n + 1)) (by simp [allFin]) with ⟨v, _, hv⟩
  exact ⟨v, fun u => hv u (mem_allFin u)⟩

def swapFin {m : Nat} (a b x : Fin m) : Fin m :=
  if x = a then b else if x = b then a else x

theorem swapFin_invol' {m : Nat} (a b x : Fin m) :
    swapFin a b (swapFin a b x) = x := by
  unfold swapFin
  by_cases hab : a = b
  · subst hab; by_cases hxa : x = a <;> simp [hxa]
  · by_cases hxa : x = a
    · rw [hxa]; have hba : b ≠ a := fun e => hab e.symm; simp [hba]
    · by_cases hxb : x = b
      · rw [hxb]; simp [hab]
      · simp [hxa, hxb]

def swapGraphVertices {m : Nat} (G : SimpleGraphN m) (a b : Fin m) : SimpleGraphN m where
  adj u v := G.adj (swapFin a b u) (swapFin a b v)
  loopless _ := G.loopless _
  symm _ _ := G.symm _ _

def isoSwapVertices {m : Nat} (G : SimpleGraphN m) (a b : Fin m) :
    IsoWitness G (swapGraphVertices G a b) where
  toFun := swapFin a b
  invFun := swapFin a b
  left_inv := swapFin_invol' a b
  right_inv := swapFin_invol' a b
  map_adj u v := by
    unfold swapGraphVertices; dsimp only
    rw [swapFin_invol', swapFin_invol']

def liftIsoExtend {n : Nat} {G₀ H₀ : SimpleGraphN n}
    (w : IsoWitness G₀ H₀) (nb : Fin n → Bool) :
    IsoWitness (extendGraph G₀ nb) (extendGraph H₀ (fun j => nb (w.invFun j))) where
  toFun := liftFixLast w.toFun
  invFun := liftFixLast w.invFun
  left_inv x := by
    apply Fin.ext
    rw [liftFixLast_val, liftFixLast_val]
    have hxl := x.isLt
    by_cases hx : x.val < n
    · have hwx := (w.toFun ⟨x.val, hx⟩).isLt
      simp only [hx, hwx, ↓reduceDIte]
      exact congrArg Fin.val (w.left_inv ⟨x.val, hx⟩)
    · have hnot : ¬ (n < n) := by omega
      simp [hx, hnot]; omega
  right_inv y := by
    apply Fin.ext
    rw [liftFixLast_val, liftFixLast_val]
    have hyl := y.isLt
    by_cases hy : y.val < n
    · have hwy := (w.invFun ⟨y.val, hy⟩).isLt
      simp only [hy, hwy, ↓reduceDIte]
      exact congrArg Fin.val (w.right_inv ⟨y.val, hy⟩)
    · have hnot : ¬ (n < n) := by omega
      simp [hy, hnot]; omega
  map_adj u v := by
    unfold extendGraph; dsimp only
    have hul := u.isLt; have hvl := v.isLt
    rw [liftFixLast_val, liftFixLast_val]
    by_cases hu : u.val < n <;> by_cases hv : v.val < n
    · have hwu := (w.toFun ⟨u.val, hu⟩).isLt
      have hwv := (w.toFun ⟨v.val, hv⟩).isLt
      simp only [hu, hv, hwu, hwv, ↓reduceDIte]
      exact w.map_adj ⟨u.val, hu⟩ ⟨v.val, hv⟩
    · have hwu := (w.toFun ⟨u.val, hu⟩).isLt
      have hnot : ¬ (n < n) := by omega
      simp only [hu, hv, hwu, hnot, ↓reduceDIte]
      have heq : (⟨(w.toFun ⟨u.val, hu⟩).val, hwu⟩ : Fin n) = w.toFun ⟨u.val, hu⟩ := Fin.ext rfl
      rw [heq, w.left_inv]
    · have hwv := (w.toFun ⟨v.val, hv⟩).isLt
      have hnot : ¬ (n < n) := by omega
      simp only [hu, hv, hwv, hnot, ↓reduceDIte]
      have heq : (⟨(w.toFun ⟨v.val, hv⟩).val, hwv⟩ : Fin n) = w.toFun ⟨v.val, hv⟩ := Fin.ext rfl
      rw [heq, w.left_inv]
    · have hnot : ¬ (n < n) := by omega
      simp [hu, hv, hnot]

def popcountBits : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, ext => (if testBitNat ext k then 1 else 0) + popcountBits k ext

def maskDeg (n m u : Nat) : Nat :=
  let rec go : Nat → Nat → Nat
    | 0, acc => acc
    | k + 1, acc =>
      go k (if hasMaskEdge n m u k then acc + 1 else acc)
  go n 0

def isValidExtMask (n prevMask ext : Nat) : Bool :=
  let dNew := popcountBits n ext
  let rec checkU : Nat → Bool
    | 0 => true
    | k + 1 =>
      let du := maskDeg n prevMask k + (if testBitNat ext k then 1 else 0)
      decide (dNew ≤ du) && checkU k
  checkU n

def extendMaskGraph (n prevMask ext : Nat) : SimpleGraphN (n + 1) :=
  extendGraph (graphOfAdjMask n prevMask) (fun i => testBitNat ext i.val)

theorem vertexDeg_last_extendMaskGraph (n prevMask ext : Nat) :
    vertexDeg (extendMaskGraph n prevMask ext) (.last n) = popcountBits n ext := by
  unfold vertexDeg
  have heq : (fun v : Fin (n + 1) => (extendMaskGraph n prevMask ext).adj (.last n) v) =
      snocBool (fun i : Fin n => testBitNat ext i.val) false := by
    funext v
    unfold extendMaskGraph extendGraph snocBool; dsimp only
    have hnot : ¬ ((Fin.last n).val < n) := by simp [Fin.last]
    by_cases hv : v.val < n <;> simp [hnot, hv]
  change subsetCard _ = _
  rw [heq, subsetCard_snocBool]
  simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
  clear heq prevMask
  induction n with
  | zero => rfl
  | succ k ih =>
    have hsnoc : (fun i : Fin (k + 1) => testBitNat ext i.val) =
        snocBool (fun j : Fin k => testBitNat ext j.val) (testBitNat ext k) := by
      funext i
      unfold snocBool
      have hil := i.isLt
      by_cases hi : i.val < k
      · simp [hi]
      · have hik : i.val = k := by omega
        simp [hi, hik]
    rw [hsnoc, subsetCard_snocBool, ih]
    conv => rhs; unfold popcountBits
    cases testBitNat ext k <;> simp <;> omega

theorem maskDeg_go_spec (n m u : Nat) :
    ∀ (r acc : Nat), maskDeg.go n m u r acc =
      acc + countWhere (List.range r) (fun k => hasMaskEdge n m u k)
  | 0, acc => by simp [maskDeg.go, countWhere]
  | r + 1, acc => by
    unfold maskDeg.go
    rw [maskDeg_go_spec n m u r, List.range_succ]
    unfold countWhere
    rw [List.filter_append, List.length_append]
    by_cases he : hasMaskEdge n m u r = true
    · simp only [he, ↓reduceIte, List.filter, List.length]; omega
    · have hef := Bool.eq_false_iff.mpr he
      simp only [hef, Bool.false_eq_true, ↓reduceIte, List.filter, List.length]; omega

theorem vertexDeg_castSucc_extendMaskGraph (n prevMask ext : Nat) (i : Fin n) :
    vertexDeg (extendMaskGraph n prevMask ext) i.castSucc =
      maskDeg n prevMask i.val + (if testBitNat ext i.val then 1 else 0) := by
  unfold vertexDeg
  have heq : (fun v : Fin (n + 1) => (extendMaskGraph n prevMask ext).adj i.castSucc v) =
      snocBool (fun j : Fin n => (graphOfAdjMask n prevMask).adj i j) (testBitNat ext i.val) := by
    funext v
    unfold extendMaskGraph extendGraph snocBool; dsimp only
    have hi := i.isLt
    by_cases hv : v.val < n <;> simp [hi, hv]
  change subsetCard _ = _
  rw [heq, subsetCard_snocBool]
  congr 1
  unfold maskDeg
  rw [maskDeg_go_spec, Nat.zero_add]
  unfold subsetCard
  refine countWhere_bij Fin.val
    (fun k => if h : k < n then ⟨k, h⟩ else i)
    (nodup_allFin n)
    (by
      clear prevMask ext i heq
      induction n with
      | zero => exact .nil
      | succ r ihr =>
        rw [List.range_succ]
        refine nodup_append ihr (.cons (by simp) .nil) ?_
        intro z hz1 hz2
        have hlt : z < r := List.mem_range.mp hz1
        simp only [List.mem_singleton] at hz2
        omega)
    ?_ ?_
  · intro j _ hj
    refine ⟨List.mem_range.mpr j.isLt, hj, by simp [j.isLt]⟩
  · intro k hk hpred
    have hlt : k < n := List.mem_range.mp hk
    refine ⟨mem_allFin _, ?_, by simp [hlt]⟩
    simp only [hlt, ↓reduceDIte]
    exact hpred

theorem isValidExtMask_of_minDeg {n : Nat} {prevMask ext : Nat}
    (hmin : ∀ u : Fin (n + 1),
      vertexDeg (extendMaskGraph n prevMask ext) (.last n) ≤
      vertexDeg (extendMaskGraph n prevMask ext) u) :
    isValidExtMask n prevMask ext = true := by
  unfold isValidExtMask
  suffices hgo : ∀ r ≤ n, isValidExtMask.checkU n prevMask ext (popcountBits n ext) r = true by
    exact hgo n (Nat.le_refl n)
  intro r hr
  induction r with
  | zero => rfl
  | succ k ih =>
    unfold isValidExtMask.checkU
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨?_, ih (by omega)⟩
    have hle := hmin ⟨k, by omega⟩
    have hcast : (⟨k, by omega⟩ : Fin n).castSucc = ⟨k, by omega⟩ := rfl
    rw [← hcast, vertexDeg_last_extendMaskGraph, vertexDeg_castSucc_extendMaskGraph] at hle
    exact hle

/-! ### Fast Pure-`Nat` Upper-Triangle Certificate Verifier -/

def decodePermEntry (code i : Nat) : Nat :=
  (code >>> (3 * i)) &&& 7

/-- Pure `Nat` edge query on `extendMaskGraph n prevMask ext`. -/
def hasExtEdge (n prevMask ext u v : Nat) : Bool :=
  if u < n then
    if v < n then hasMaskEdge n prevMask u v
    else testBitNat ext u
  else
    if v < n then testBitNat ext v
    else false

theorem hasExtEdge_eq_adj (n prevMask ext : Nat) (u v : Fin (n + 1)) :
    hasExtEdge n prevMask ext u.val v.val = (extendMaskGraph n prevMask ext).adj u v := by
  unfold hasExtEdge extendMaskGraph extendGraph graphOfAdjMask; dsimp only
  by_cases hu : u.val < n <;> by_cases hv : v.val < n <;> simp [hu, hv]

/-- Pure `Nat` bijection check on `0 .. m - 1` via structural countdown! -/
def checkPermBijection (m pCode pinvCode : Nat) : Nat → Bool
  | 0 => true
  | i + 1 =>
    let pi := decodePermEntry pCode i
    let pii := decodePermEntry pinvCode i
    decide (pi < m) && decide (pii < m) &&
    (decodePermEntry pinvCode pi == i) &&
    (decodePermEntry pCode pii == i) &&
    checkPermBijection m pCode pinvCode i

/-- Pure `Nat` upper-triangle edge check (`0 ≤ i < j < n + 1`, only `n*(n+1)/2` checks, zero `Fin`/`dite`!) -/
def checkUpperEdges (n pCode prevMask ext tMask : Nat) : Nat → Bool
  | 0 => true
  | j + 1 =>
    let pj := decodePermEntry pCode j
    let rec checkI : Nat → Bool
      | 0 => true
      | i + 1 =>
        let pi := decodePermEntry pCode i
        (hasExtEdge n prevMask ext i j == hasMaskEdge (n + 1) tMask pi pj) && checkI i
    checkI j && checkUpperEdges n pCode prevMask ext tMask j

def checkIsoMaskExt (n pCode pinvCode prevMask ext tMask : Nat) : Bool :=
  checkPermBijection (n + 1) pCode pinvCode (n + 1) &&
  checkUpperEdges n pCode prevMask ext tMask (n + 1)

theorem checkPermBijection_spec (m pCode pinvCode : Nat) :
    ∀ r, checkPermBijection m pCode pinvCode r = true →
      ∀ i < r,
        decodePermEntry pCode i < m ∧
        decodePermEntry pinvCode i < m ∧
        decodePermEntry pinvCode (decodePermEntry pCode i) = i ∧
        decodePermEntry pCode (decodePermEntry pinvCode i) = i
  | 0, _, _, hi => by omega
  | r + 1, hok, i, hi => by
    unfold checkPermBijection at hok
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    by_cases hir : i = r
    · subst hir
      exact ⟨hok.1.1.1.1, hok.1.1.1.2,
             of_decide_eq_true (by simpa using hok.1.1.2),
             of_decide_eq_true (by simpa using hok.1.2)⟩
    · exact checkPermBijection_spec m pCode pinvCode r hok.2 i (by omega)

theorem checkUpperEdges_checkI_spec (n pCode prevMask ext tMask j : Nat) :
    ∀ r, checkUpperEdges.checkI n pCode prevMask ext tMask j (decodePermEntry pCode j) r = true →
      ∀ i < r,
        hasExtEdge n prevMask ext i j =
          hasMaskEdge (n + 1) tMask (decodePermEntry pCode i) (decodePermEntry pCode j)
  | 0, _, _, hi => by omega
  | r + 1, hok, i, hi => by
    unfold checkUpperEdges.checkI at hok
    simp only [Bool.and_eq_true] at hok
    by_cases hir : i = r
    · subst hir; exact eq_of_beq hok.1
    · exact checkUpperEdges_checkI_spec n pCode prevMask ext tMask j r hok.2 i (by omega)

theorem checkUpperEdges_spec (n pCode prevMask ext tMask : Nat) :
    ∀ r, checkUpperEdges n pCode prevMask ext tMask r = true →
      ∀ i j, i < j → j < r →
        hasExtEdge n prevMask ext i j =
          hasMaskEdge (n + 1) tMask (decodePermEntry pCode i) (decodePermEntry pCode j)
  | 0, _, _, _, _, hj => by omega
  | r + 1, hok, i, j, hij, hj => by
    unfold checkUpperEdges at hok
    simp only [Bool.and_eq_true] at hok
    by_cases hjr : j = r
    · subst hjr
      exact checkUpperEdges_checkI_spec n pCode prevMask ext tMask j j hok.1 i hij
    · exact checkUpperEdges_spec n pCode prevMask ext tMask r hok.2 i j hij (by omega)

theorem graphIso_of_checkIsoMaskExt {n pCode pinvCode prevMask ext tMask : Nat}
    (hok : checkIsoMaskExt n pCode pinvCode prevMask ext tMask = true) :
    GraphIso (extendMaskGraph n prevMask ext) (graphOfAdjMask (n + 1) tMask) := by
  unfold checkIsoMaskExt at hok
  simp only [Bool.and_eq_true] at hok
  have hbij := checkPermBijection_spec (n + 1) pCode pinvCode (n + 1) hok.1
  have hedge := checkUpperEdges_spec n pCode prevMask ext tMask (n + 1) hok.2
  let src := extendMaskGraph n prevMask ext
  let dst := graphOfAdjMask (n + 1) tMask
  refine ⟨{
    toFun := fun u => ⟨decodePermEntry pCode u.val, (hbij u.val u.isLt).1⟩
    invFun := fun v => ⟨decodePermEntry pinvCode v.val, (hbij v.val v.isLt).2.1⟩
    left_inv := fun u => Fin.ext (hbij u.val u.isLt).2.2.1
    right_inv := fun v => Fin.ext (hbij v.val v.isLt).2.2.2
    map_adj := fun u v => by
      by_cases huv : u.val = v.val
      · have heq : u = v := Fin.ext huv
        subst heq
        rw [src.loopless, dst.loopless]
      · by_cases hlt : u.val < v.val
        · rw [← hasExtEdge_eq_adj]
          exact hedge u.val v.val hlt v.isLt
        · have hgt : v.val < u.val := by omega
          rw [src.symm u v, dst.symm, ← hasExtEdge_eq_adj]
          exact hedge v.val u.val hgt u.isLt
  }⟩

def verifyExtLoop (n prevMask : Nat) (nextBST : NatBST) :
    Nat → Nat → List (Nat × Nat × Nat) → Option (List (Nat × Nat × Nat))
  | 0, _, cs => some cs
  | rem + 1, ext, cs =>
    if isValidExtMask n prevMask ext then
      match cs with
      | [] => none
      | (tMask, pCode, pinvCode) :: rest =>
        if bstContains nextBST tMask &&
           checkIsoMaskExt n pCode pinvCode prevMask ext tMask
        then verifyExtLoop n prevMask nextBST rem (ext + 1) rest
        else none
    else verifyExtLoop n prevMask nextBST rem (ext + 1) cs

def verifyLevelCerts (n : Nat) : List Nat → NatBST → List (Nat × Nat × Nat) → Bool
  | [], _, cs => cs.isEmpty
  | pm :: pms, nextBST, cs =>
    match verifyExtLoop n pm nextBST (2 ^ n) 0 cs with
    | none => false
    | some cs' => verifyLevelCerts n pms nextBST cs'

theorem verifyExtLoop_sound (n prevMask : Nat) (nextBST : NatBST) :
    ∀ (rem start : Nat) (cs cs' : List (Nat × Nat × Nat)),
      verifyExtLoop n prevMask nextBST rem start cs = some cs' →
      ∀ ext, start ≤ ext → ext < start + rem → isValidExtMask n prevMask ext = true →
        ∃ tMask ∈ bstToList nextBST,
          GraphIso (extendMaskGraph n prevMask ext) (graphOfAdjMask (n + 1) tMask)
  | 0, _, _, _, _, _, h1, h2, _ => by omega
  | rem + 1, start, cs, cs', heq, ext, hlo, hhi, hval => by
    unfold verifyExtLoop at heq
    by_cases hst : isValidExtMask n prevMask start = true
    · simp only [hst, ↓reduceIte] at heq
      cases cs with
      | nil => cases heq
      | cons cert rest =>
        rcases cert with ⟨tMask, pCode, pinvCode⟩
        dsimp only at heq
        by_cases hchk : (bstContains nextBST tMask &&
            checkIsoMaskExt n pCode pinvCode prevMask start tMask) = true
        · simp only [hchk, ↓reduceIte] at heq
          by_cases hext : ext = start
          · subst hext
            simp only [Bool.and_eq_true] at hchk
            exact ⟨tMask, mem_bstToList_of_bstContains hchk.1, graphIso_of_checkIsoMaskExt hchk.2⟩
          · exact verifyExtLoop_sound n prevMask nextBST rem (start + 1) rest cs' heq
              ext (by omega) (by omega) hval
        · have hchkF := Bool.eq_false_iff.mpr hchk
          simp [hchkF] at heq
    · have hstF := Bool.eq_false_iff.mpr hst
      simp only [hstF, Bool.false_eq_true, ↓reduceIte] at heq
      have hne : ext ≠ start := fun e => by subst e; rw [hval] at hstF; cases hstF
      exact verifyExtLoop_sound n prevMask nextBST rem (start + 1) cs cs' heq
        ext (by omega) (by omega) hval

theorem verifyLevelCerts_sound (n : Nat) :
    ∀ (pms : List Nat) (nextBST : NatBST) (cs : List (Nat × Nat × Nat)),
      verifyLevelCerts n pms nextBST cs = true →
      ∀ prevMask ∈ pms, ∀ ext < 2 ^ n, isValidExtMask n prevMask ext = true →
        ∃ tMask ∈ bstToList nextBST,
          GraphIso (extendMaskGraph n prevMask ext) (graphOfAdjMask (n + 1) tMask)
  | [], _, _, _, _, hmem, _, _, _ => by cases hmem
  | pm :: pms, nextBST, cs, hv, prevMask, hmem, ext, hext, hval => by
    unfold verifyLevelCerts at hv
    cases hloop : verifyExtLoop n pm nextBST (2 ^ n) 0 cs with
    | none => rw [hloop] at hv; cases hv
    | some cs' =>
      rw [hloop] at hv
      rcases List.mem_cons.mp hmem with rfl | hpms
      · exact verifyExtLoop_sound n prevMask nextBST (2 ^ n) 0 cs cs' hloop
          ext (Nat.zero_le _) (by omega) hval
      · exact verifyLevelCerts_sound n pms nextBST cs' hv prevMask hpms ext hext hval

theorem step_canon_reduction {n : Nat} {prevBST nextBST : NatBST} {certs : List (Nat × Nat × Nat)}
    (hprev : ∀ G₀ : SimpleGraphN n, ∃ m₀ ∈ bstToList prevBST, GraphIso G₀ (graphOfAdjMask n m₀))
    (hcert : verifyLevelCerts n (bstToList prevBST) nextBST certs = true) :
    ∀ G : SimpleGraphN (n + 1), ∃ m₁ ∈ bstToList nextBST, GraphIso G (graphOfAdjMask (n + 1) m₁) := by
  intro G
  rcases exists_min_deg_vertex G with ⟨vmin, hvmin⟩
  let G₁ := swapGraphVertices G vmin (.last n)
  let w₁ : IsoWitness G G₁ := isoSwapVertices G vmin (.last n)
  have hmin₁ : ∀ u : Fin (n + 1), vertexDeg G₁ (.last n) ≤ vertexDeg G₁ u := by
    intro u
    have hlast : w₁.toFun vmin = .last n := by show swapFin vmin (.last n) vmin = _; unfold swapFin; simp
    have hd_last : vertexDeg G vmin = vertexDeg G₁ (.last n) := by
      rw [w₁.deg_eq vmin, hlast]
    have hd_u : vertexDeg G (w₁.invFun u) = vertexDeg G₁ u := by
      have := w₁.deg_eq (w₁.invFun u)
      rw [w₁.right_inv u] at this
      exact this
    have := hvmin (w₁.invFun u)
    omega
  rcases hprev (initGraph G₁) with ⟨m₀, hm₀, ⟨w₀⟩⟩
  let nb₁ := lastNeighbors G₁
  let nb₂ := fun j : Fin n => nb₁ (w₀.invFun j)
  let w₂ : IsoWitness (extendGraph (initGraph G₁) nb₁) (extendGraph (graphOfAdjMask n m₀) nb₂) :=
    liftIsoExtend w₀ nb₁
  have hG₁_eq : extendGraph (initGraph G₁) nb₁ = G₁ := extendGraph_init_last G₁
  let bs : List Bool := (List.range n).map (fun k => if hk : k < n then nb₂ ⟨k, hk⟩ else false)
  let ext := packBools bs
  have hext_lt : ext < 2 ^ n := by
    have := packBools_lt_pow2 bs
    simpa [bs] using this
  have hnb₂_eq : nb₂ = (fun j : Fin n => testBitNat ext j.val) := by
    funext j
    have hbit := testBitNat_packBools bs j.val (by simp [bs, j.isLt])
    dsimp only [ext]
    rw [hbit]
    simp [bs, j.isLt]
  have hG₂_eq : extendGraph (graphOfAdjMask n m₀) nb₂ = extendMaskGraph n m₀ ext := by
    unfold extendMaskGraph
    rw [hnb₂_eq]
  have hmin₂ : ∀ u : Fin (n + 1),
      vertexDeg (extendMaskGraph n m₀ ext) (.last n) ≤
      vertexDeg (extendMaskGraph n m₀ ext) u := by
    intro u
    rw [← hG₂_eq]
    let u' : Fin (n + 1) := w₂.invFun u
    have hlast_fix : w₂.toFun (.last n) = .last n := by
      apply Fin.ext; show (liftFixLast w₀.toFun (.last n)).val = n
      rw [liftFixLast_val]; have : ¬ ((Fin.last n).val < n) := by simp [Fin.last]
      simp [this]
    have hd1 : vertexDeg (extendGraph (initGraph G₁) nb₁) (.last n) =
        vertexDeg (extendGraph (graphOfAdjMask n m₀) nb₂) (.last n) := by
      have := w₂.deg_eq (.last n); rw [hlast_fix] at this; exact this
    have hd2 : vertexDeg (extendGraph (initGraph G₁) nb₁) u' =
        vertexDeg (extendGraph (graphOfAdjMask n m₀) nb₂) u := by
      have := w₂.deg_eq u'
      have hru : w₂.toFun u' = u := w₂.right_inv u
      rw [hru] at this; exact this
    rw [hG₁_eq] at hd1 hd2
    have := hmin₁ u'
    omega
  have hval := isValidExtMask_of_minDeg hmin₂
  rcases verifyLevelCerts_sound n (bstToList prevBST) nextBST certs hcert m₀ hm₀ ext hext_lt hval
    with ⟨m₁, hm₁, hiso₃⟩
  have hiso₁ : GraphIso G G₁ := ⟨w₁⟩
  have hiso₂ : GraphIso G₁ (extendMaskGraph n m₀ ext) := by
    rw [← hG₁_eq, ← hG₂_eq]; exact ⟨w₂⟩
  exact ⟨m₁, hm₁, hiso₁.trans (hiso₂.trans hiso₃)⟩

/-! ### Kernel Verification of All Canonical Certificates (`n = 1 .. 7`) -/

theorem certs_ok_2 : verifyLevelCerts 1 (bstToList canonBST1) canonBST2 canonCerts2 = true := by decide
theorem certs_ok_3 : verifyLevelCerts 2 (bstToList canonBST2) canonBST3 canonCerts3 = true := by decide
theorem certs_ok_4 : verifyLevelCerts 3 (bstToList canonBST3) canonBST4 canonCerts4 = true := by decide
theorem certs_ok_5 : verifyLevelCerts 4 (bstToList canonBST4) canonBST5 canonCerts5 = true := by decide
theorem certs_ok_6 : verifyLevelCerts 5 (bstToList canonBST5) canonBST6 canonCerts6 = true := by decide

set_option maxHeartbeats 1000000 in
theorem certs_ok_7 : verifyLevelCerts 6 (bstToList canonBST6) canonBST7 canonCerts7 = true := by decide

theorem canon_reduction_1 : ∀ G : SimpleGraphN 1, ∃ m ∈ bstToList canonBST1, GraphIso G (graphOfAdjMask 1 m) := by
  intro G
  refine ⟨0, List.mem_singleton_self 0, ?_⟩
  have hG : G = graphOfAdjMask 1 0 := by
    apply SimpleGraphN.ext; funext u v
    have : u = v := Fin.ext (by omega)
    subst this
    rw [G.loopless, (graphOfAdjMask 1 0).loopless]
  rw [hG]; exact GraphIso.refl _

theorem canon_reduction_2 : ∀ G : SimpleGraphN 2, ∃ m ∈ bstToList canonBST2, GraphIso G (graphOfAdjMask 2 m) :=
  step_canon_reduction canon_reduction_1 certs_ok_2

theorem canon_reduction_3 : ∀ G : SimpleGraphN 3, ∃ m ∈ bstToList canonBST3, GraphIso G (graphOfAdjMask 3 m) :=
  step_canon_reduction canon_reduction_2 certs_ok_3

theorem canon_reduction_4 : ∀ G : SimpleGraphN 4, ∃ m ∈ bstToList canonBST4, GraphIso G (graphOfAdjMask 4 m) :=
  step_canon_reduction canon_reduction_3 certs_ok_4

theorem canon_reduction_5 : ∀ G : SimpleGraphN 5, ∃ m ∈ bstToList canonBST5, GraphIso G (graphOfAdjMask 5 m) :=
  step_canon_reduction canon_reduction_4 certs_ok_5

theorem canon_reduction_6 : ∀ G : SimpleGraphN 6, ∃ m ∈ bstToList canonBST6, GraphIso G (graphOfAdjMask 6 m) :=
  step_canon_reduction canon_reduction_5 certs_ok_6

theorem canon_reduction_7 : ∀ G : SimpleGraphN 7, ∃ m ∈ bstToList canonBST7, GraphIso G (graphOfAdjMask 7 m) :=
  step_canon_reduction canon_reduction_6 certs_ok_7

/-! ### `O(N log N)` Verified Injectivity Checker (`VecMapBST`) -/

def listNatLt : List Nat → List Nat → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys => if x == y then listNatLt xs ys else decide (x < y)

inductive VecMapBST where
  | empty : VecMapBST
  | branch : List Nat → Nat → VecMapBST → VecMapBST → VecMapBST

def vmLookup : VecMapBST → List Nat → Option Nat
  | .empty, _ => none
  | .branch k v l r, q =>
    if q == k then some v
    else if listNatLt q k then vmLookup l q
    else vmLookup r q

def vmInsert : VecMapBST → List Nat → Nat → Option VecMapBST
  | .empty, k, v => some (.branch k v .empty .empty)
  | .branch k₀ v₀ l r, k, v =>
    if k == k₀ then
      if v == v₀ then some (.branch k₀ v₀ l r) else none
    else if listNatLt k k₀ then
      match vmInsert l k v with
      | none => none
      | some l' => some (.branch k₀ v₀ l' r)
    else
      match vmInsert r k v with
      | none => none
      | some r' => some (.branch k₀ v₀ l r')

theorem vmLookup_vmInsert :
    ∀ {t t' : VecMapBST} {k : List Nat} {v : Nat},
      vmInsert t k v = some t' →
      vmLookup t' k = some v ∧ (∀ q, q ≠ k → vmLookup t' q = vmLookup t q)
  | .empty, _, k, v, h => by
    injection h with h'; subst h'
    refine ⟨by simp [vmLookup], fun q hqk => ?_⟩
    have b : (q == k) = false := Bool.eq_false_iff.mpr (fun e => hqk (of_decide_eq_true (by simpa using e)))
    unfold vmLookup; simp only [b, Bool.false_eq_true, ↓reduceIte]
    split <;> rfl
  | .branch k₀ v₀ l r, _, k, v, h => by
    unfold vmInsert at h
    by_cases hkk₀ : k == k₀
    · have hkeq : k = k₀ := of_decide_eq_true (by simpa using hkk₀)
      subst hkeq; simp only [beq_self_eq_true, ↓reduceIte] at h
      by_cases hvv₀ : v == v₀
      · have hveq : v = v₀ := of_decide_eq_true (by simpa using hvv₀)
        subst hveq; simp only [beq_self_eq_true, ↓reduceIte] at h
        injection h with h'; subst h'
        exact ⟨by simp [vmLookup], fun _ _ => rfl⟩
      · simp [hvv₀] at h
    · simp only [hkk₀, Bool.false_eq_true, ↓reduceIte] at h
      have hkne : k ≠ k₀ := fun e => hkk₀ (by simpa using decide_eq_true e)
      by_cases hlt : listNatLt k k₀ = true
      · simp only [hlt, ↓reduceIte] at h
        cases hins : vmInsert l k v with
        | none => rw [hins] at h; cases h
        | some l' =>
          rw [hins] at h; injection h with h'; subst h'
          rcases vmLookup_vmInsert hins with ⟨hl1, hl2⟩
          refine ⟨by simp [vmLookup, hkk₀, hlt, hl1], fun q hqk => ?_⟩
          unfold vmLookup
          by_cases hqk₀ : q == k₀
          · simp [hqk₀]
          · simp only [hqk₀, Bool.false_eq_true, ↓reduceIte]
            split
            · exact hl2 q hqk
            · rfl
      · have hltF := Bool.eq_false_iff.mpr hlt
        simp only [hltF, Bool.false_eq_true, ↓reduceIte] at h
        cases hins : vmInsert r k v with
        | none => rw [hins] at h; cases h
        | some r' =>
          rw [hins] at h; injection h with h'; subst h'
          rcases vmLookup_vmInsert hins with ⟨hr1, hr2⟩
          refine ⟨by simp [vmLookup, hkk₀, hltF, hr1], fun q hqk => ?_⟩
          unfold vmLookup
          by_cases hqk₀ : q == k₀
          · simp [hqk₀]
          · simp only [hqk₀, Bool.false_eq_true, ↓reduceIte]
            split
            · rfl
            · exact hr2 q hqk

theorem vmInsert_preserves_existing :
    ∀ {T T' : VecMapBST} {k : List Nat} {v w : Nat},
      vmInsert T k v = some T' → vmLookup T k = some w → v = w
  | .empty, _, _, _, _, _, hlk0 => by cases hlk0
  | .branch k₀ v₀ l r, _, k, v, w, hi, hl0 => by
    unfold vmInsert at hi; unfold vmLookup at hl0
    by_cases hkk₀ : k == k₀
    · simp only [hkk₀, ↓reduceIte] at hi hl0
      injection hl0 with hw
      rw [hw] at hi
      by_cases hvv : v == w
      · exact of_decide_eq_true (by simpa using hvv)
      · simp [hvv] at hi
    · simp only [hkk₀, Bool.false_eq_true, ↓reduceIte] at hi hl0
      split at hi
      · next hlt =>
        cases h1 : vmInsert l k v with
        | none => rw [h1] at hi; cases hi
        | some _ => simp only [hlt, ↓reduceIte] at hl0; exact vmInsert_preserves_existing h1 hl0
      · next hlt =>
        cases h1 : vmInsert r k v with
        | none => rw [h1] at hi; cases hi
        | some _ => simp only [hlt, ↓reduceIte] at hl0; exact vmInsert_preserves_existing h1 hl0

def vmInsertAll (fn : Nat → List Nat) : List Nat → VecMapBST → Option VecMapBST
  | [], t => some t
  | m :: ms, t =>
    match vmInsert t (fn m) m with
    | none => none
    | some t' => vmInsertAll fn ms t'

def checkInjOnMasks (masks : List Nat) (fn : Nat → List Nat) : Bool :=
  (vmInsertAll fn masks .empty).isSome

theorem vmInsertAll_lookup (fn : Nat → List Nat) :
    ∀ (ms : List Nat) (t tFinal : VecMapBST),
      vmInsertAll fn ms t = some tFinal →
      ∀ m, (m ∈ ms ∨ vmLookup t (fn m) = some m) → vmLookup tFinal (fn m) = some m
  | [], t, _, h, _, hm => by
    injection h with h'; subst h'
    rcases hm with hmem | hlk
    · cases hmem
    · exact hlk
  | x :: xs, t, tFinal, h, m, hm => by
    unfold vmInsertAll at h
    cases hins : vmInsert t (fn x) x with
    | none => rw [hins] at h; cases h
    | some t' =>
      rw [hins] at h
      rcases vmLookup_vmInsert hins with ⟨hx1, hx2⟩
      refine vmInsertAll_lookup fn xs t' tFinal h m ?_
      rcases hm with hmem | hlk
      · rcases List.mem_cons.mp hmem with rfl | hxs
        · exact Or.inr hx1
        · exact Or.inl hxs
      · by_cases hfx : fn m = fn x
        · right
          rw [hfx] at hlk ⊢
          have hxm := vmInsert_preserves_existing hins hlk
          subst hxm; exact hx1
        · right; rw [hx2 (fn m) hfx]; exact hlk

theorem checkInjOnMasks_sound {masks : List Nat} {fn : Nat → List Nat}
    (hok : checkInjOnMasks masks fn = true) :
    ∀ m₁ ∈ masks, ∀ m₂ ∈ masks, fn m₁ = fn m₂ → m₁ = m₂ := by
  unfold checkInjOnMasks at hok
  cases hall : vmInsertAll fn masks .empty with
  | none => rw [hall] at hok; cases hok
  | some tFinal =>
    intro m₁ hm₁ m₂ hm₂ hfeq
    have h1 := vmInsertAll_lookup fn masks .empty tFinal hall m₁ (Or.inl hm₁)
    have h2 := vmInsertAll_lookup fn masks .empty tFinal hall m₂ (Or.inl hm₂)
    rw [hfeq, h2] at h1
    injection h1 with h12
    exact h12.symm

/-- Construct a `SimpleGraphN n` from an explicit undirected edge list `edges : List (Nat × Nat)`. -/
def mkGraphFromEdges (n : Nat) (edges : List (Nat × Nat)) : SimpleGraphN n where
  adj u v :=
    !(u == v) && edges.any (fun p =>
      ((u.val == p.1) && (v.val == p.2)) || ((u.val == p.2) && (v.val == p.1)))
  loopless u := by simp
  symm u v := by
    by_cases huv : u = v
    · subst huv; simp
    · have hvu : v ≠ u := fun e => huv e.symm
      have b1 : (u == v) = false := Bool.eq_false_iff.mpr (fun e => huv (of_decide_eq_true (by simpa using e)))
      have b2 : (v == u) = false := Bool.eq_false_iff.mpr (fun e => hvu (of_decide_eq_true (by simpa using e)))
      simp only [b1, b2, Bool.not_false, Bool.true_and]
      have hcongr : ∀ L : List (Nat × Nat),
          L.any (fun p => ((u.val == p.1) && (v.val == p.2)) || ((u.val == p.2) && (v.val == p.1))) =
          L.any (fun p => ((v.val == p.1) && (u.val == p.2)) || ((v.val == p.2) && (u.val == p.1))) := by
        intro L
        induction L with
        | nil => rfl
        | cons p ps ih =>
          simp only [List.any_cons, ih]
          congr 1
          rw [Bool.and_comm (u.val == p.1), Bool.and_comm (u.val == p.2), Bool.or_comm]
      exact hcongr edges

end Conjecture00000003970
