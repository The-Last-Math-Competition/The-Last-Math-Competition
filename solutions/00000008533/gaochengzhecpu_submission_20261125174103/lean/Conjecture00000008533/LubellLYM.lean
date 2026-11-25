/-
Copyright (c) 2026. All rights reserved.
Core Lean 4.19.0 formalization for Conjecture 00000008533:
1. Positive LYM-type theorem on ALL finite geometric lattices (Lubell maximal-chain weighting
   and general nonnegative chain-convex weightings), with unimprovable constant 1.
2. General refutation of constant-tightness for global and proper-global |μ|-normalizations
   on every geometric lattice of rank ≥ 1 (resp. rank ≥ 3).
-/
import Conjecture00000008533.Basic

namespace Conjecture00000008533

theorem sumNat_le_sumNat {α : Type} {xs : List α} {f g : α → Nat}
    (h : ∀ x ∈ xs, f x ≤ g x) : sumNat xs f ≤ sumNat xs g := by
  induction xs with
  | nil => exact Nat.le_refl 0
  | cons a as ih =>
    simp only [sumNat]
    have h1 := h a List.mem_cons_self
    have h2 := ih (fun x hx => h x (List.mem_cons_of_mem a hx))
    omega

theorem sumInt_const_neg_one {α : Type} (xs : List α) :
    sumInt xs (fun _ => (-1 : Int)) = - (xs.length : Int) := by
  induction xs with
  | nil => rfl
  | cons _ _ ih => simp [sumInt, ih]; omega

namespace GeometricLattice

/-! ## 1. Maximal Chains and Lubell's Tight LYM Inequality on All Geometric Lattices -/

/-- Elements covering `x` in `L` (characterized by `x ≤ y ∧ rk y = rk x + 1`). -/
def upperCovers {α : Type} [DecidableEq α] (L : GeometricLattice α) (x : α) : List α :=
  L.elems.filter (fun y => L.leb x y && decide (L.rk y = L.rk x + 1))

/-- Saturated chains of `d` steps starting at `x`. -/
def chainsFrom {α : Type} [DecidableEq α] (L : GeometricLattice α) : Nat → α → List (List α)
  | 0, x => [[x]]
  | d + 1, x =>
    (L.upperCovers x).foldr
      (fun y acc => (L.chainsFrom d y).map (fun C => x :: C) ++ acc) []

/-- All maximal chains from `⊥` to `⊤` in `L`. -/
def maxChains {α : Type} [DecidableEq α] (L : GeometricLattice α) : List (List α) :=
  L.chainsFrom (L.rk L.top) L.bot

theorem mem_foldr_map_append {β γ : Type} (ys : List β) (g : β → List γ) (z : γ) :
    z ∈ ys.foldr (fun y acc => g y ++ acc) [] ↔ ∃ y ∈ ys, z ∈ g y := by
  induction ys with
  | nil => simp [List.foldr]
  | cons a as ih =>
    simp only [List.foldr, List.mem_append, List.mem_cons]
    constructor
    · rintro (hza | hzas)
      · exact ⟨a, Or.inl rfl, hza⟩
      · rcases ih.mp hzas with ⟨y, hy, hzy⟩
        exact ⟨y, Or.inr hy, hzy⟩
    · rintro ⟨y, rfl | hy, hzy⟩
      · exact Or.inl hzy
      · exact Or.inr (ih.mpr ⟨y, hy, hzy⟩)

theorem nodup_append_of_disjoint {β : Type} {xs ys : List β}
    (hx : NoDup xs) (hy : NoDup ys) (hdisj : ∀ z, z ∈ xs → z ∈ ys → False) :
    NoDup (xs ++ ys) := by
  induction hx with
  | nil => exact hy
  | @cons a as hnin _ ih =>
    simp only [List.cons_append]
    refine NoDup.cons ?_ (ih (fun z hza hzy => hdisj z (List.mem_cons_of_mem a hza) hzy))
    intro hm
    rcases List.mem_append.mp hm with hma | hmy
    · exact hnin hma
    · exact hdisj a List.mem_cons_self hmy

theorem nodup_map_cons {β : Type} (x : β) {Cs : List (List β)} (hnd : NoDup Cs) :
    NoDup (Cs.map (fun C => x :: C)) := by
  induction hnd with
  | nil => exact NoDup.nil
  | @cons c cs hnin _ ih =>
    simp only [List.map]
    refine NoDup.cons ?_ ih
    intro hm
    rcases List.mem_map.mp hm with ⟨c', hc', heq⟩
    cases heq
    exact hnin hc'

/-- Structural invariants of `chainsFrom d x`. -/
theorem chainsFrom_props {α : Type} [DecidableEq α] (L : GeometricLattice α) :
    ∀ (d : Nat) (x : α) (C : List α),
      C ∈ L.chainsFrom d x →
      (∃ tail, C = x :: tail) ∧
      NoDup C ∧
      (∀ u ∈ C, L.le x u ∧ L.rk x ≤ L.rk u) ∧
      (∀ u ∈ C, ∀ v ∈ C, L.le u v ∨ L.le v u) ∧
      (∀ k, L.rk x ≤ k → k ≤ L.rk x + d → ∃ z ∈ C, L.rk z = k)
  | 0, x, C, hC => by
    simp only [chainsFrom, List.mem_singleton] at hC
    subst hC
    refine ⟨⟨[], rfl⟩, NoDup.cons (by simp) NoDup.nil, ?_, ?_, ?_⟩
    · intro u hu; simp at hu; rw [hu]; exact ⟨L.le_refl x, Nat.le_refl _⟩
    · intro u hu v hv; simp at hu hv; rw [hu, hv]; exact Or.inl (L.le_refl x)
    · intro k hk1 hk2; have hk : k = L.rk x := by omega
      exact ⟨x, List.mem_singleton.mpr rfl, hk.symm⟩
  | d + 1, x, C, hC => by
    unfold chainsFrom at hC
    rw [mem_foldr_map_append] at hC
    rcases hC with ⟨y, hy, hCy⟩
    rcases List.mem_map.mp hCy with ⟨C', hC', rfl⟩
    unfold upperCovers at hy
    rcases (Bool.and_eq_true _ _).mp ((mem_filter_iff_prop _ _ _).mp hy).2 with ⟨hxy, hry_b⟩
    have hry : L.rk y = L.rk x + 1 := of_decide_eq_true hry_b
    rcases L.chainsFrom_props d y C' hC' with ⟨_, hnd', hlow', hcmp', hrks'⟩
    refine ⟨⟨C', rfl⟩, ?_, ?_, ?_, ?_⟩
    · refine NoDup.cons ?_ hnd'
      intro hxC'
      have hlt := (hlow' x hxC').2
      omega
    · intro u hu
      rcases List.mem_cons.mp hu with hu_eq | hu'
      · rw [hu_eq]; exact ⟨L.le_refl x, Nat.le_refl _⟩
      · rcases hlow' u hu' with ⟨hyu, hryu⟩
        exact ⟨L.le_trans hxy hyu, by omega⟩
    · intro u hu v hv
      rcases List.mem_cons.mp hu with hu_eq | hu'
      · rw [hu_eq]
        rcases List.mem_cons.mp hv with hv_eq | hv'
        · rw [hv_eq]; exact Or.inl (L.le_refl x)
        · exact Or.inl (L.le_trans hxy (hlow' v hv').1)
      · rcases List.mem_cons.mp hv with hv_eq | hv'
        · rw [hv_eq]; exact Or.inr (L.le_trans hxy (hlow' u hu').1)
        · exact hcmp' u hu' v hv'
    · intro k hk1 hk2
      by_cases hkx : k = L.rk x
      · exact ⟨x, List.mem_cons_self, hkx.symm⟩
      · rcases hrks' k (by omega) (by omega) with ⟨z, hz, hrz⟩
        exact ⟨z, List.mem_cons_of_mem x hz, hrz⟩

theorem nodup_foldr_chains {α : Type} [DecidableEq α] (L : GeometricLattice α)
    (d : Nat) (x : α) {ys : List α} (hnd : NoDup ys) :
    NoDup (ys.foldr (fun y acc => (L.chainsFrom d y).map (fun C => x :: C) ++ acc) []) := by
  induction hnd with
  | nil => exact NoDup.nil
  | @cons y ys' hnin _ ih =>
    simp only [List.foldr]
    apply nodup_append_of_disjoint
    · exact nodup_map_cons x (nodup_foldr_chains_aux L d y)
    · exact ih
    · intro C h1 h2
      rcases List.mem_map.mp h1 with ⟨C₁, hC₁, rfl⟩
      rw [mem_foldr_map_append] at h2
      rcases h2 with ⟨y₂, hy₂, hCy₂⟩
      rcases List.mem_map.mp hCy₂ with ⟨C₂, hC₂, heq⟩
      cases heq
      rcases (L.chainsFrom_props d y C₁ hC₁).1 with ⟨_, hhead1⟩
      rcases (L.chainsFrom_props d y₂ C₁ hC₂).1 with ⟨_, hhead2⟩
      rw [hhead1] at hhead2
      cases hhead2
      exact hnin hy₂
where
  nodup_foldr_chains_aux {α : Type} [DecidableEq α] (L : GeometricLattice α) :
      (d : Nat) → (x : α) → NoDup (L.chainsFrom d x)
    | 0, _ => NoDup.cons (by simp) NoDup.nil
    | d + 1, x => nodup_foldr_chains L d x (nodup_filter _ L.nodup_elems)

theorem chainsFrom_nodup {α : Type} [DecidableEq α] (L : GeometricLattice α)
    (d : Nat) (x : α) : NoDup (L.chainsFrom d x) :=
  nodup_foldr_chains.nodup_foldr_chains_aux L d x

/-- Nonemptiness of `chainsFrom d x` whenever `x ≤ ⊤` and `rk x + d = rk ⊤`. -/
theorem chainsFrom_nonempty {α : Type} [DecidableEq α] (L : GeometricLattice α) :
    ∀ (d : Nat) (x : α), L.le x L.top → L.rk x + d = L.rk L.top →
      0 < (L.chainsFrom d x).length
  | 0, _, _, _ => by simp [chainsFrom]
  | d + 1, x, hxt, hrk => by
    have hex_y : ∃ y, y ∈ L.upperCovers x ∧ L.le y L.top := by
      by_cases hd0 : d = 0
      · refine ⟨L.top, ?_, L.le_refl L.top⟩
        unfold upperCovers; rw [mem_filter_iff_prop]
        exact ⟨L.mem_elems L.top, Bool.and_eq_true _ _ |>.mpr ⟨hxt, decide_eq_true (by omega)⟩⟩
      · rcases L.exists_step hxt (by omega) with ⟨z, hxz, _, hzt, hrz⟩
        refine ⟨z, ?_, hzt⟩
        unfold upperCovers; rw [mem_filter_iff_prop]
        exact ⟨L.mem_elems z, Bool.and_eq_true _ _ |>.mpr ⟨hxz, decide_eq_true hrz⟩⟩
    rcases hex_y with ⟨y, hy_mem, hyt⟩
    have hyp := (Bool.and_eq_true _ _).mp ((mem_filter_iff_prop _ _ _).mp hy_mem).2
    have hry : L.rk y = L.rk x + 1 := of_decide_eq_true hyp.2
    have hih := L.chainsFrom_nonempty d y hyt (by omega)
    cases hCy : L.chainsFrom d y with
    | nil => rw [hCy] at hih; simp at hih
    | cons C₀ Cs =>
      have hmem : (x :: C₀) ∈ L.chainsFrom (d + 1) x := by
        unfold chainsFrom
        rw [mem_foldr_map_append]
        refine ⟨y, hy_mem, List.mem_map.mpr ⟨C₀, ?_, rfl⟩⟩
        rw [hCy]; exact List.mem_cons_self
      cases hAll : L.chainsFrom (d + 1) x with
      | nil => rw [hAll] at hmem; cases hmem
      | cons _ _ => simp

/-- Every finite geometric lattice possesses at least one maximal chain (`|C(L)| ≥ 1`). -/
theorem maxChains_pos {α : Type} [DecidableEq α] (L : GeometricLattice α) :
    0 < L.maxChains.length :=
  L.chainsFrom_nonempty (L.rk L.top) L.bot (L.bot_le L.top) (by rw [L.rk_bot, Nat.zero_add])

/-- Number of maximal chains passing through `x`. -/
def chainsThrough {α : Type} [DecidableEq α] (L : GeometricLattice α) (x : α) : Nat :=
  (L.maxChains.filter (fun C => decide (x ∈ C))).length

/-- Lubell's canonical chain-probability weight `w_chain(x) = c(x) / |C(L)|`. -/
def lubellWeight {α : Type} [DecidableEq α] (L : GeometricLattice α) (x : α) : QRat :=
  QRat.mkNat (L.chainsThrough x) L.maxChains.length L.maxChains_pos

/-- Core double-counting bound: an antichain `A` meets any chain `C` in at most one element. -/
theorem chain_hit_antichain_le {α : Type} [DecidableEq α] (L : GeometricLattice α)
    {A : List α} (hA : L.IsAntichain A)
    {C : List α} (hcmp : ∀ u ∈ C, ∀ v ∈ C, L.le u v ∨ L.le v u) (wC : Nat) :
    sumNat A (fun x => if x ∈ C then wC else 0) ≤ wC := by
  rcases hA with ⟨hndA, hincomp⟩
  by_cases hex : ∃ a ∈ A, a ∈ C
  · rcases hex with ⟨a, haA, haC⟩
    have hcongr : sumNat A (fun x => if x ∈ C then wC else 0) =
        sumNat A (fun x => if x = a then wC else 0) := by
      apply sumNat_congr
      intro x hxA
      by_cases hxa : x = a
      · subst hxa; simp [haC]
      · simp only [hxa, ↓reduceIte]
        by_cases hxC : x ∈ C
        · rcases hcmp x hxC a haC with hle | hge
          · exact absurd (hincomp x hxA a haA hle) hxa
          · exact absurd (hincomp a haA x hxA hge).symm hxa
        · simp [hxC]
    rw [hcongr, sumNat_single_hit hndA haA]
    exact Nat.le_refl wC
  · have hz : sumNat A (fun x => if x ∈ C then wC else 0) = 0 := by
      apply sumNat_eq_zero
      intro x hxA
      have hxC : x ∉ C := fun h => hex ⟨x, hxA, h⟩
      simp [hxC]
    omega

/-- Every maximal chain meets `rankLevel k` (`k ≤ rk ⊤`) in a unique element. -/
theorem chain_hit_rankLevel_eq {α : Type} [DecidableEq α] (L : GeometricLattice α)
    {k : Nat} (hk : k ≤ L.rk L.top)
    {C : List α} (hC : C ∈ L.maxChains) (wC : Nat) :
    sumNat (L.rankLevel k) (fun x => if x ∈ C then wC else 0) = wC := by
  unfold maxChains at hC
  rcases L.chainsFrom_props (L.rk L.top) L.bot C hC with ⟨_, _, _, hcmp, hrks⟩
  rcases hrks k (by rw [L.rk_bot]; exact Nat.zero_le k) (by rw [L.rk_bot, Nat.zero_add]; exact hk)
    with ⟨a, haC, hra⟩
  have ha_rk : a ∈ L.rankLevel k := by
    unfold rankLevel; rw [mem_filter_iff_prop]
    exact ⟨L.mem_elems a, decide_eq_true hra⟩
  rcases L.rankLevel_isAntichain k with ⟨hndR, hincompR⟩
  have hcongr : sumNat (L.rankLevel k) (fun x => if x ∈ C then wC else 0) =
      sumNat (L.rankLevel k) (fun x => if x = a then wC else 0) := by
    apply sumNat_congr
    intro x hxR
    by_cases hxa : x = a
    · subst hxa; simp [haC]
    · simp only [hxa, ↓reduceIte]
      by_cases hxC : x ∈ C
      · rcases hcmp x hxC a haC with hle | hge
        · exact absurd (hincompR x hxR a ha_rk hle) hxa
        · exact absurd (hincompR a ha_rk x hxR hge).symm hxa
      · simp [hxC]
  rw [hcongr, sumNat_single_hit hndR ha_rk]

/--
**Theorem (Weighted Chain-Convex LYM Inequality on All Geometric Lattices):**
For any nonnegative weight function `ω : List α → Nat` on maximal chains and any antichain `A`,
`∑_{x ∈ A} (∑_{C ∋ x} ω(C)) ≤ ∑_{C ∈ maxChains} ω(C)`.
-/
theorem weighted_chain_lym_nat {α : Type} [DecidableEq α] (L : GeometricLattice α)
    (ω : List α → Nat) {A : List α} (hA : L.IsAntichain A) :
    sumNat A (fun x => sumNat L.maxChains (fun C => if x ∈ C then ω C else 0)) ≤
      sumNat L.maxChains ω := by
  rw [sumNat_double_swap]
  apply sumNat_le_sumNat
  intro C hC
  unfold maxChains at hC
  rcases L.chainsFrom_props (L.rk L.top) L.bot C hC with ⟨_, _, _, hcmp, _⟩
  exact L.chain_hit_antichain_le hA hcmp (ω C)

theorem chainsThrough_eq_sumNat {α : Type} [DecidableEq α] (L : GeometricLattice α) (x : α) :
    L.chainsThrough x = sumNat L.maxChains (fun C => if x ∈ C then 1 else 0) := by
  unfold chainsThrough
  rw [length_eq_sumNat_ones]
  generalize L.maxChains = cs
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.filter, sumNat]
    by_cases h : x ∈ c <;> simp [h, sumNat, ih]

/--
**Theorem 1 (Lubell Chain-Probability LYM Inequality & Tightness on All Geometric Lattices):**
1. For every antichain `A` in `L`, `∑_{x ∈ A} w_chain(x) ≤ 1` (`∑_{x ∈ A} c(x) ≤ |C(L)|`).
2. For every rank `0 ≤ k ≤ rk ⊤`, `L_k` is an antichain achieving `∑_{x ∈ L_k} w_chain(x) = 1`,
   so the constant `1` cannot be improved further.
-/
theorem lubell_lym_nat {α : Type} [DecidableEq α] (L : GeometricLattice α)
    {A : List α} (hA : L.IsAntichain A) :
    sumNat A L.chainsThrough ≤ L.maxChains.length := by
  have hcongr : sumNat A L.chainsThrough =
      sumNat A (fun x => sumNat L.maxChains (fun C => if x ∈ C then 1 else 0)) := by
    apply sumNat_congr; intro x _; exact L.chainsThrough_eq_sumNat x
  rw [hcongr, length_eq_sumNat_ones]
  exact L.weighted_chain_lym_nat (fun _ => 1) hA

theorem lubell_lym_qrat {α : Type} [DecidableEq α] (L : GeometricLattice α)
    {A : List α} (hA : L.IsAntichain A) :
    QRat.le (QRat.sumList A L.lubellWeight) QRat.one := by
  unfold lubellWeight
  apply QRat.le_of_eqv_left (QRat.sumList_const_den A L.chainsThrough L.maxChains.length L.maxChains_pos)
  have h := L.lubell_lym_nat hA
  dsimp only [QRat.le, QRat.mkNat, QRat.one]
  omega

theorem lubell_rankLevel_tight {α : Type} [DecidableEq α] (L : GeometricLattice α)
    {k : Nat} (hk : k ≤ L.rk L.top) :
    sumNat (L.rankLevel k) L.chainsThrough = L.maxChains.length ∧
    QRat.eqv (QRat.sumList (L.rankLevel k) L.lubellWeight) QRat.one := by
  have hnat : sumNat (L.rankLevel k) L.chainsThrough = L.maxChains.length := by
    have hcongr : sumNat (L.rankLevel k) L.chainsThrough =
        sumNat (L.rankLevel k) (fun x => sumNat L.maxChains (fun C => if x ∈ C then 1 else 0)) := by
      apply sumNat_congr; intro x _; exact L.chainsThrough_eq_sumNat x
    rw [hcongr, sumNat_double_swap, length_eq_sumNat_ones]
    exact sumNat_congr (fun C hC => L.chain_hit_rankLevel_eq hk hC 1)
  refine ⟨hnat, ?_⟩
  unfold lubellWeight
  have heqv := QRat.sumList_const_den (L.rankLevel k) L.chainsThrough L.maxChains.length L.maxChains_pos
  unfold QRat.eqv QRat.mkNat at heqv
  unfold QRat.eqv QRat.one
  rw [hnat] at heqv
  have hpos : (0 : Int) < (L.maxChains.length : Int) := Int.ofNat_lt.mpr L.maxChains_pos
  have heq_sd : (QRat.sumList (L.rankLevel k) (fun x =>
      QRat.mkNat (L.chainsThrough x) L.maxChains.length L.maxChains_pos)).num * 1 =
      1 * ((QRat.sumList (L.rankLevel k) (fun x =>
        QRat.mkNat (L.chainsThrough x) L.maxChains.length L.maxChains_pos)).den : Int) := by
    have hcancel := Int.eq_of_mul_eq_mul_right (by omega : (L.maxChains.length : Int) ≠ 0)
      (by
        let Q := QRat.sumList (L.rankLevel k) (fun x =>
          QRat.mkNat (L.chainsThrough x) L.maxChains.length L.maxChains_pos)
        have : Q.num * (L.maxChains.length : Int) = (Q.den : Int) * (L.maxChains.length : Int) := by
          rw [Int.mul_comm (Q.den : Int) (L.maxChains.length : Int)]
          exact heqv
        exact this)
    omega
  exact heq_sd

/-! ## 2. Global and Proper-Global |μ| Normalizations: Constant `1` IS Always Improvable -/

/-- For any rank-1 atom `a`, `|μ(⊥, a)| = 1`. -/
theorem absMobius_bot_atom {α : Type} [DecidableEq α] (L : GeometricLattice α)
    {a : α} (hra : L.rk a = 1) :
    L.absMobius L.bot a = 1 := by
  have hne : L.bot ≠ a := by
    intro h; have hr0 := L.rk_bot; rw [h] at hr0; omega
  have hmu : L.mobius L.bot a = -1 := by
    rw [L.mobius_of_lt (L.bot_le a) hne]
    have hcongr : sumInt (L.intervalLt L.bot a) (fun z => L.mobius L.bot z) =
        sumInt L.elems (fun z => if z = L.bot then L.mobius L.bot z else 0) := by
      unfold intervalLt; rw [sumInt_filter_eq_sumInt_ite]
      apply sumInt_congr; intro z _
      by_cases hzb : z = L.bot
      · subst hzb
        have hc : (L.leb L.bot L.bot && L.leb L.bot a && !decide (L.bot = a)) = true := by
          simp [L.le_refl L.bot, L.bot_le a, hne]
        simp [hc]
      · have hnc : (L.leb L.bot z && L.leb z a && !decide (z = a)) = false := by
          apply Bool.eq_false_iff.mpr
          intro ht
          rcases (Bool.and_eq_true _ _).mp ht with ⟨h12, hza_b⟩
          rcases (Bool.and_eq_true _ _).mp h12 with ⟨hbz, hza⟩
          have hza_ne : z ≠ a := by intro h; subst h; simp at hza_b
          have h1 := L.lt_rk hbz (Ne.symm hzb)
          have h2 := L.lt_rk hza hza_ne
          have hr0 := L.rk_bot
          omega
        simp [hzb, hnc]
    rw [hcongr, sumInt_single_hit L.nodup_elems (L.mem_elems L.bot)]
    simp [L.mobius_self]
  unfold absMobius
  rw [hmu]
  rfl

/-- Every rank-2 element `b` covers at least two distinct rank-1 atoms, so `|μ(⊥, b)| ≥ 1`. -/
theorem absMobius_bot_rank2_pos {α : Type} [DecidableEq α] (L : GeometricLattice α)
    {b : α} (hrb : L.rk b = 2) :
    1 ≤ L.absMobius L.bot b := by
  have hr0 := L.rk_bot
  have hne_bot : L.bot ≠ b := by intro h; rw [h] at hr0; omega
  rcases L.exists_step (L.bot_le b) (by omega) with ⟨a₁, _, _, ha₁b, hra₁_raw⟩
  have hra₁ : L.rk a₁ = 1 := by omega
  have hex_a₂ : ∃ a₂, L.rk a₂ = 1 ∧ L.leb a₂ b = true ∧ a₂ ≠ a₁ := by
    exact Classical.byContradiction fun hall => by
      have hba₁ : L.leb b a₁ = true := by
        apply L.atomistic
        intro a hra hab
        by_cases ha_eq : a = a₁
        · rw [ha_eq]; exact L.le_refl a₁
        · exact False.elim (hall ⟨a, hra, hab, ha_eq⟩)
      have hbeq : a₁ = b := L.le_antisymm ha₁b hba₁
      rw [hbeq] at hra₁
      omega
  rcases hex_a₂ with ⟨a₂, hra₂, ha₂b, ha₂_ne⟩
  have hmu_atom : ∀ z, L.rk z = 1 → L.mobius L.bot z = -1 := by
    intro z hrz
    have hz_ne : L.bot ≠ z := by intro h; rw [h] at hr0; omega
    rw [L.mobius_of_lt (L.bot_le z) hz_ne]
    have hcongr : sumInt (L.intervalLt L.bot z) (fun w => L.mobius L.bot w) =
        sumInt L.elems (fun w => if w = L.bot then L.mobius L.bot w else 0) := by
      unfold intervalLt; rw [sumInt_filter_eq_sumInt_ite]
      apply sumInt_congr; intro w _
      by_cases hwb : w = L.bot
      · subst hwb
        have hc : (L.leb L.bot L.bot && L.leb L.bot z && !decide (L.bot = z)) = true := by
          simp [L.le_refl L.bot, L.bot_le z, hz_ne]
        simp [hc]
      · have hnc : (L.leb L.bot w && L.leb w z && !decide (w = z)) = false := by
          apply Bool.eq_false_iff.mpr
          intro ht
          rcases (Bool.and_eq_true _ _).mp ht with ⟨h12, hwz_b⟩
          rcases (Bool.and_eq_true _ _).mp h12 with ⟨hbw, hwz⟩
          have hwz_ne : w ≠ z := by intro h; subst h; simp at hwz_b
          have h1 := L.lt_rk hbw (Ne.symm hwb)
          have h2 := L.lt_rk hwz hwz_ne
          omega
        simp [hwb, hnc]
    rw [hcongr, sumInt_single_hit L.nodup_elems (L.mem_elems L.bot)]
    simp [L.mobius_self]
  have hsplit := sumInt_filter_split (L.intervalLt L.bot b) (fun z => decide (z = L.bot))
    (fun z => L.mobius L.bot z)
  have hbot_mem : L.bot ∈ L.intervalLt L.bot b := by
    unfold intervalLt; rw [mem_filter_iff_prop]
    exact ⟨L.mem_elems L.bot, by simp [L.le_refl L.bot, L.bot_le b, hne_bot]⟩
  have hhit : sumInt ((L.intervalLt L.bot b).filter (fun z => decide (z = L.bot)))
      (fun z => L.mobius L.bot z) = 1 := by
    rw [sumInt_filter_eq_sumInt_ite]
    have hc : sumInt (L.intervalLt L.bot b)
        (fun z => if decide (z = L.bot) = true then L.mobius L.bot z else 0) =
        sumInt (L.intervalLt L.bot b) (fun z => if z = L.bot then L.mobius L.bot z else 0) := by
      apply sumInt_congr; intro z _; by_cases h : z = L.bot <;> simp [h]
    rw [hc]
    exact (sumInt_single_hit (nodup_filter _ L.nodup_elems) hbot_mem
      (fun z => L.mobius L.bot z)).trans (L.mobius_self L.bot)
  let atoms_b := (L.intervalLt L.bot b).filter (fun z => !decide (z = L.bot))
  have hatoms_val : sumInt atoms_b (fun z => L.mobius L.bot z) = - (atoms_b.length : Int) := by
    have hall1 : ∀ z ∈ atoms_b, L.mobius L.bot z = -1 := by
      intro z hz
      have hp1 := (mem_filter_iff_prop _ _ _).mp hz
      unfold intervalLt at hp1
      have hp2 := ((mem_filter_iff_prop _ _ _).mp hp1.1).2
      rcases (Bool.and_eq_true _ _).mp hp2 with ⟨h12, hzb_b⟩
      rcases (Bool.and_eq_true _ _).mp h12 with ⟨hbz, hzb⟩
      have hzne : L.bot ≠ z := by intro h; subst h; simp at hp1
      have hzb_ne : z ≠ b := by intro h; subst h; simp at hzb_b
      have hr1 := L.lt_rk hbz hzne
      have hr2 := L.lt_rk hzb hzb_ne
      exact hmu_atom z (by omega)
    rw [sumInt_congr hall1, sumInt_const_neg_one]
  have ha₁_mem : a₁ ∈ atoms_b := by
    rw [mem_filter_iff_prop]
    refine ⟨?_, ?_⟩
    · unfold intervalLt; rw [mem_filter_iff_prop]
      have ha₁_neb : a₁ ≠ b := by intro h; rw [h] at hra₁; omega
      exact ⟨L.mem_elems a₁, by simp [L.bot_le a₁, ha₁b, ha₁_neb]⟩
    · have hne : a₁ ≠ L.bot := by intro h; rw [h] at hra₁; omega
      simp [hne]
  have ha₂_mem : a₂ ∈ atoms_b := by
    rw [mem_filter_iff_prop]
    refine ⟨?_, ?_⟩
    · unfold intervalLt; rw [mem_filter_iff_prop]
      have ha₂_neb : a₂ ≠ b := by intro h; rw [h] at hra₂; omega
      exact ⟨L.mem_elems a₂, by simp [L.bot_le a₂, ha₂b, ha₂_neb]⟩
    · have hne : a₂ ≠ L.bot := by intro h; rw [h] at hra₂; omega
      simp [hne]
  have hlen2 : 2 ≤ atoms_b.length := by
    rw [length_eq_sumNat_ones]
    have hnd_pair : NoDup [a₁, a₂] :=
      NoDup.cons (by simp [Ne.symm ha₂_ne]) (NoDup.cons (by simp) NoDup.nil)
    have hsub : ∀ x ∈ [a₁, a₂], x ∈ atoms_b := by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact ha₁_mem
      · simp at hx'; subst hx'; exact ha₂_mem
    have hle := sumNat_subset_le hnd_pair hsub (fun _ => 1)
    simp [sumNat] at hle
    exact hle
  have hmu_b : L.mobius L.bot b = (atoms_b.length : Int) - 1 := by
    rw [L.mobius_of_lt (L.bot_le b) hne_bot]
    change - sumInt (L.intervalLt L.bot b) (fun z => L.mobius L.bot z) = _
    rw [← hsplit, hhit]
    change - (1 + sumInt atoms_b (fun z => L.mobius L.bot z)) = _
    rw [hatoms_val]
    omega
  unfold absMobius
  rw [hmu_b]
  omega

/-- General strict bound when two comparable elements `u < v` inside a domain `D` both have positive weight. -/
theorem antichain_sum_lt_of_comparable_pos {α : Type} [DecidableEq α] (L : GeometricLattice α)
    {D : List α} (_hndD : NoDup D)
    {u v : α} (huD : u ∈ D) (hvD : v ∈ D) (huv : L.le u v) (hne : u ≠ v)
    (ν : α → Nat) (hu_pos : 1 ≤ ν u) (hv_pos : 1 ≤ ν v)
    {A : List α} (hA : L.IsAntichain A) (hAD : ∀ x ∈ A, x ∈ D) :
    sumNat A ν ≤ sumNat D ν - 1 ∧ 1 ≤ sumNat D ν - 1 := by
  have hnot_both : ¬ (u ∈ A ∧ v ∈ A) := by
    rintro ⟨huA, hvA⟩
    exact hne (hA.2 u huA v hvA huv)
  have hnd_uv : NoDup [u, v] := NoDup.cons (by simp [hne]) (NoDup.cons (by simp) NoDup.nil)
  have hsub_uv : ∀ x ∈ [u, v], x ∈ D := by
    intro x hx; rcases List.mem_cons.mp hx with rfl | hx'
    · exact huD
    · simp at hx'; subst hx'; exact hvD
  have hD_ge2 : ν u + ν v ≤ sumNat D ν := by
    have h := sumNat_subset_le hnd_uv hsub_uv ν
    simp [sumNat] at h
    omega
  refine ⟨?_, by omega⟩
  by_cases huA : u ∈ A
  · have hv_not : v ∉ A := fun hvA => hnot_both ⟨huA, hvA⟩
    have hsplit := sumNat_filter_split D (fun x => decide (x = v)) ν
    have hv_filt : v ∈ D.filter (fun x => decide (x = v)) := by
      rw [mem_filter_iff_prop]; exact ⟨hvD, decide_eq_true rfl⟩
    have hhit : ν v ≤ sumNat (D.filter (fun x => decide (x = v))) ν :=
      mem_sumNat_le hv_filt ν
    have hsubA : ∀ x ∈ A, x ∈ D.filter (fun x => !decide (x = v)) := by
      intro x hx; rw [mem_filter_iff_prop]
      refine ⟨hAD x hx, ?_⟩
      have hxv : x ≠ v := fun h => hv_not (h ▸ hx)
      simp [hxv]
    have hleA := sumNat_subset_le hA.1 hsubA ν
    omega
  · have hsplit := sumNat_filter_split D (fun x => decide (x = u)) ν
    have hu_filt : u ∈ D.filter (fun x => decide (x = u)) := by
      rw [mem_filter_iff_prop]; exact ⟨huD, decide_eq_true rfl⟩
    have hhit : ν u ≤ sumNat (D.filter (fun x => decide (x = u))) ν :=
      mem_sumNat_le hu_filt ν
    have hsubA : ∀ x ∈ A, x ∈ D.filter (fun x => !decide (x = u)) := by
      intro x hx; rw [mem_filter_iff_prop]
      refine ⟨hAD x hx, ?_⟩
      have hxu : x ≠ u := fun h => huA (h ▸ hx)
      simp [hxu]
    have hleA := sumNat_subset_le hA.1 hsubA ν
    omega

/-- Global lower-Möbius total weight `∑_{y ∈ L} |μ(⊥, y)|`. -/
def totalAbsMobiusBot {α : Type} [DecidableEq α] (L : GeometricLattice α) : Nat :=
  sumNat L.elems (fun y => L.absMobius L.bot y)

/--
**Theorem 2 (Global |μ| Normalization Constant Is Strictly Improvable on Every Geometric Lattice):**
For EVERY finite geometric lattice `L` of rank `≥ 1`, there is an explicit rational constant
`C = (S - 1) / S < 1` (where `S = ∑_{y ∈ L} |μ(⊥, y)| ≥ 2`) such that EVERY antichain `A` in `L`
satisfies `∑_{x ∈ A} (|μ(⊥, x)| / S) ≤ C < 1`. Thus the LYM constant `1` CAN always be improved.
-/
theorem global_mobius_constant_improvable {α : Type} [DecidableEq α] (L : GeometricLattice α)
    (hrk_pos : 1 ≤ L.rk L.top) :
    0 < L.totalAbsMobiusBot ∧
    ∃ C : QRat, QRat.lt C QRat.one ∧
      ∀ (A : List α) (hpos : 0 < L.totalAbsMobiusBot), L.IsAntichain A →
        QRat.le (QRat.sumList A (fun x => QRat.mkNat (L.absMobius L.bot x) L.totalAbsMobiusBot hpos)) C := by
  have hr0 := L.rk_bot
  have hex_atom : ∃ a, L.rk a = 1 := by
    by_cases h1 : L.rk L.top = 1
    · exact ⟨L.top, h1⟩
    · rcases L.exists_step (L.bot_le L.top) (by omega) with ⟨a, _, _, _, hra⟩
      exact ⟨a, by omega⟩
  rcases hex_atom with ⟨a, hra⟩
  have hne : L.bot ≠ a := by intro h; rw [h] at hr0; omega
  have hbot_pos : 1 ≤ L.absMobius L.bot L.bot := by
    unfold absMobius; rw [L.mobius_self]; decide
  have hatom_pos : 1 ≤ L.absMobius L.bot a := by
    rw [L.absMobius_bot_atom hra]; exact Nat.le_refl 1
  have hS_ge2 : 2 ≤ L.totalAbsMobiusBot := by
    unfold totalAbsMobiusBot
    have hnd : NoDup [L.bot, a] := NoDup.cons (by simp [hne]) (NoDup.cons (by simp) NoDup.nil)
    have hsub : ∀ x ∈ [L.bot, a], x ∈ L.elems := fun x _ => L.mem_elems x
    have h := sumNat_subset_le hnd hsub (fun y => L.absMobius L.bot y)
    simp [sumNat] at h
    omega
  have hS_pos : 0 < L.totalAbsMobiusBot := by omega
  refine ⟨hS_pos, QRat.mkNat (L.totalAbsMobiusBot - 1) L.totalAbsMobiusBot hS_pos, ?_, ?_⟩
  · dsimp only [QRat.lt, QRat.mkNat, QRat.one]
    omega
  · intro A hpos hA
    apply QRat.le_of_eqv_left
      (QRat.sumList_const_den A (fun x => L.absMobius L.bot x) L.totalAbsMobiusBot hpos)
    unfold QRat.le QRat.mkNat
    have hbound := (L.antichain_sum_lt_of_comparable_pos L.nodup_elems
      (L.mem_elems L.bot) (L.mem_elems a) (L.bot_le a) hne
      (fun y => L.absMobius L.bot y) hbot_pos hatom_pos hA (fun x _ => L.mem_elems x)).1
    have hle_int : (sumNat A (fun y => L.absMobius L.bot y) : Int) ≤
        ((L.totalAbsMobiusBot - 1 : Nat) : Int) := Int.ofNat_le.mpr hbound
    exact Int.mul_le_mul_of_nonneg_right hle_int (Int.ofNat_le.mpr (Nat.zero_le _))

/-- Proper elements `L \ {⊥, ⊤} = {x ∈ L : 1 ≤ rk x ∧ rk x < rk ⊤}`. -/
def properElems {α : Type} [DecidableEq α] (L : GeometricLattice α) : List α :=
  L.elems.filter (fun x => decide (1 ≤ L.rk x ∧ L.rk x < L.rk L.top))

def totalProperAbsMobiusBot {α : Type} [DecidableEq α] (L : GeometricLattice α) : Nat :=
  sumNat L.properElems (fun y => L.absMobius L.bot y)

/--
**Theorem 3 (Proper-Global |μ| Normalization Constant Is Strictly Improvable for Rank ≥ 3):**
For EVERY finite geometric lattice `L` of rank `≥ 3`, normalizing `|μ(⊥, x)|` over proper flats
`L^\circ = L \ {⊥, ⊤}` still yields a strictly improvable constant `C = (S^\circ - 1) / S^\circ < 1`
for all proper antichains `A ⊆ L^\circ`.
-/
theorem proper_global_mobius_constant_improvable {α : Type} [DecidableEq α] (L : GeometricLattice α)
    (hrk3 : 3 ≤ L.rk L.top) :
    0 < L.totalProperAbsMobiusBot ∧
    ∃ C : QRat, QRat.lt C QRat.one ∧
      ∀ (A : List α) (hpos : 0 < L.totalProperAbsMobiusBot),
        L.IsAntichain A → (∀ x ∈ A, x ∈ L.properElems) →
        QRat.le (QRat.sumList A (fun x => QRat.mkNat (L.absMobius L.bot x) L.totalProperAbsMobiusBot hpos)) C := by
  have hr0 := L.rk_bot
  rcases L.exists_step (L.bot_le L.top) (by omega) with ⟨a, _, _, hat, hra_raw⟩
  have hra : L.rk a = 1 := by omega
  rcases L.exists_step hat (by omega) with ⟨b, hab, hba_ne, _, hrb_raw⟩
  have hrb : L.rk b = 2 := by omega
  have ha_prop : a ∈ L.properElems := by
    unfold properElems; rw [mem_filter_iff_prop]
    exact ⟨L.mem_elems a, decide_eq_true ⟨by omega, by omega⟩⟩
  have hb_prop : b ∈ L.properElems := by
    unfold properElems; rw [mem_filter_iff_prop]
    exact ⟨L.mem_elems b, decide_eq_true ⟨by omega, by omega⟩⟩
  have ha_pos : 1 ≤ L.absMobius L.bot a := by
    rw [L.absMobius_bot_atom hra]; exact Nat.le_refl 1
  have hb_pos : 1 ≤ L.absMobius L.bot b := L.absMobius_bot_rank2_pos hrb
  have hndP : NoDup L.properElems := nodup_filter _ L.nodup_elems
  have hS_ge2 : 2 ≤ L.totalProperAbsMobiusBot := by
    unfold totalProperAbsMobiusBot
    have hnd : NoDup [a, b] := NoDup.cons (by simp [Ne.symm hba_ne]) (NoDup.cons (by simp) NoDup.nil)
    have hsub : ∀ x ∈ [a, b], x ∈ L.properElems := by
      intro x hx; rcases List.mem_cons.mp hx with rfl | hx'
      · exact ha_prop
      · simp at hx'; subst hx'; exact hb_prop
    have h := sumNat_subset_le hnd hsub (fun y => L.absMobius L.bot y)
    simp [sumNat] at h
    omega
  have hS_pos : 0 < L.totalProperAbsMobiusBot := by omega
  refine ⟨hS_pos, QRat.mkNat (L.totalProperAbsMobiusBot - 1) L.totalProperAbsMobiusBot hS_pos, ?_, ?_⟩
  · dsimp only [QRat.lt, QRat.mkNat, QRat.one]
    omega
  · intro A hpos hA hAD
    apply QRat.le_of_eqv_left
      (QRat.sumList_const_den A (fun x => L.absMobius L.bot x) L.totalProperAbsMobiusBot hpos)
    unfold QRat.le QRat.mkNat
    have hbound := (L.antichain_sum_lt_of_comparable_pos hndP
      ha_prop hb_prop hab (Ne.symm hba_ne)
      (fun y => L.absMobius L.bot y) ha_pos hb_pos hA hAD).1
    have hle_int : (sumNat A (fun y => L.absMobius L.bot y) : Int) ≤
        ((L.totalProperAbsMobiusBot - 1 : Nat) : Int) := Int.ofNat_le.mpr hbound
    exact Int.mul_le_mul_of_nonneg_right hle_int (Int.ofNat_le.mpr (Nat.zero_le _))

end GeometricLattice

end Conjecture00000008533
