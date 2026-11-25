/-
  Conjecture 00000007178 — Pillars 3 & 4:
  Spectral Graph Minimum Rank `mr_F(G)`, Fano Characteristic Separation, & Haemers Minrank
  1. Universal `mr_F(G) = 1` characterization: `mr_F(G) = 1 ↔ ActiveCliqueProp G` (forbidden
     induced subgraphs are `P₃` and `2K₂` — both acyclic forests, NOT cycle-parity obstructions!).
  2. Minimal `5`-vertex chordal simple graph `G₅ = K₅ \ P₃`:
     `mr_{𝔽₂}(G₅) = 3 ≠ 2 = mr_F(G₅)` for EVERY field `F` with `|F| ≥ 3` (including `𝔽₃` and `𝔽₄`!),
     proving `mr_F(G)` is NOT a purely combinatorial graph invariant.
  3. Infinite-field characteristic dependence on the `7 × 7` Fano zero-nonzero pattern `Z_Fano`:
     `mr_F^{znz}(Z_Fano) = 3` for EVERY field of `char(F) = 2` (including `𝔽₂, 𝔽₄, F̄₂`) vs.
     `mr_F^{znz}(Z_Fano) = 4` for EVERY field of `char(F) ≠ 2` (including `𝔽₃, ℚ, ℝ, ℂ`).
  4. Haemers minrank cycle-parity reversal over EVERY field `F`:
     Bipartite even `6`-cycle `C₆` (zero odd cycles) has `minrank_F(C₆) = 3`, whereas its
     non-bipartite complement `C₆^c` (containing odd `C₃` triangles) has `minrank_F(C₆^c) = 2 < 3`.
-/

import Conjecture00000007178.SymmetricCycles

namespace Conjecture00000007178

universe u

open CommRingR FieldR

/-- Finite simple undirected graph on `Fin n`. -/
structure SimpleGraph (n : Nat) where
  adj      : Fin n → Fin n → Bool
  loopless : ∀ i : Fin n, adj i i = false
  symm     : ∀ i j : Fin n, adj i j = adj j i

/-- `M ∈ S_F(G)` in the standard spectral graph minimum-rank sense: `M` is symmetric,
its diagonal is completely free, and for `i ≠ j`, `M i j ≠ 0 ↔ G.adj i j = true`. -/
def FitsGraph (F : Type u) [CommRingR F] {n : Nat} (G : SimpleGraph n) (M : Mat F n n) : Prop :=
  IsSymmetric M ∧ ∀ i j : Fin n, i ≠ j → (M i j ≠ 0 ↔ G.adj i j = true)

/-- Exact spectral graph minimum rank `mr_F(G) = r`. -/
def IsGraphMinRank (F : Type u) [CommRingR F] {n : Nat} (G : SimpleGraph n) (r : Nat) : Prop :=
  (∃ M : Mat F n n, FitsGraph F G M ∧ HasRankAtMost F r M) ∧
  (∀ r' : Nat, r' < r → ∀ M : Mat F n n, FitsGraph F G M → ¬ HasRankAtMost F r' M)

/-! ### 3A. Universal Characterization of `mr_F(G) = 1`: `(P₃, 2K₂)`-Freeness (Acyclic Obstructions!) -/

/-- Decidable check whether vertex `i` has at least one neighbor in `G`. -/
def finAny : {n : Nat} → (Fin n → Bool) → Bool
  | 0, _ => false
  | n + 1, p => p ⟨0, Nat.zero_lt_succ n⟩ || finAny (fun t : Fin n => p ⟨t.val + 1, Nat.succ_lt_succ t.isLt⟩)

theorem finAny_eq_true {n : Nat} {p : Fin n → Bool} :
    finAny p = true ↔ ∃ k : Fin n, p k = true := by
  induction n with
  | zero =>
    constructor
    · intro h; contradiction
    · rintro ⟨k, _⟩; exact Fin.elim0 k
  | succ n ih =>
    unfold finAny
    constructor
    · intro h
      cases h0 : p ⟨0, Nat.zero_lt_succ n⟩ with
      | true => exact ⟨⟨0, Nat.zero_lt_succ n⟩, h0⟩
      | false =>
        rw [h0, Bool.false_or] at h
        rcases ih.mp h with ⟨t, ht⟩
        exact ⟨⟨t.val + 1, Nat.succ_lt_succ t.isLt⟩, ht⟩
    · rintro ⟨k, hk⟩
      rcases k with ⟨val, isLt⟩
      cases val with
      | zero =>
        rw [hk]
        rfl
      | succ v =>
        have hv : v < n := Nat.lt_of_succ_lt_succ isLt
        have hex : ∃ t : Fin n, p ⟨t.val + 1, Nat.succ_lt_succ t.isLt⟩ = true :=
          ⟨⟨v, hv⟩, hk⟩
        rw [ih.mpr hex, Bool.or_true]

/-- Combinatorial `(P₃, 2K₂)`-freeness (single active clique plus isolated vertices):
any two distinct non-isolated vertices are adjacent. -/
def ActiveCliqueProp {n : Nat} (G : SimpleGraph n) : Prop :=
  ∀ a b c d : Fin n, G.adj a b = true → G.adj c d = true → a ≠ c → G.adj a c = true

/-- Universal Rank-`1` Graph Theorem: over EVERY field `F`, a nonempty simple graph `G`
satisfies `mr_F(G) = 1` if and only if `ActiveCliqueProp G` holds (i.e. `G` is `(P₃, 2K₂)`-free,
whose forbidden induced subgraphs `P₃` and `2K₂` are acyclic forests!). -/
theorem graph_minRank_one_iff_activeClique {F : Type u} [FieldR F] {n : Nat}
    (G : SimpleGraph n) (hne : ∃ i₀ j₀ : Fin n, G.adj i₀ j₀ = true) :
    IsGraphMinRank F G 1 ↔ ActiveCliqueProp G := by
  constructor
  · rintro ⟨⟨M, ⟨_, hfit⟩, hrk1⟩, _⟩
    rcases (hasRankAtMost_one_iff_outer M).mp hrk1 with ⟨u, v, huv⟩
    intro a b c d hab hcd hac
    have hab_ne : a ≠ b := by
      intro heq; subst heq; rw [G.loopless a] at hab; contradiction
    have hcd_ne : d ≠ c := by
      intro heq; subst heq; rw [G.loopless d] at hcd; contradiction
    have hdc : G.adj d c = true := by rw [G.symm d c]; exact hcd
    have hm_ab : M a b ≠ 0 := (hfit a b hab_ne).mpr hab
    have hm_dc : M d c ≠ 0 := (hfit d c hcd_ne).mpr hdc
    rw [huv a b] at hm_ab
    rw [huv d c] at hm_dc
    have hua : u a ≠ 0 := fun h0 => hm_ab (by rw [h0, zero_mul])
    have hvc : v c ≠ 0 := fun h0 => hm_dc (by rw [h0, mul_zero])
    have hm_ac : M a c ≠ 0 := by
      rw [huv a c]
      exact mul_ne_zero hua hvc
    exact (hfit a c hac).mp hm_ac
  · intro hact
    let act : Fin n → Bool := fun i => finAny (fun k => G.adj i k)
    let u : Fin n → F := fun i => if act i = true then 1 else 0
    let M : Mat F n n := fun i j => u i * u j
    have hsymM : IsSymmetric M := by
      intro i j; dsimp [M]; rw [mul_comm]
    have hrkM : HasRankAtMost F 1 M :=
      (hasRankAtMost_one_iff_outer M).mpr ⟨u, u, fun _ _ => rfl⟩
    have hfitM : FitsGraph F G M := by
      refine ⟨hsymM, ?_⟩
      intro i j hij
      constructor
      · intro hmnz
        dsimp [M, u] at hmnz
        by_cases hi : act i = true
        · by_cases hj : act j = true
          · rcases (finAny_eq_true (p := fun k => G.adj i k)).mp hi with ⟨b, hb⟩
            rcases (finAny_eq_true (p := fun k => G.adj j k)).mp hj with ⟨d, hd⟩
            exact hact i b j d hb hd hij
          · simp [hi, hj, mul_zero] at hmnz
        · simp [hi, zero_mul] at hmnz
      · intro hadj
        have hi : act i = true :=
          (finAny_eq_true (p := fun k => G.adj i k)).mpr ⟨j, hadj⟩
        have hj : act j = true :=
          (finAny_eq_true (p := fun k => G.adj j k)).mpr ⟨i, by rw [G.symm j i]; exact hadj⟩
        dsimp [M, u]
        simp only [hi, hj, ↓reduceIte, mul_one]
        exact one_ne_zero
    refine ⟨⟨M, hfitM, hrkM⟩, ?_⟩
    intro r' hr' N hfitN
    have hr0 : r' = 0 := by omega
    subst hr0
    rcases hne with ⟨i₀, j₀, hadj₀⟩
    have hij₀ : i₀ ≠ j₀ := by
      intro heq; subst heq; rw [G.loopless i₀] at hadj₀; contradiction
    have hnz : N i₀ j₀ ≠ 0 := (hfitN.2 i₀ j₀ hij₀).mpr hadj₀
    exact not_hasRankAtMost_zero_of_entry_ne_zero i₀ j₀ hnz

/-! ### 3B. Minimal `5`-Vertex Chordal Graph `G₅ = K₅ \ P₃`: Field Dependence `mr_{𝔽₂} = 3 ≠ 2 = mr_F` -/

/-- The `5`-vertex chordal simple graph `G₅ = K₅ \ {(2,4), (3,4)}` (`8` edges). -/
def G5 : SimpleGraph 5 where
  adj i j :=
    i != j &&
    !(i == 2 && j == 4) && !(i == 4 && j == 2) &&
    !(i == 3 && j == 4) && !(i == 4 && j == 3)
  loopless := by decide
  symm := by decide

theorem G5_not_rank_one {F : Type u} [FieldR F]
    (M : Mat F 5 5) (hfit : FitsGraph F G5 M) :
    ¬ HasRankAtMost F 1 M := by
  intro hrk1
  -- `G5` has edges `(2, 3)` and `(4, 0)` (`2 ≠ 4`), yet `(2, 4)` is a non-edge!
  rcases (hasRankAtMost_one_iff_outer M).mp hrk1 with ⟨u, v, huv⟩
  have hm23 : M 2 3 ≠ 0 := (hfit.2 2 3 (by decide)).mpr rfl
  have hm04 : M 0 4 ≠ 0 := (hfit.2 0 4 (by decide)).mpr rfl
  have hm24 : M 2 4 = 0 := by
    by_cases hz : M 2 4 = 0
    · exact hz
    · have hbad : G5.adj 2 4 = true := (hfit.2 2 4 (by decide)).mp hz
      contradiction
  rw [huv 2 3] at hm23
  rw [huv 0 4] at hm04
  have hu2 : u 2 ≠ 0 := fun h0 => hm23 (by rw [h0, zero_mul])
  have hv4 : v 4 ≠ 0 := fun h0 => hm04 (by rw [h0, mul_zero])
  exact mul_ne_zero hu2 hv4 (by rw [← huv 2 4, hm24])

/-- Over `𝔽₂`, the chordal `5`-vertex graph `G₅` has exact minimum rank `3`. -/
theorem G5_minRank_F2_eq_three : IsGraphMinRank F2 G5 3 := by
  constructor
  · -- Explicit rank-3 Gram matrix `U * U^T` over `F2`:
    -- rows `(1,1,1), (1,1,1), (1,0,0), (1,0,0), (0,1,0)`
    let U : Mat F2 5 3 := fun i t =>
      match i.val, t.val with
      | 0, _ => 1
      | 1, _ => 1
      | 2, 0 => 1 | 2, _ => 0
      | 3, 0 => 1 | 3, _ => 0
      | _, 1 => 1 | _, _ => 0
    let UT : Mat F2 3 5 := fun t j => U j t
    let M : Mat F2 5 5 := fun i j => finSum (fun t : Fin 3 => U i t * UT t j)
    refine ⟨M, ⟨?_, ?_⟩, ⟨U, UT, fun _ _ => rfl⟩⟩
    · refine fin5_cases ?_ ?_ ?_ ?_ ?_ <;> refine fin5_cases ?_ ?_ ?_ ?_ ?_ <;> rfl
    · refine fin5_cases ?_ ?_ ?_ ?_ ?_ <;> refine fin5_cases ?_ ?_ ?_ ?_ ?_ <;> intro hij <;> first
        | exact absurd rfl hij
        | (dsimp [M, UT, U]; decide)
  · intro r' hr' M hfit hrk
    have hle2 : r' ≤ 2 := by omega
    have hrk2 : HasRankAtMost F2 2 M := HasRankAtMost.mono hle2 hrk
    have hdet := subDet3_eq_zero_of_rank_le_two hrk2 0 2 4 1 3 4
    -- Over `F2`, every edge entry of `M` equals `1`, and `(2,4) = (4,3) = 0`!
    have e01 : M 0 1 = 1 := F2.eq_one_of_ne_zero ((hfit.2 0 1 (by decide)).mpr rfl)
    have e03 : M 0 3 = 1 := F2.eq_one_of_ne_zero ((hfit.2 0 3 (by decide)).mpr rfl)
    have e04 : M 0 4 = 1 := F2.eq_one_of_ne_zero ((hfit.2 0 4 (by decide)).mpr rfl)
    have e21 : M 2 1 = 1 := F2.eq_one_of_ne_zero ((hfit.2 2 1 (by decide)).mpr rfl)
    have e23 : M 2 3 = 1 := F2.eq_one_of_ne_zero ((hfit.2 2 3 (by decide)).mpr rfl)
    have e41 : M 4 1 = 1 := F2.eq_one_of_ne_zero ((hfit.2 4 1 (by decide)).mpr rfl)
    have z24 : M 2 4 = 0 := by
      cases h : M 2 4 with
      | zero => rfl
      | one =>
        have hbad : G5.adj 2 4 = true := (hfit.2 2 4 (by decide)).mp (by rw [h]; decide)
        contradiction
    have z43 : M 4 3 = 0 := by
      cases h : M 4 3 with
      | zero => rfl
      | one =>
        have hbad : G5.adj 4 3 = true := (hfit.2 4 3 (by decide)).mp (by rw [h]; decide)
        contradiction
    unfold subDet3 at hdet
    rw [e01, e03, e04, e21, e23, z24, e41, z43] at hdet
    cases hd4 : M 4 4 <;> rw [hd4] at hdet <;> contradiction

/-- Over EVERY field `F` of cardinality at least `3` (`∃ α : F, α ≠ 0 ∧ α ≠ 1`, including BOTH
`𝔽₃` in characteristic `3` and `𝔽₄` in characteristic `2`, as well as `ℚ, ℝ, ℂ`),
`G₅` has exact minimum rank `2`! -/
theorem G5_minRank_card_ge_three_eq_two {F : Type u} [FieldR F]
    (hcard : ∃ α : F, α ≠ 0 ∧ α ≠ 1) :
    IsGraphMinRank F G5 2 := by
  rcases exists_nonzero_one_add_ne_zero hcard with ⟨β, hβ0, hβ1⟩
  constructor
  · -- Universal rank-2 Gram matrix `U * U^T` with rows `(1,1), (1,β), (1,0), (1,0), (0,1)`
    let U : Mat F 5 2 := fun i t =>
      match i.val, t.val with
      | 0, _ => 1
      | 1, 0 => 1 | 1, _ => β
      | 2, 0 => 1 | 2, _ => 0
      | 3, 0 => 1 | 3, _ => 0
      | _, 0 => 0 | _, _ => 1
    let UT : Mat F 2 5 := fun t j => U j t
    let M : Mat F 5 5 := fun i j => finSum (fun t : Fin 2 => U i t * UT t j)
    refine ⟨M, ⟨?_, ?_⟩, ⟨U, UT, fun _ _ => rfl⟩⟩
    · have hcomm2 : ∀ a0 b0 a1 b1 : F, a0 * b0 + a1 * b1 = b0 * a0 + b1 * a1 :=
        fun a0 b0 a1 b1 => by rw [mul_comm a0 b0, mul_comm a1 b1]
      intro i j
      dsimp [M, UT]
      rw [finSum_two, finSum_two]
      exact hcomm2 _ _ _ _
    · refine fin5_cases ?_ ?_ ?_ ?_ ?_ <;> refine fin5_cases ?_ ?_ ?_ ?_ ?_ <;> intro hij <;>
        (dsimp [M, UT]; rw [finSum_two])
      · exact absurd rfl hij
      · dsimp [U, G5]; rw [one_mul, one_mul]; exact ⟨fun _ => rfl, fun _ => hβ1⟩
      · dsimp [U, G5]; rw [one_mul, mul_zero, add_zero]; exact ⟨fun _ => rfl, fun _ => one_ne_zero⟩
      · dsimp [U, G5]; rw [one_mul, mul_zero, add_zero]; exact ⟨fun _ => rfl, fun _ => one_ne_zero⟩
      · dsimp [U, G5]; rw [mul_zero, one_mul, zero_add]; exact ⟨fun _ => rfl, fun _ => one_ne_zero⟩
      · dsimp [U, G5]; rw [one_mul, mul_one]; exact ⟨fun _ => rfl, fun _ => hβ1⟩
      · exact absurd rfl hij
      · dsimp [U, G5]; rw [one_mul, mul_zero, add_zero]; exact ⟨fun _ => rfl, fun _ => one_ne_zero⟩
      · dsimp [U, G5]; rw [one_mul, mul_zero, add_zero]; exact ⟨fun _ => rfl, fun _ => one_ne_zero⟩
      · dsimp [U, G5]; rw [mul_zero, mul_one, zero_add]; exact ⟨fun _ => rfl, fun _ => hβ0⟩
      · dsimp [U, G5]; rw [one_mul, zero_mul, add_zero]; exact ⟨fun _ => rfl, fun _ => one_ne_zero⟩
      · dsimp [U, G5]; rw [one_mul, zero_mul, add_zero]; exact ⟨fun _ => rfl, fun _ => one_ne_zero⟩
      · exact absurd rfl hij
      · dsimp [U, G5]; rw [one_mul, zero_mul, add_zero]; exact ⟨fun _ => rfl, fun _ => one_ne_zero⟩
      · dsimp [U, G5]; rw [mul_zero, zero_mul, add_zero]; exact ⟨fun h => absurd rfl h, fun h => by contradiction⟩
      · dsimp [U, G5]; rw [one_mul, zero_mul, add_zero]; exact ⟨fun _ => rfl, fun _ => one_ne_zero⟩
      · dsimp [U, G5]; rw [one_mul, zero_mul, add_zero]; exact ⟨fun _ => rfl, fun _ => one_ne_zero⟩
      · dsimp [U, G5]; rw [one_mul, zero_mul, add_zero]; exact ⟨fun _ => rfl, fun _ => one_ne_zero⟩
      · exact absurd rfl hij
      · dsimp [U, G5]; rw [mul_zero, zero_mul, add_zero]; exact ⟨fun h => absurd rfl h, fun h => by contradiction⟩
      · dsimp [U, G5]; rw [zero_mul, one_mul, zero_add]; exact ⟨fun _ => rfl, fun _ => one_ne_zero⟩
      · dsimp [U, G5]; rw [zero_mul, one_mul, zero_add]; exact ⟨fun _ => rfl, fun _ => hβ0⟩
      · dsimp [U, G5]; rw [zero_mul, mul_zero, add_zero]; exact ⟨fun h => absurd rfl h, fun h => by contradiction⟩
      · dsimp [U, G5]; rw [zero_mul, mul_zero, add_zero]; exact ⟨fun h => absurd rfl h, fun h => by contradiction⟩
      · exact absurd rfl hij
  · intro r' hr' M hfit
    have hcases : r' = 0 ∨ r' = 1 := by omega
    cases hcases with
    | inl h0 =>
      subst h0
      have hnz : M 0 1 ≠ 0 := (hfit.2 0 1 (by decide)).mpr rfl
      exact not_hasRankAtMost_zero_of_entry_ne_zero 0 1 hnz
    | inr h1 =>
      subst h1
      exact G5_not_rank_one M hfit

/-! ### 3C. Characteristic Dependence Across Arbitrary (Even Infinite) Fields:
    The `7 × 7` Fano Zero-Nonzero Pattern `Z_Fano` -/

/-- The `7` nonzero points of `𝔽₂³`. -/
def fanoVec (i : Fin 7) (t : Fin 3) : Nat :=
  match i.val, t.val with
  | 0, 0 => 1 | 0, _ => 0
  | 1, 1 => 1 | 1, _ => 0
  | 2, 2 => 1 | 2, _ => 0
  | 3, 0 => 1 | 3, 1 => 1 | 3, _ => 0
  | 4, 0 => 1 | 4, 2 => 1 | 4, _ => 0
  | 5, 1 => 1 | 5, 2 => 1 | 5, _ => 0
  | _, _ => 1

/-- The `7 × 7` Fano inner-product zero-nonzero pattern (`Z_Fano i j = true` iff `⟨p_i, p_j⟩ ≡ 1 mod 2`). -/
def Z_Fano (i j : Fin 7) : Bool :=
  ((fanoVec i 0 * fanoVec j 0 + fanoVec i 1 * fanoVec j 1 + fanoVec i 2 * fanoVec j 2) % 2) == 1

def FitsZNZ (F : Type u) [CommRingR F] {m n : Nat} (Z : Fin m → Fin n → Bool) (M : Mat F m n) : Prop :=
  ∀ i j, (M i j ≠ 0 ↔ Z i j = true)

def IsZNZMinRank (F : Type u) [CommRingR F] {m n : Nat} (Z : Fin m → Fin n → Bool) (r : Nat) : Prop :=
  (∃ M : Mat F m n, FitsZNZ F Z M ∧ HasRankAtMost F r M) ∧
  (∀ r' : Nat, r' < r → ∀ M : Mat F m n, FitsZNZ F Z M → ¬ HasRankAtMost F r' M)

theorem fano_not_rank_le_two {F : Type u} [FieldR F]
    (M : Mat F 7 7) (hfit : FitsZNZ F Z_Fano M) :
    ¬ HasRankAtMost F 2 M := by
  intro hrk2
  have hdet := subDet3_eq_zero_of_rank_le_two hrk2 0 1 2 0 1 2
  have d0 : M 0 0 ≠ 0 := (hfit 0 0).mpr rfl
  have d1 : M 1 1 ≠ 0 := (hfit 1 1).mpr rfl
  have d2 : M 2 2 ≠ 0 := (hfit 2 2).mpr rfl
  have z01 : M 0 1 = 0 := by
    by_cases hz : M 0 1 = 0; exact hz
    have hb : Z_Fano 0 1 = true := (hfit 0 1).mp hz; contradiction
  have z02 : M 0 2 = 0 := by
    by_cases hz : M 0 2 = 0; exact hz
    have hb : Z_Fano 0 2 = true := (hfit 0 2).mp hz; contradiction
  have z12 : M 1 2 = 0 := by
    by_cases hz : M 1 2 = 0; exact hz
    have hb : Z_Fano 1 2 = true := (hfit 1 2).mp hz; contradiction
  have z21 : M 2 1 = 0 := by
    by_cases hz : M 2 1 = 0; exact hz
    have hb : Z_Fano 2 1 = true := (hfit 2 1).mp hz; contradiction
  unfold subDet3 at hdet
  rw [z01, z02, z12, z21, mul_zero, sub_zero, zero_mul, sub_zero, zero_mul, add_zero] at hdet
  exact mul_ne_zero d0 (mul_ne_zero d1 d2) hdet

/-- Over EVERY field `F` of characteristic `2` (`1 + 1 = 0`, including `𝔽₂, 𝔽₄`, and infinite `F̄₂`),
`Z_Fano` has exact minimum rank `3`. -/
theorem fano_znz_minRank_char_two {F : Type u} [FieldR F] (hchar2 : (1 : F) + 1 = 0) :
    IsZNZMinRank F Z_Fano 3 := by
  constructor
  · let P : Mat F 7 3 := fun i t => match fanoVec i t with | 1 => 1 | _ => 0
    let PT : Mat F 3 7 := fun t j => P j t
    let M : Mat F 7 7 := fun i j => finSum (fun t : Fin 3 => P i t * PT t j)
    refine ⟨M, ?_, ⟨P, PT, fun _ _ => rfl⟩⟩
    refine fin7_cases ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> refine fin7_cases ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      (dsimp [M, PT]; rw [finSum_three]; dsimp [P, fanoVec, Z_Fano];
       simp only [one_mul, zero_mul, mul_zero, add_zero, zero_add, hchar2];
       first
         | exact ⟨fun _ => trivial, fun _ => one_ne_zero⟩
         | exact ⟨fun h => False.elim (h trivial), fun h => by contradiction⟩)
  · intro r' hr' M hfit hrk
    have hle2 : r' ≤ 2 := by omega
    exact fano_not_rank_le_two M hfit (HasRankAtMost.mono hle2 hrk)

/-- Key linear-independence lemma for `3`-factor decompositions: if `M = U_{7×3} V_{3×7}` fits
`Z_Fano`, then any linear relation `w₀ V₀ + w₁ V₁ + w₂ V₂` vanishing on columns `0, 1, 2`
must satisfy `w₀ = w₁ = w₂ = 0`! -/
theorem fano_factor_kernel_trivial {F : Type u} [FieldR F]
    {U : Mat F 7 3} {V : Mat F 3 7} {M : Mat F 7 7}
    (hM : ∀ i j, M i j = finSum (fun t : Fin 3 => U i t * V t j))
    (hfit : FitsZNZ F Z_Fano M)
    (w0 w1 w2 : F)
    (hk0 : w0 * V 0 0 + (w1 * V 1 0 + w2 * V 2 0) = 0)
    (hk1 : w0 * V 0 1 + (w1 * V 1 1 + w2 * V 2 1) = 0)
    (hk2 : w0 * V 0 2 + (w1 * V 1 2 + w2 * V 2 2) = 0) :
    w0 = 0 ∧ w1 = 0 ∧ w2 = 0 := by
  -- If `w_t ≠ 0`, row `t` of `V[·, {0,1,2}]` is a linear combination of the other two rows,
  -- giving `HasRankAtMost F 2 (submatrix M {0,1,2} {0,1,2})`, contradicting `subDet3 ≠ 0`!
  let subM : Mat F 3 3 := fun i k => M ⟨i.val, by omega⟩ ⟨k.val, by omega⟩
  have hsub_not2 : ¬ HasRankAtMost F 2 subM := by
    intro hrk2
    have hdet := subDet3_eq_zero_of_rank_le_two hrk2 0 1 2 0 1 2
    have hd0 : M 0 0 ≠ 0 := (hfit 0 0).mpr rfl
    have hd1 : M 1 1 ≠ 0 := (hfit 1 1).mpr rfl
    have hd2 : M 2 2 ≠ 0 := (hfit 2 2).mpr rfl
    have z01 : M 0 1 = 0 := by
      by_cases hz : M 0 1 = 0; exact hz
      have hb : Z_Fano 0 1 = true := (hfit 0 1).mp hz; contradiction
    have z02 : M 0 2 = 0 := by
      by_cases hz : M 0 2 = 0; exact hz
      have hb : Z_Fano 0 2 = true := (hfit 0 2).mp hz; contradiction
    have z12 : M 1 2 = 0 := by
      by_cases hz : M 1 2 = 0; exact hz
      have hb : Z_Fano 1 2 = true := (hfit 1 2).mp hz; contradiction
    have z21 : M 2 1 = 0 := by
      by_cases hz : M 2 1 = 0; exact hz
      have hb : Z_Fano 2 1 = true := (hfit 2 1).mp hz; contradiction
    unfold subDet3 at hdet
    dsimp [subM] at hdet
    rw [z01, z02, z12, z21, mul_zero, sub_zero, zero_mul, sub_zero, zero_mul, add_zero] at hdet
    exact mul_ne_zero hd0 (mul_ne_zero hd1 hd2) hdet
  have hk_all : ∀ k : Fin 3,
      w0 * V 0 ⟨k.val, by omega⟩ + (w1 * V 1 ⟨k.val, by omega⟩ + w2 * V 2 ⟨k.val, by omega⟩) = 0 := by
    refine fin3_cases ?_ ?_ ?_
    · exact hk0
    · exact hk1
    · exact hk2
  have hw0 : w0 = 0 := by
    by_cases h0 : w0 = 0
    · exact h0
    · exfalso
      apply hsub_not2
      -- Express `V 0 k = (-w0⁻¹ * w1) * V 1 k + (-w0⁻¹ * w2) * V 2 k`
      let c1 := -(w0⁻¹ * w1)
      let c2 := -(w0⁻¹ * w2)
      have hv0 : ∀ k : Fin 3,
          V 0 ⟨k.val, by omega⟩ = c1 * V 1 ⟨k.val, by omega⟩ + c2 * V 2 ⟨k.val, by omega⟩ := by
        intro k
        have hrel := hk_all k
        have hneg := eq_neg_of_add_eq_zero hrel
        apply mul_left_cancel h0
        rw [hneg, left_distrib]
        dsimp [c1, c2]
        have t1 : w0 * (-(w0⁻¹ * w1) * V 1 ⟨k.val, by omega⟩) = -(w1 * V 1 ⟨k.val, by omega⟩) := by
          rw [neg_mul, mul_neg, ← mul_assoc, ← mul_assoc, FieldR.mul_inv_cancel w0 h0, one_mul]
        have t2 : w0 * (-(w0⁻¹ * w2) * V 2 ⟨k.val, by omega⟩) = -(w2 * V 2 ⟨k.val, by omega⟩) := by
          rw [neg_mul, mul_neg, ← mul_assoc, ← mul_assoc, FieldR.mul_inv_cancel w0 h0, one_mul]
        rw [t1, t2, ← neg_add]
      let U2 : Mat F 3 2 := fun i s =>
        match s.val with
        | 0 => U ⟨i.val, by omega⟩ 1 + U ⟨i.val, by omega⟩ 0 * c1
        | _ => U ⟨i.val, by omega⟩ 2 + U ⟨i.val, by omega⟩ 0 * c2
      let V2 : Mat F 2 3 := fun s k =>
        match s.val with
        | 0 => V 1 ⟨k.val, by omega⟩
        | _ => V 2 ⟨k.val, by omega⟩
      refine ⟨U2, V2, ?_⟩
      intro i k
      dsimp [subM]
      rw [hM ⟨i.val, by omega⟩ ⟨k.val, by omega⟩, finSum_three, finSum_two]
      dsimp [U2, V2]
      rw [hv0 k, left_distrib, right_distrib, right_distrib, mul_assoc, mul_assoc]
      let A := U ⟨i.val, by omega⟩ 0 * (c1 * V 1 ⟨k.val, by omega⟩)
      let B := U ⟨i.val, by omega⟩ 0 * (c2 * V 2 ⟨k.val, by omega⟩)
      let C := U ⟨i.val, by omega⟩ 1 * V 1 ⟨k.val, by omega⟩
      let D := U ⟨i.val, by omega⟩ 2 * V 2 ⟨k.val, by omega⟩
      show (A + B) + (C + D) = (C + A) + (D + B)
      calc
        (A + B) + (C + D) = A + (B + (C + D)) := by rw [add_assoc]
        _ = A + ((B + C) + D) := by rw [← add_assoc B C D]
        _ = A + ((C + B) + D) := by rw [add_comm B C]
        _ = (A + C) + (B + D) := by rw [add_assoc C B D, ← add_assoc A C (B + D)]
        _ = (C + A) + (D + B) := by rw [add_comm A C, add_comm B D]
  rw [hw0] at hk_all
  have hw1 : w1 = 0 := by
    by_cases h1 : w1 = 0
    · exact h1
    · exfalso
      apply hsub_not2
      let c2 := -(w1⁻¹ * w2)
      have hv1 : ∀ k : Fin 3,
          V 1 ⟨k.val, by omega⟩ = c2 * V 2 ⟨k.val, by omega⟩ := by
        intro k
        have hrel := hk_all k
        rw [zero_mul, zero_add] at hrel
        have hneg := eq_neg_of_add_eq_zero hrel
        apply mul_left_cancel h1
        rw [hneg]
        dsimp [c2]
        rw [neg_mul, mul_neg, ← mul_assoc, ← mul_assoc, FieldR.mul_inv_cancel w1 h1, one_mul]
      let U2 : Mat F 3 2 := fun i s =>
        match s.val with
        | 0 => U ⟨i.val, by omega⟩ 0
        | _ => U ⟨i.val, by omega⟩ 2 + U ⟨i.val, by omega⟩ 1 * c2
      let V2 : Mat F 2 3 := fun s k =>
        match s.val with
        | 0 => V 0 ⟨k.val, by omega⟩
        | _ => V 2 ⟨k.val, by omega⟩
      refine ⟨U2, V2, ?_⟩
      intro i k
      dsimp [subM]
      rw [hM ⟨i.val, by omega⟩ ⟨k.val, by omega⟩, finSum_three, finSum_two]
      dsimp [U2, V2]
      rw [hv1 k, right_distrib, mul_assoc, add_comm (U ⟨i.val, by omega⟩ 2 * V 2 ⟨k.val, by omega⟩)]
  rw [hw1] at hk_all
  have hw2 : w2 = 0 := by
    by_cases h2 : w2 = 0
    · exact h2
    · exfalso
      apply hsub_not2
      have hv2 : ∀ k : Fin 3, V 2 ⟨k.val, by omega⟩ = 0 := by
        intro k
        have hrel := hk_all k
        rw [zero_mul, zero_add, zero_mul, zero_add] at hrel
        cases mul_eq_zero hrel with
        | inl hc => exact absurd hc h2
        | inr hv => exact hv
      let U2 : Mat F 3 2 := fun i s =>
        match s.val with
        | 0 => U ⟨i.val, by omega⟩ 0
        | _ => U ⟨i.val, by omega⟩ 1
      let V2 : Mat F 2 3 := fun s k =>
        match s.val with
        | 0 => V 0 ⟨k.val, by omega⟩
        | _ => V 1 ⟨k.val, by omega⟩
      refine ⟨U2, V2, ?_⟩
      intro i k
      dsimp [subM]
      rw [hM ⟨i.val, by omega⟩ ⟨k.val, by omega⟩, finSum_three, finSum_two]
      dsimp [U2, V2]
      rw [hv2 k, mul_zero, add_zero]
  exact ⟨hw0, hw1, hw2⟩

/-- Over EVERY field `F` of characteristic `≠ 2` (`1 + 1 ≠ 0`), NO matrix fitting `Z_Fano`
has rank `≤ 3`! -/
theorem fano_not_rank_le_three_char_ne_two {F : Type u} [FieldR F]
    (hchar : (1 : F) + 1 ≠ 0)
    (M : Mat F 7 7) (hfit : FitsZNZ F Z_Fano M) :
    ¬ HasRankAtMost F 3 M := by
  rintro ⟨U, V, hM⟩
  have zm : ∀ i j : Fin 7, Z_Fano i j = false → M i j = 0 := by
    intro i j hzf
    by_cases hz : M i j = 0
    · exact hz
    · have ht : Z_Fano i j = true := (hfit i j).mp hz
      rw [hzf] at ht; contradiction
  have nzm : ∀ i j : Fin 7, Z_Fano i j = true → M i j ≠ 0 :=
    fun i j hzt => (hfit i j).mpr hzt
  have d0 : M 0 0 ≠ 0 := nzm 0 0 rfl
  have d1 : M 1 1 ≠ 0 := nzm 1 1 rfl
  have d2 : M 2 2 ≠ 0 := nzm 2 2 rfl
  -- Every row `r` of `M` is the exact linear combination of Rows `0, 1, 2`!
  let α0 (r : Fin 7) : F := M r 0 * (M 0 0)⁻¹
  let α1 (r : Fin 7) : F := M r 1 * (M 1 1)⁻¹
  let α2 (r : Fin 7) : F := M r 2 * (M 2 2)⁻¹
  have hrow : ∀ (r j : Fin 7),
      M r j = α0 r * M 0 j + (α1 r * M 1 j + α2 r * M 2 j) := by
    intro r j
    let w (t : Fin 3) : F :=
      U r t - (α0 r * U 0 t + (α1 r * U 1 t + α2 r * U 2 t))
    -- Check `∑_t w t * M_factor = M r j - (α0 r * M 0 j + (α1 r * M 1 j + α2 r * M 2 j))`
    have hcomb : ∀ k : Fin 7,
        w 0 * V 0 k + (w 1 * V 1 k + w 2 * V 2 k) =
        M r k - (α0 r * M 0 k + (α1 r * M 1 k + α2 r * M 2 k)) := by
      intro k
      rw [hM r k, hM 0 k, hM 1 k, hM 2 k,
          finSum_three, finSum_three, finSum_three, finSum_three]
      dsimp [w]
      rw [sub_mul, sub_mul, sub_mul]
      rw [right_distrib, right_distrib, right_distrib, right_distrib, right_distrib, right_distrib]
      rw [mul_assoc (α0 r), mul_assoc (α1 r), mul_assoc (α2 r),
          mul_assoc (α0 r), mul_assoc (α1 r), mul_assoc (α2 r),
          mul_assoc (α0 r), mul_assoc (α1 r), mul_assoc (α2 r)]
      rw [left_distrib (α0 r), left_distrib (α0 r),
          left_distrib (α1 r), left_distrib (α1 r),
          left_distrib (α2 r), left_distrib (α2 r)]
      -- Group `(X0 - Y0) + ((X1 - Y1) + (X2 - Y2)) = (X0 + (X1 + X2)) - (Y0 + (Y1 + Y2))`
      have rearr_sub : ∀ X0 X1 X2 A0 A1 A2 B0 B1 B2 C0 C1 C2 : F,
          (X0 - (A0 + (B0 + C0))) + ((X1 - (A1 + (B1 + C1))) + (X2 - (A2 + (B2 + C2)))) =
          (X0 + (X1 + X2)) - ((A0 + (A1 + A2)) + ((B0 + (B1 + B2)) + (C0 + (C1 + C2)))) := by
        intro X0 X1 X2 A0 A1 A2 B0 B1 B2 C0 C1 C2
        have step2 : ∀ P0 Q0 P1 Q1 P2 Q2 : F,
            (P0 - Q0) + ((P1 - Q1) + (P2 - Q2)) = (P0 + (P1 + P2)) - (Q0 + (Q1 + Q2)) := by
          intro P0 Q0 P1 Q1 P2 Q2
          have pair : ∀ p q r s : F, (p - q) + (r - s) = (p + r) - (q + s) := by
            intro p q r s
            rw [sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg, neg_add]
            calc
              (p + -q) + (r + -s) = p + (-q + (r + -s)) := by rw [add_assoc]
              _ = p + ((r + -q) + -s) := by rw [← add_assoc (-q) r (-s), add_comm (-q) r]
              _ = (p + r) + (-q + -s) := by rw [add_assoc r (-q) (-s), ← add_assoc p r]
          rw [pair P1 Q1 P2 Q2, pair P0 Q0 (P1 + P2) (Q1 + Q2)]
        rw [step2]
        have sum9 : (A0 + (B0 + C0)) + ((A1 + (B1 + C1)) + (A2 + (B2 + C2))) =
            (A0 + (A1 + A2)) + ((B0 + (B1 + B2)) + (C0 + (C1 + C2))) := by
          have pair3 : ∀ a b c d e f : F, (a + (b + c)) + (d + (e + f)) = (a + d) + ((b + e) + (c + f)) := by
            intro a b c d e f
            calc
              (a + (b + c)) + (d + (e + f))
                  = a + ((b + c) + (d + (e + f))) := by rw [add_assoc]
              _ = a + (d + ((b + c) + (e + f))) := by
                    rw [← add_assoc (b + c) d, add_comm (b + c) d, add_assoc d]
              _ = (a + d) + ((b + c) + (e + f)) := by rw [← add_assoc a d]
              _ = (a + d) + (b + (c + (e + f))) := by rw [add_assoc b c]
              _ = (a + d) + (b + (e + (c + f))) := by rw [← add_assoc c e f, add_comm c e, add_assoc e]
              _ = (a + d) + ((b + e) + (c + f)) := by rw [← add_assoc b e]
          rw [pair3 A1 B1 C1 A2 B2 C2, pair3 A0 B0 C0 (A1 + A2) (B1 + B2) (C1 + C2)]
        rw [sum9]
      exact rearr_sub _ _ _ _ _ _ _ _ _ _ _ _
    have hk0 : w 0 * V 0 0 + (w 1 * V 1 0 + w 2 * V 2 0) = 0 := by
      rw [hcomb 0, zm 1 0 rfl, zm 2 0 rfl, mul_zero, mul_zero, add_zero, add_zero]
      dsimp [α0]
      rw [mul_assoc, inv_mul_cancel d0, mul_one, sub_self]
    have hk1 : w 0 * V 0 1 + (w 1 * V 1 1 + w 2 * V 2 1) = 0 := by
      rw [hcomb 1, zm 0 1 rfl, zm 2 1 rfl, mul_zero, mul_zero, zero_add, add_zero]
      dsimp [α1]
      rw [mul_assoc, inv_mul_cancel d1, mul_one, sub_self]
    have hk2 : w 0 * V 0 2 + (w 1 * V 1 2 + w 2 * V 2 2) = 0 := by
      rw [hcomb 2, zm 0 2 rfl, zm 1 2 rfl, mul_zero, mul_zero, zero_add, zero_add]
      dsimp [α2]
      rw [mul_assoc, inv_mul_cancel d2, mul_one, sub_self]
    rcases fano_factor_kernel_trivial hM hfit (w 0) (w 1) (w 2) hk0 hk1 hk2 with ⟨hw0, hw1, hw2⟩
    have hj := hcomb j
    rw [hw0, hw1, hw2, zero_mul, zero_mul, zero_mul, add_zero, add_zero] at hj
    exact (sub_eq_zero.mp hj.symm)
  -- Now deduce `u0 + u1 = 0`, `u0 + u2 = 0`, `u1 + u2 = 0` where `u_k = α_k 6 * M k 6 ≠ 0`!
  let u0 := α0 6 * M 0 6
  let u1 := α1 6 * M 1 6
  let u2 := α2 6 * M 2 6
  have hu0_nz : u0 ≠ 0 := mul_ne_zero (mul_ne_zero (nzm 6 0 rfl) (inv_ne_zero d0)) (nzm 0 6 rfl)
  -- Helper for each of rows `3, 4, 5`
  have pair_sum_zero :
      ∀ (a b : F) (pa pb m_ab0 m_ab1 m_a6 m_b6 : F),
        pb ≠ 0 → m_ab1 ≠ 0 →
        pa * m_ab0 + pb * m_ab1 = 0 →
        a * m_ab0 + b * m_ab1 = 0 →
        pa * m_a6 + pb * m_b6 = 0 →
        a * m_a6 + b * m_b6 = 0 := by
    intro a b pa pb m_ab0 m_ab1 m_a6 m_b6 hpb hm1 h1 h2 h3
    -- From `h1` and `h2`, `(pa * b - a * pb) * m_ab1 = 0` -> `pa * b = a * pb`!
    have hdet2 : pa * b = a * pb := by
      apply mul_right_cancel hm1
      have n1 : pa * m_ab0 = -(pb * m_ab1) := eq_neg_of_add_eq_zero h1
      have n2 : a * m_ab0 = -(b * m_ab1) := eq_neg_of_add_eq_zero h2
      calc
        (pa * b) * m_ab1 = pa * (b * m_ab1) := by rw [mul_assoc]
        _ = pa * (-(a * m_ab0)) := by rw [n2, neg_neg]
        _ = -(pa * (a * m_ab0)) := by rw [mul_neg]
        _ = -(a * (pa * m_ab0)) := by rw [← mul_assoc pa a, mul_comm pa a, mul_assoc]
        _ = -(a * (-(pb * m_ab1))) := by rw [n1]
        _ = (a * pb) * m_ab1 := by rw [mul_neg, neg_neg, mul_assoc]
    apply mul_left_cancel hpb
    rw [left_distrib, mul_zero]
    have s2 : pb * (b * m_b6) = b * (pb * m_b6) := by
      rw [← mul_assoc pb b, mul_comm pb b, mul_assoc]
    -- Wait: multiply by `pb`: `pb * (a * m_a6) + pb * (b * m_b6) = (a * pb) * m_a6 + pb * (b * m_b6)`
    -- `= (pa * b) * m_a6 + b * (pb * m_b6) = b * (pa * m_a6 + pb * m_b6) = 0`!
    calc
      pb * (a * m_a6) + pb * (b * m_b6)
          = (a * pb) * m_a6 + b * (pb * m_b6) := by
            rw [← mul_assoc pb a, mul_comm pb a, s2]
      _ = (pa * b) * m_a6 + b * (pb * m_b6) := by rw [hdet2]
      _ = b * (pa * m_a6) + b * (pb * m_b6) := by
            rw [mul_comm pa b, mul_assoc b pa]
      _ = b * (pa * m_a6 + pb * m_b6) := by rw [← left_distrib]
      _ = b * 0 := by rw [h3]
      _ = 0 := mul_zero b
  -- Row 3 vs Row 6 on cols `3` and `6` (`α2 3 = 0` since `M 3 2 = 0`, and `M 2 3 = 0`):
  have hα2_3 : α2 3 = 0 := by dsimp [α2]; rw [zm 3 2 rfl, zero_mul]
  have eq33 : α0 3 * M 0 3 + α1 3 * M 1 3 = 0 := by
    have h := (hrow 3 3).symm
    rw [zm 3 3 rfl, hα2_3, zero_mul, add_zero] at h; exact h
  have eq63 : α0 6 * M 0 3 + α1 6 * M 1 3 = 0 := by
    have h := (hrow 6 3).symm
    rw [zm 6 3 rfl, zm 2 3 rfl, mul_zero, add_zero] at h; exact h
  have eq36 : α0 3 * M 0 6 + α1 3 * M 1 6 = 0 := by
    have h := (hrow 3 6).symm
    rw [zm 3 6 rfl, hα2_3, zero_mul, add_zero] at h; exact h
  have hu01 : u0 + u1 = 0 :=
    pair_sum_zero (α0 6) (α1 6) (α0 3) (α1 3) (M 0 3) (M 1 3) (M 0 6) (M 1 6)
      (mul_ne_zero (nzm 3 1 rfl) (inv_ne_zero d1)) (nzm 1 3 rfl) eq33 eq63 eq36
  -- Row 4 vs Row 6 on cols `4` and `6` (`α1 4 = 0` since `M 4 1 = 0`, and `M 1 4 = 0`):
  have hα1_4 : α1 4 = 0 := by dsimp [α1]; rw [zm 4 1 rfl, zero_mul]
  have eq44 : α0 4 * M 0 4 + α2 4 * M 2 4 = 0 := by
    have h := (hrow 4 4).symm
    rw [zm 4 4 rfl, hα1_4, zero_mul, zero_add] at h; exact h
  have eq64 : α0 6 * M 0 4 + α2 6 * M 2 4 = 0 := by
    have h := (hrow 6 4).symm
    rw [zm 6 4 rfl, zm 1 4 rfl, mul_zero, zero_add] at h; exact h
  have eq46 : α0 4 * M 0 6 + α2 4 * M 2 6 = 0 := by
    have h := (hrow 4 6).symm
    rw [zm 4 6 rfl, hα1_4, zero_mul, zero_add] at h; exact h
  have hu02 : u0 + u2 = 0 :=
    pair_sum_zero (α0 6) (α2 6) (α0 4) (α2 4) (M 0 4) (M 2 4) (M 0 6) (M 2 6)
      (mul_ne_zero (nzm 4 2 rfl) (inv_ne_zero d2)) (nzm 2 4 rfl) eq44 eq64 eq46
  -- Row 5 vs Row 6 on cols `5` and `6` (`α0 5 = 0` since `M 5 0 = 0`, and `M 0 5 = 0`):
  have hα0_5 : α0 5 = 0 := by dsimp [α0]; rw [zm 5 0 rfl, zero_mul]
  have eq55 : α1 5 * M 1 5 + α2 5 * M 2 5 = 0 := by
    have h := (hrow 5 5).symm
    rw [zm 5 5 rfl, hα0_5, zero_mul, zero_add] at h; exact h
  have eq65 : α1 6 * M 1 5 + α2 6 * M 2 5 = 0 := by
    have h := (hrow 6 5).symm
    rw [zm 6 5 rfl, zm 0 5 rfl, mul_zero, zero_add] at h; exact h
  have eq56 : α1 5 * M 1 6 + α2 5 * M 2 6 = 0 := by
    have h := (hrow 5 6).symm
    rw [zm 5 6 rfl, hα0_5, zero_mul, zero_add] at h; exact h
  have hu12 : u1 + u2 = 0 :=
    pair_sum_zero (α1 6) (α2 6) (α1 5) (α2 5) (M 1 5) (M 2 5) (M 1 6) (M 2 6)
      (mul_ne_zero (nzm 5 2 rfl) (inv_ne_zero d2)) (nzm 2 5 rfl) eq55 eq65 eq56
  -- Combine `u0 + u1 = 0`, `u0 + u2 = 0`, `u1 + u2 = 0` -> `((1 + 1) * u0) = 0`!
  have h2u0 : ((1 : F) + 1) * u0 = 0 := by
    have nu1 : u1 = -u0 := by rw [add_comm] at hu01; exact eq_neg_of_add_eq_zero hu01
    have nu2 : u2 = -u0 := by rw [add_comm] at hu02; exact eq_neg_of_add_eq_zero hu02
    rw [nu1, nu2] at hu12
    calc
      ((1 : F) + 1) * u0 = u0 + u0 := by rw [right_distrib, one_mul]
      _ = -((-u0) + (-u0)) := by rw [neg_add, neg_neg]
      _ = -(0 : F) := by rw [hu12]
      _ = 0 := neg_zero
  cases mul_eq_zero h2u0 with
  | inl hc => exact hchar hc
  | inr hu => exact hu0_nz hu

/-- Over EVERY field `F` of characteristic `≠ 2` (`1 + 1 ≠ 0`, including `𝔽₃, ℚ, ℝ, ℂ`),
`Z_Fano` has exact minimum rank `4`! -/
theorem fano_znz_minRank_char_ne_two {F : Type u} [FieldR F] (hchar : (1 : F) + 1 ≠ 0) :
    IsZNZMinRank F Z_Fano 4 := by
  constructor
  · -- Universal `{0, 1, -1}`-valued rank-4 matrix `MZ = P * P^T - 2 * w * w^T`!
    let w (i : Fin 7) : F :=
      match i.val with
      | 0 | 1 | 2 => 0
      | _ => 1
    let two : F := (1 : F) + 1
    let U : Mat F 7 4 := fun i t =>
      match t.val with
      | 0 => match fanoVec i 0 with | 1 => 1 | _ => 0
      | 1 => match fanoVec i 1 with | 1 => 1 | _ => 0
      | 2 => match fanoVec i 2 with | 1 => 1 | _ => 0
      | _ => w i
    let V : Mat F 4 7 := fun t j =>
      match t.val with
      | 0 => match fanoVec j 0 with | 1 => 1 | _ => 0
      | 1 => match fanoVec j 1 with | 1 => 1 | _ => 0
      | 2 => match fanoVec j 2 with | 1 => 1 | _ => 0
      | _ => -(two * w j)
    let M : Mat F 7 7 := fun i j => finSum (fun t : Fin 4 => U i t * V t j)
    refine ⟨M, ?_, ⟨U, V, fun _ _ => rfl⟩⟩
    have c1 : (1 : F) + -two = -1 := by
      dsimp [two]
      rw [neg_add, ← add_assoc (1 : F) (-1) (-1), add_neg_cancel, zero_add]
    have h1neg1 : (1 : F) + -1 = 0 := add_neg_cancel 1
    refine fin7_cases ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> refine fin7_cases ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      (dsimp [M]; rw [finSum_four]; dsimp [U, V, w, fanoVec, Z_Fano];
       simp only [one_mul, mul_one, zero_mul, mul_zero, neg_zero, zero_add, add_zero, c1, h1neg1];
       first
         | exact ⟨fun _ => trivial, fun _ => one_ne_zero⟩
         | exact ⟨fun _ => trivial, fun _ => neg_one_ne_zero⟩
         | exact ⟨fun h => False.elim (h trivial), fun h => by contradiction⟩)
  · intro r' hr' M hfit hrk
    have hle3 : r' ≤ 3 := by omega
    exact fano_not_rank_le_three_char_ne_two hchar M hfit (HasRankAtMost.mono hle3 hrk)

/-! ### Pillar 4: Haemers Minrank Cycle-Parity Reversal (`minrank_F(C₆) = 3 > 2 = minrank_F(C₆^c)`) -/

/-- `M` fits `G` in Haemers' orthogonal-representation / index-coding sense:
`M i i = 1` for all `i`, and `M i j = 0` whenever `i ≠ j` and `i j ∉ E(G)`. -/
def FitsHaemers (F : Type u) [CommRingR F] {n : Nat} (G : SimpleGraph n) (M : Mat F n n) : Prop :=
  (∀ i : Fin n, M i i = 1) ∧ (∀ i j : Fin n, i ≠ j → G.adj i j = false → M i j = 0)

def IsHaemersMinRank (F : Type u) [CommRingR F] {n : Nat} (G : SimpleGraph n) (r : Nat) : Prop :=
  (∃ M : Mat F n n, FitsHaemers F G M ∧ HasRankAtMost F r M) ∧
  (∀ r' : Nat, r' < r → ∀ M : Mat F n n, FitsHaemers F G M → ¬ HasRankAtMost F r' M)

/-- The even `6`-cycle `C₆` (bipartite, zero odd cycles). -/
def G_C6 : SimpleGraph 6 where
  adj i j := ((i.val + 1) % 6 == j.val) || ((j.val + 1) % 6 == i.val)
  loopless := by decide
  symm := by decide

/-- The complement `C₆^c` (`3`-prism, containing two odd `3`-cycles `{0,2,4}` and `{1,3,5}`). -/
def G_C6_compl : SimpleGraph 6 where
  adj i j := i != j && !(((i.val + 1) % 6 == j.val) || ((j.val + 1) % 6 == i.val))
  loopless := by decide
  symm := by decide

/-- Over EVERY field `F`, bipartite `C₆` (zero odd cycles) has Haemers minrank `3`, whereas
non-bipartite `C₆^c` (containing odd `C₃` cycles) has Haemers minrank `2 < 3`! -/
theorem haemers_C6_vs_complement (F : Type u) [FieldR F] :
    IsHaemersMinRank F G_C6 3 ∧ IsHaemersMinRank F G_C6_compl 2 := by
  constructor
  · -- `minrank_F(C₆) = 3`: clique cover `{0,1}, {2,3}, {4,5}` gives `≤ 3`, independent set `{0,2,4}` gives `≥ 3`!
    constructor
    · let U : Mat F 6 3 := fun i t =>
        match i.val / 2, t.val with
        | 0, 0 => 1 | 1, 1 => 1 | 2, 2 => 1 | _, _ => 0
      let UT : Mat F 3 6 := fun t j => U j t
      let M : Mat F 6 6 := fun i j => finSum (fun t : Fin 3 => U i t * UT t j)
      refine ⟨M, ⟨?_, ?_⟩, ⟨U, UT, fun _ _ => rfl⟩⟩
      · refine fin6_cases ?_ ?_ ?_ ?_ ?_ ?_ <;>
          (dsimp [M, UT]; rw [finSum_three]; dsimp [U];
           simp only [one_mul, zero_mul, add_zero, zero_add])
      · refine fin6_cases ?_ ?_ ?_ ?_ ?_ ?_ <;> refine fin6_cases ?_ ?_ ?_ ?_ ?_ ?_ <;>
          intro hij hnon <;> first
            | exact absurd rfl hij
            | contradiction
            | (dsimp [M, UT]; rw [finSum_three]; dsimp [U];
               simp only [one_mul, zero_mul, mul_zero, add_zero, zero_add])
    · intro r' hr' M ⟨hdiag, hzero⟩ hrk
      have hle2 : r' ≤ 2 := by omega
      have hrk2 : HasRankAtMost F 2 M := HasRankAtMost.mono hle2 hrk
      have hdet := subDet3_eq_zero_of_rank_le_two hrk2 0 2 4 0 2 4
      unfold subDet3 at hdet
      rw [hdiag 0, hdiag 2, hdiag 4,
          hzero 0 2 (by decide) rfl, hzero 0 4 (by decide) rfl,
          hzero 2 4 (by decide) rfl, hzero 4 2 (by decide) rfl,
          mul_zero, sub_zero, mul_one, mul_one, zero_mul, sub_zero, zero_mul, add_zero] at hdet
      exact one_ne_zero hdet
  · -- `minrank_F(C₆^c) = 2`: clique cover `{0,2,4}, {1,3,5}` gives `≤ 2`, non-edge `{0,1}` gives `≥ 2`!
    constructor
    · let U : Mat F 6 2 := fun i t =>
        match i.val % 2, t.val with
        | 0, 0 => 1 | 1, 1 => 1 | _, _ => 0
      let UT : Mat F 2 6 := fun t j => U j t
      let M : Mat F 6 6 := fun i j => finSum (fun t : Fin 2 => U i t * UT t j)
      refine ⟨M, ⟨?_, ?_⟩, ⟨U, UT, fun _ _ => rfl⟩⟩
      · refine fin6_cases ?_ ?_ ?_ ?_ ?_ ?_ <;>
          (dsimp [M, UT]; rw [finSum_two]; dsimp [U];
           simp only [one_mul, zero_mul, add_zero, zero_add])
      · refine fin6_cases ?_ ?_ ?_ ?_ ?_ ?_ <;> refine fin6_cases ?_ ?_ ?_ ?_ ?_ ?_ <;>
          intro hij hnon <;> first
            | exact absurd rfl hij
            | contradiction
            | (dsimp [M, UT]; rw [finSum_two]; dsimp [U];
               simp only [one_mul, zero_mul, mul_zero, add_zero, zero_add])
    · intro r' hr' M ⟨hdiag, hzero⟩ hrk
      have hcases : r' = 0 ∨ r' = 1 := by omega
      cases hcases with
      | inl h0 =>
        subst h0
        have hne : M 0 0 ≠ 0 := by rw [hdiag 0]; exact one_ne_zero
        exact not_hasRankAtMost_zero_of_entry_ne_zero 0 0 hne hrk
      | inr h1 =>
        subst h1
        have hmin := minor2_eq_of_rank_le_one hrk 0 1 0 1
        rw [hdiag 0, hdiag 1, hzero 0 1 (by decide) rfl, mul_one, zero_mul] at hmin
        exact one_ne_zero hmin

end Conjecture00000007178
