/-
  Conjecture 00000007178 — Pillar 2: Symmetric Partial Matrices on Undirected Graphs
  Covers BOTH fixed-diagonal (Gram / correlation) and free-diagonal partial matrices:
  1. Variant 2A (Unit/Nonzero Diagonal Specified — Chordality vs. Cycle Parity):
     - Positive Simplicial-Vertex Chordal Extension Theorem: adding a simplicial vertex
       preserves symmetric and general rank-`1` completability when the new clique block
       has rank `≤ 1` (so odd `3`-cycles `C₃` and chordal graphs NEVER obstruct!).
     - Even `4`-cycle `C₄` separation: `S_C4_plus` vs `S_C4_minus` have all clique
       principal submatrices symmetric of rank `1`, yet `mr(S_C4_plus) = smr(S_C4_plus) = 1`
       whereas `mr(S_C4_minus) = 2` and `smr(S_C4_minus) = 3`!
     - Both odd `5`-cycle `C₅` AND even `6`-cycle `C₆` satisfy `LocallyRankAtMost F 1`
       across ALL submatrices (principal and non-principal), yet fail rank-`1` completion:
       chordality (`length ≥ 4`), NOT cycle parity, is the boundary!
  2. Variant 2B (Free/Unspecified Diagonal — Single-Cycle Trap vs. Global Refutation):
     - Positive Single-Odd-Cycle Theorem: on `C₃` with free diagonal, EVERY everywhere-nonzero
       symmetric edge assignment has `smr = mr = 1` over EVERY field!
     - Double Refutation:
       (a) Even cycle `C₄` with free diagonal has `mr = smr = 1` for `a⁺` vs `2` for `a⁻`;
       (b) Butterfly graph `B₂` (two odd `C₃` triangles sharing one vertex — EVERY simple
           cycle is odd, ZERO even cycles!) with free diagonal ALSO has `mr = smr = 1`
           for `a⁺` vs `mr = smr = 2` for `a⁻`!
-/

import Conjecture00000007178.BipartiteCompletion

namespace Conjecture00000007178

universe u

open CommRingR FieldR

/-! ### Variant 2A: Fixed Nonzero Diagonal — Chordal Simplicial Extension vs. `C₄, C₅, C₆` -/

/-- Positive Chordal Simplicial-Vertex Extension Theorem:
Let `P` be a symmetric partial `(n + 1) × (n + 1)` matrix with nonzero diagonal where the last
vertex `last = n` is simplicial with clique neighborhood `K : Fin n → Bool`.
If `P` restricted to the first `n` vertices admits a symmetric outer-product completion
`M₀ i j = c * x i * x j` (`c ≠ 0`), and the clique compatibility conditions hold at `last`,
then `P` admits a global rank-`1` symmetric completion over `F`. -/
theorem chordal_simplicial_sym_rank_one_step {F : Type u} [FieldR F] {n : Nat}
    (P : PartialMatrix F (n + 1) (n + 1))
    (K : Fin n → Bool)
    (i_piv : Fin n) (hpiv : K i_piv = true)
    (hlast_spec : ∀ i : Fin n,
      P.spec ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ ⟨n, Nat.lt_succ_self n⟩ = K i ∧
      P.spec ⟨n, Nat.lt_succ_self n⟩ ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ = K i)
    (hsym_last : ∀ i : Fin n, K i = true →
      P.val ⟨n, Nat.lt_succ_self n⟩ ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ =
      P.val ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ ⟨n, Nat.lt_succ_self n⟩)
    (c : F) (hc : c ≠ 0) (x : Fin n → F) (hx_piv : x i_piv ≠ 0)
    (hbase : ∀ i j : Fin n,
      P.spec ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ = true →
      (c * x i) * x j = P.val ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩)
    (hK_spec_piv : ∀ i : Fin n, K i = true →
      P.spec ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ ⟨i_piv.val, Nat.lt_succ_of_lt i_piv.isLt⟩ = true)
    (hclique_minor : ∀ i : Fin n, K i = true →
      P.val ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ ⟨i_piv.val, Nat.lt_succ_of_lt i_piv.isLt⟩ *
        P.val ⟨i_piv.val, Nat.lt_succ_of_lt i_piv.isLt⟩ ⟨n, Nat.lt_succ_self n⟩ =
      P.val ⟨i_piv.val, Nat.lt_succ_of_lt i_piv.isLt⟩ ⟨i_piv.val, Nat.lt_succ_of_lt i_piv.isLt⟩ *
        P.val ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ ⟨n, Nat.lt_succ_self n⟩)
    (hdiag_last : P.spec ⟨n, Nat.lt_succ_self n⟩ ⟨n, Nat.lt_succ_self n⟩ = true →
      P.val ⟨i_piv.val, Nat.lt_succ_of_lt i_piv.isLt⟩ ⟨n, Nat.lt_succ_self n⟩ *
        P.val ⟨i_piv.val, Nat.lt_succ_of_lt i_piv.isLt⟩ ⟨n, Nat.lt_succ_self n⟩ =
      P.val ⟨i_piv.val, Nat.lt_succ_of_lt i_piv.isLt⟩ ⟨i_piv.val, Nat.lt_succ_of_lt i_piv.isLt⟩ *
        P.val ⟨n, Nat.lt_succ_self n⟩ ⟨n, Nat.lt_succ_self n⟩) :
    ∃ x' : Fin (n + 1) → F,
      (∀ a b : Fin (n + 1), P.spec a b = true → (c * x' a) * x' b = P.val a b) ∧
      IsSymmetric (fun a b => (c * x' a) * x' b) ∧
      HasRankAtMost F 1 (fun a b => (c * x' a) * x' b) := by
  let piv' : Fin (n + 1) := ⟨i_piv.val, Nat.lt_succ_of_lt i_piv.isLt⟩
  let last' : Fin (n + 1) := ⟨n, Nat.lt_succ_self n⟩
  let x_last : F := (c * x i_piv)⁻¹ * P.val piv' last'
  let x' : Fin (n + 1) → F := fun a =>
    if ha : a.val < n then x ⟨a.val, ha⟩ else x_last
  have hcx_piv_ne : c * x i_piv ≠ 0 := mul_ne_zero hc hx_piv
  have hdiag_piv : (c * x i_piv) * x i_piv = P.val piv' piv' :=
    hbase i_piv i_piv (hK_spec_piv i_piv hpiv)
  have hdp_ne : P.val piv' piv' ≠ 0 := by
    rw [← hdiag_piv]
    exact mul_ne_zero hcx_piv_ne hx_piv
  refine ⟨x', ?_, ?_, ?_⟩
  · intro a b hs
    by_cases ha : a.val < n
    · by_cases hb : b.val < n
      · simp only [x', ha, hb, ↓reduceDIte]
        exact hbase ⟨a.val, ha⟩ ⟨b.val, hb⟩ hs
      · have hb_eq : b = last' := by
          apply Fin.ext
          dsimp [last']
          omega
        subst hb_eq
        have hKi : K ⟨a.val, ha⟩ = true := by
          rw [← (hlast_spec ⟨a.val, ha⟩).1]
          exact hs
        simp only [x', last', ha, Nat.lt_irrefl n, ↓reduceDIte]
        apply mul_left_cancel hdp_ne
        have hrel := hclique_minor ⟨a.val, ha⟩ hKi
        have ha_piv := hbase ⟨a.val, ha⟩ i_piv (hK_spec_piv ⟨a.val, ha⟩ hKi)
        calc
          P.val piv' piv' * ((c * x ⟨a.val, ha⟩) * x_last)
              = ((c * x i_piv) * x i_piv) * ((c * x ⟨a.val, ha⟩) * ((c * x i_piv)⁻¹ * P.val piv' last')) := by
                rw [← hdiag_piv]
          _ = ((c * x ⟨a.val, ha⟩) * x i_piv) * (((c * x i_piv) * (c * x i_piv)⁻¹) * P.val piv' last') := by
                let A := c * x i_piv
                let B := x i_piv
                let C := c * x ⟨a.val, ha⟩
                let D := (c * x i_piv)⁻¹
                let E := P.val piv' last'
                show (A * B) * (C * (D * E)) = (C * B) * ((A * D) * E)
                calc
                  (A * B) * (C * (D * E)) = A * (B * (C * (D * E))) := by rw [mul_assoc]
                  _ = A * ((B * C) * (D * E)) := by rw [← mul_assoc B C (D * E)]
                  _ = A * ((C * B) * (D * E)) := by rw [mul_comm B C]
                  _ = (A * (C * B)) * (D * E) := by rw [← mul_assoc A (C * B) (D * E)]
                  _ = ((C * B) * A) * (D * E) := by rw [mul_comm A (C * B)]
                  _ = (C * B) * (A * (D * E)) := by rw [mul_assoc (C * B) A (D * E)]
                  _ = (C * B) * ((A * D) * E) := by rw [← mul_assoc A D E]
          _ = P.val ⟨a.val, Nat.lt_succ_of_lt ha⟩ piv' * ((1 : F) * P.val piv' last') := by
                rw [ha_piv, FieldR.mul_inv_cancel (c * x i_piv) hcx_piv_ne]
          _ = P.val ⟨a.val, Nat.lt_succ_of_lt ha⟩ piv' * P.val piv' last' := by rw [one_mul]
          _ = P.val piv' piv' * P.val ⟨a.val, Nat.lt_succ_of_lt ha⟩ last' := hrel
    · have ha_eq : a = last' := by
        apply Fin.ext
        dsimp [last']
        omega
      subst ha_eq
      by_cases hb : b.val < n
      · have hKb : K ⟨b.val, hb⟩ = true := by
          rw [← (hlast_spec ⟨b.val, hb⟩).2]
          exact hs
        simp only [x', last', hb, Nat.lt_irrefl n, ↓reduceDIte]
        rw [hsym_last ⟨b.val, hb⟩ hKb]
        have hcomm_xb : (c * x_last) * x ⟨b.val, hb⟩ = (c * x ⟨b.val, hb⟩) * x_last := by
          rw [mul_assoc, mul_comm x_last, ← mul_assoc]
        rw [hcomm_xb]
        apply mul_left_cancel hdp_ne
        have hrel := hclique_minor ⟨b.val, hb⟩ hKb
        have hb_piv := hbase ⟨b.val, hb⟩ i_piv (hK_spec_piv ⟨b.val, hb⟩ hKb)
        calc
          P.val piv' piv' * ((c * x ⟨b.val, hb⟩) * x_last)
              = ((c * x i_piv) * x i_piv) * ((c * x ⟨b.val, hb⟩) * ((c * x i_piv)⁻¹ * P.val piv' last')) := by
                rw [← hdiag_piv]
          _ = ((c * x ⟨b.val, hb⟩) * x i_piv) * (((c * x i_piv) * (c * x i_piv)⁻¹) * P.val piv' last') := by
                let A := c * x i_piv
                let B := x i_piv
                let C := c * x ⟨b.val, hb⟩
                let D := (c * x i_piv)⁻¹
                let E := P.val piv' last'
                show (A * B) * (C * (D * E)) = (C * B) * ((A * D) * E)
                calc
                  (A * B) * (C * (D * E)) = A * (B * (C * (D * E))) := by rw [mul_assoc]
                  _ = A * ((B * C) * (D * E)) := by rw [← mul_assoc B C (D * E)]
                  _ = A * ((C * B) * (D * E)) := by rw [mul_comm B C]
                  _ = (A * (C * B)) * (D * E) := by rw [← mul_assoc A (C * B) (D * E)]
                  _ = ((C * B) * A) * (D * E) := by rw [mul_comm A (C * B)]
                  _ = (C * B) * (A * (D * E)) := by rw [mul_assoc (C * B) A (D * E)]
                  _ = (C * B) * ((A * D) * E) := by rw [← mul_assoc A D E]
          _ = P.val ⟨b.val, Nat.lt_succ_of_lt hb⟩ piv' * ((1 : F) * P.val piv' last') := by
                rw [hb_piv, FieldR.mul_inv_cancel (c * x i_piv) hcx_piv_ne]
          _ = P.val ⟨b.val, Nat.lt_succ_of_lt hb⟩ piv' * P.val piv' last' := by rw [one_mul]
          _ = P.val piv' piv' * P.val ⟨b.val, Nat.lt_succ_of_lt hb⟩ last' := hrel
      · have hb_eq : b = last' := by
          apply Fin.ext
          dsimp [last']
          omega
        subst hb_eq
        simp only [x', last', Nat.lt_irrefl n, ↓reduceDIte]
        apply mul_left_cancel hdp_ne
        have hdlast := hdiag_last hs
        calc
          P.val piv' piv' * ((c * x_last) * x_last)
              = ((c * x i_piv) * x i_piv) * ((c * ((c * x i_piv)⁻¹ * P.val piv' last')) * ((c * x i_piv)⁻¹ * P.val piv' last')) := by
                rw [← hdiag_piv]
          _ = ((c * x i_piv) * (c * x i_piv)⁻¹) * ((c * x i_piv) * (c * x i_piv)⁻¹) * (P.val piv' last' * P.val piv' last') := by
                let X := x i_piv
                let I := (c * x i_piv)⁻¹
                let V := P.val piv' last'
                have hPQR : ∀ A B C : F, A * (B * C) = B * (A * C) :=
                  fun A B C => by rw [← mul_assoc A B C, mul_comm A B, mul_assoc B A C]
                show ((c * X) * X) * ((c * (I * V)) * (I * V)) = ((c * X) * I) * ((c * X) * I) * (V * V)
                calc
                  ((c * X) * X) * ((c * (I * V)) * (I * V))
                      = (c * X) * (X * ((c * (I * V)) * (I * V))) := by rw [mul_assoc]
                  _ = (c * X) * ((X * (c * (I * V))) * (I * V)) := by rw [← mul_assoc X]
                  _ = (c * X) * (((X * c) * (I * V)) * (I * V)) := by rw [← mul_assoc X c]
                  _ = (c * X) * (((c * X) * (I * V)) * (I * V)) := by rw [mul_comm X c]
                  _ = ((c * X) * (I * V)) * ((c * X) * (I * V)) := hPQR (c * X) ((c * X) * (I * V)) (I * V)
                  _ = (((c * X) * I) * V) * (((c * X) * I) * V) := by rw [← mul_assoc (c * X) I V]
                  _ = ((c * X) * I) * (V * (((c * X) * I) * V)) := by rw [mul_assoc ((c * X) * I)]
                  _ = ((c * X) * I) * ((V * ((c * X) * I)) * V) := by rw [← mul_assoc V]
                  _ = ((c * X) * I) * ((((c * X) * I) * V) * V) := by rw [mul_comm V ((c * X) * I)]
                  _ = (((c * X) * I) * ((c * X) * I)) * (V * V) := by
                        rw [mul_assoc (((c * X) * I)) V V, ← mul_assoc ((c * X) * I) ((c * X) * I) (V * V)]
          _ = (1 : F) * 1 * (P.val piv' last' * P.val piv' last') := by
                rw [FieldR.mul_inv_cancel (c * x i_piv) hcx_piv_ne]
          _ = P.val piv' last' * P.val piv' last' := by rw [one_mul, one_mul]
          _ = P.val piv' piv' * P.val last' last' := hdlast
  · intro a b
    dsimp only
    rw [mul_assoc, mul_comm (x' a) (x' b), ← mul_assoc]
  · exact (hasRankAtMost_one_iff_outer _).mpr ⟨fun a => c * x' a, x', fun _ _ => rfl⟩

/-! ### Even `4`-Cycle `C₄` with Unit Diagonal: `mr = 1` vs `mr = 2` and `smr = 3` -/

def spec_C4_diag (i j : Fin 4) : Bool :=
  !(i == 0 && j == 2) && !(i == 2 && j == 0) &&
  !(i == 1 && j == 3) && !(i == 3 && j == 1)

def S_C4_plus (F : Type u) [FieldR F] : PartialMatrix F 4 4 where
  spec := spec_C4_diag
  val  := fun _ _ => 1

def S_C4_minus (F : Type u) [FieldR F] : PartialMatrix F 4 4 where
  spec := spec_C4_diag
  val  := fun i j =>
    match i.val, j.val with
    | 0, 3 => -1
    | 3, 0 => -1
    | _, _ => 1

/-- Every `2 × 2` principal edge submatrix (every maximal clique of `C₄`) in `S_{C₄}⁻`
is symmetric and has rank `1`. -/
theorem S_C4_minus_all_edge_cliques_rank_one (F : Type u) [FieldR F]
    (i₀ i₁ : Fin 4) :
    let B : Mat F 2 2 := PartialMatrix.submatrix (S_C4_minus F).val
      (fun t => match t.val with | 0 => i₀ | _ => i₁)
      (fun t => match t.val with | 0 => i₀ | _ => i₁)
    IsSymmetric B ∧ HasRankAtMost F 1 B := by
  intro B
  have hsym_all : ∀ a b : Fin 4, (S_C4_minus F).val b a = (S_C4_minus F).val a b := by
    refine fin4_cases ?_ ?_ ?_ ?_ <;> refine fin4_cases ?_ ?_ ?_ ?_ <;> rfl
  have hdiag_all : ∀ a : Fin 4, (S_C4_minus F).val a a = 1 := by
    refine fin4_cases ?_ ?_ ?_ ?_ <;> rfl
  have hsq_all : ∀ a b : Fin 4, (S_C4_minus F).val a b * (S_C4_minus F).val a b = 1 := by
    refine fin4_cases ?_ ?_ ?_ ?_ <;> refine fin4_cases ?_ ?_ ?_ ?_ <;>
      (dsimp [S_C4_minus]; simp only [neg_mul_neg, mul_one])
  have hsym01 : (S_C4_minus F).val i₁ i₀ = (S_C4_minus F).val i₀ i₁ := hsym_all i₀ i₁
  have hdiag0 : (S_C4_minus F).val i₀ i₀ = 1 := hdiag_all i₀
  have hdiag1 : (S_C4_minus F).val i₁ i₁ = 1 := hdiag_all i₁
  constructor
  · refine fin2_cases ?_ ?_ <;> refine fin2_cases ?_ ?_ <;>
      dsimp [B, PartialMatrix.submatrix]
    · exact hsym01.symm
    · exact hsym01
  · rw [hasRankAtMost_one_iff_outer]
    let s : F := (S_C4_minus F).val i₀ i₁
    let u : Fin 2 → F := fun t => match t.val with | 0 => 1 | _ => s
    refine ⟨u, u, ?_⟩
    have hsq : s * s = 1 := hsq_all i₀ i₁
    refine fin2_cases ?_ ?_ <;> refine fin2_cases ?_ ?_ <;>
      dsimp [B, PartialMatrix.submatrix, u]
    · rw [mul_one, hdiag0]
    · rw [one_mul]
    · rw [mul_one, hsym01]
    · rw [hsq, hdiag1]

theorem S_C4_plus_minRank_one (F : Type u) [FieldR F] :
    IsMinCompletionRank F (S_C4_plus F) 1 ∧ IsMinSymCompletionRank F (S_C4_plus F) 1 := by
  have hrk1 : HasRankAtMost F 1 (fun (_ _ : Fin 4) => (1 : F)) :=
    (hasRankAtMost_one_iff_outer _).mpr ⟨fun _ => 1, fun _ => 1, fun _ _ => (mul_one 1).symm⟩
  constructor
  · refine ⟨⟨fun _ _ => 1, fun _ _ _ => rfl, hrk1⟩, ?_⟩
    intro r' hr' M hcomp
    have hr0 : r' = 0 := by omega
    subst hr0
    have hne : M 0 0 ≠ 0 := by rw [hcomp 0 0 rfl]; exact one_ne_zero
    exact not_hasRankAtMost_zero_of_entry_ne_zero 0 0 hne
  · refine ⟨⟨fun _ _ => 1, ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩, hrk1⟩, ?_⟩
    intro r' hr' M hcomp
    have hr0 : r' = 0 := by omega
    subst hr0
    have hne : M 0 0 ≠ 0 := by rw [hcomp.2 0 0 rfl]; exact one_ne_zero
    exact not_hasRankAtMost_zero_of_entry_ne_zero 0 0 hne

theorem S_C4_minus_not_rank_one {F : Type u} [FieldR F] (hchar : (1 : F) + 1 ≠ 0)
    (M : Mat F 4 4) (hcomp : (S_C4_minus F).IsCompletion M) :
    ¬ HasRankAtMost F 1 M := by
  intro hrk
  have hcyc := directed_cycle_diag_product_eq (k := 3) hrk (fun t => t)
  have hL : finProd (fun t : Fin 4 => M t (nextIdx t)) =
      M 0 1 * (M 1 2 * (M 2 3 * (M 3 0 * 1))) := rfl
  have hR : finProd (fun t : Fin 4 => M t t) =
      M 0 0 * (M 1 1 * (M 2 2 * (M 3 3 * 1))) := rfl
  rw [hL, hR] at hcyc
  rw [hcomp 0 1 rfl, hcomp 1 2 rfl, hcomp 2 3 rfl, hcomp 3 0 rfl,
      hcomp 0 0 rfl, hcomp 1 1 rfl, hcomp 2 2 rfl, hcomp 3 3 rfl] at hcyc
  dsimp [S_C4_minus] at hcyc
  simp only [mul_one, one_mul] at hcyc
  exact neg_one_ne_one hchar hcyc

/-- Exact asymmetric minimum completion rank of `S_{C₄}⁻` is `2`. -/
theorem S_C4_minus_minRank_two {F : Type u} [FieldR F] (hchar : (1 : F) + 1 ≠ 0) :
    IsMinCompletionRank F (S_C4_minus F) 2 := by
  constructor
  · let U : Mat F 4 2 := fun i t =>
      match i.val, t.val with
      | 0, 0 => 1
      | 1, 1 => 1
      | 2, 1 => 1
      | 3, 0 => -1
      | _, _ => 0
    let V : Mat F 2 4 := fun t j =>
      match t.val, j.val with
      | 0, 0 => 1
      | 0, 1 => 1
      | 0, 2 => -1
      | 0, 3 => -1
      | _, _ => 1
    let M : Mat F 4 4 := fun i j => finSum (fun t : Fin 2 => U i t * V t j)
    refine ⟨M, ?_, ⟨U, V, fun _ _ => rfl⟩⟩
    refine fin4_cases ?_ ?_ ?_ ?_ <;> refine fin4_cases ?_ ?_ ?_ ?_ <;> intro hs <;> first
      | contradiction
      | (dsimp [M]; rw [finSum_two]; dsimp [U, V, S_C4_minus];
         simp only [one_mul, mul_one, zero_mul, mul_zero, neg_one_mul, neg_mul_neg, add_zero, zero_add, neg_neg])
  · intro r' hr' M hcomp
    have hcases : r' = 0 ∨ r' = 1 := by omega
    cases hcases with
    | inl h0 =>
      subst h0
      have hne : M 0 0 ≠ 0 := by rw [hcomp 0 0 rfl]; exact one_ne_zero
      exact not_hasRankAtMost_zero_of_entry_ne_zero 0 0 hne
    | inr h1 =>
      subst h1
      exact S_C4_minus_not_rank_one hchar M hcomp

/-- No SYMMETRIC completion of `S_{C₄}⁻` has rank `≤ 2` when `char(F) ≠ 2`. -/
theorem S_C4_minus_no_sym_rank_two {F : Type u} [FieldR F] (hchar : (1 : F) + 1 ≠ 0)
    (M : Mat F 4 4) (hsym : (S_C4_minus F).IsSymCompletion M) :
    ¬ HasRankAtMost F 2 M := by
  intro hrk2
  rcases hsym with ⟨hMsym, hcomp⟩
  let x := M 0 2
  let y := M 1 3
  have hx_sym : M 2 0 = x := hMsym 2 0
  have hy_sym : M 3 1 = y := hMsym 3 1
  have hdet023 := subDet3_eq_zero_of_rank_le_two hrk2 0 2 3 0 2 3
  unfold subDet3 at hdet023
  rw [hcomp 0 0 rfl, hcomp 0 3 rfl, hx_sym, hcomp 2 2 rfl, hcomp 2 3 rfl,
      hcomp 3 0 rfl, hcomp 3 2 rfl, hcomp 3 3 rfl] at hdet023
  dsimp [S_C4_minus] at hdet023
  have hsq_x : (x + 1) * (x + 1) = 0 := by
    rw [mul_one, sub_self, mul_zero, zero_sub, mul_one, mul_neg, mul_one,
        sub_eq_add_neg x (-1), neg_neg] at hdet023
    have hfactor : -(x * (x + 1)) + (-1 : F) * (x + 1) = -((x + 1) * (x + 1)) := by
      rw [neg_one_mul, ← neg_add, right_distrib, one_mul]
    rw [hfactor] at hdet023
    calc
      (x + 1) * (x + 1) = -(-((x + 1) * (x + 1))) := (neg_neg _).symm
      _ = -(0 : F) := by rw [hdet023]
      _ = 0 := neg_zero
  have hx1_zero : x + 1 = 0 := by
    cases mul_eq_zero hsq_x with
    | inl h => exact h
    | inr h => exact h
  have hx_eq : x = -1 := eq_neg_of_add_eq_zero hx1_zero
  have hdet013 := subDet3_eq_zero_of_rank_le_two hrk2 0 1 3 0 1 3
  unfold subDet3 at hdet013
  rw [hcomp 0 0 rfl, hcomp 0 1 rfl, hcomp 0 3 rfl,
      hcomp 1 0 rfl, hcomp 1 1 rfl,
      hcomp 3 0 rfl, hy_sym, hcomp 3 3 rfl] at hdet013
  dsimp [S_C4_minus] at hdet013
  have hy1_sq : (y + 1) * (y + 1) = 0 := by
    change (1 : F) * (1 * 1 - y * y) - 1 * (1 * 1 - y * (-1)) + (-1) * (1 * y - 1 * (-1)) = 0 at hdet013
    rw [one_mul (1 * 1 - y * y), one_mul (1 * 1 - y * (-1)), mul_one (1 : F),
        mul_neg y 1, mul_one y, sub_eq_add_neg (1 : F) (-y), neg_neg y,
        one_mul y, mul_neg (1 : F) 1, mul_one (1 : F), sub_eq_add_neg y (-1), neg_neg (1 : F)] at hdet013
    have hsimp : (((1 : F) - y * y) - (1 + y)) + (-1 : F) * (y + 1) = -((y + 1) * (y + 1)) := by
      rw [neg_one_mul]
      have h1 : ((1 : F) - y * y) - (1 + y) = -(y * y) + -y := by
        rw [sub_eq_add_neg, sub_eq_add_neg, neg_add]
        calc
          ((1 : F) + -(y * y)) + (-1 + -y)
              = ((1 : F) + -1) + (-(y * y) + -y) := by
                calc
                  ((1 : F) + -(y * y)) + (-1 + -y) = (1 : F) + (-(y * y) + (-1 + -y)) := by rw [add_assoc]
                  _ = (1 : F) + ((-1 + -(y * y)) + -y) := by
                        rw [← add_assoc (-(y * y)) (-1) (-y), add_comm (-(y * y)) (-1)]
                  _ = ((1 : F) + -1) + (-(y * y) + -y) := by
                        rw [add_assoc (-1) (-(y * y)) (-y), ← add_assoc (1 : F) (-1)]
          _ = -(y * y) + -y := by rw [add_neg_cancel, zero_add]
      rw [h1]
      have h2 : (y + 1) * (y + 1) = (y * y + y) + (y + 1) := by
        rw [right_distrib, left_distrib, one_mul, mul_one]
      simp only [h2, neg_add]
    rw [hsimp] at hdet013
    calc
      (y + 1) * (y + 1) = -(-((y + 1) * (y + 1))) := (neg_neg _).symm
      _ = -(0 : F) := by rw [hdet013]
      _ = 0 := neg_zero
  have hy1_zero : y + 1 = 0 := by
    cases mul_eq_zero hy1_sq with
    | inl h => exact h
    | inr h => exact h
  have hy_eq : y = -1 := eq_neg_of_add_eq_zero hy1_zero
  have hdet_off := subDet3_eq_zero_of_rank_le_two hrk2 0 1 2 1 2 3
  unfold subDet3 at hdet_off
  rw [hcomp 0 1 rfl, show M 0 2 = -1 from hx_eq, hcomp 0 3 rfl,
      hcomp 1 1 rfl, hcomp 1 2 rfl, show M 1 3 = -1 from hy_eq,
      hcomp 2 1 rfl, hcomp 2 2 rfl, hcomp 2 3 rfl] at hdet_off
  dsimp [S_C4_minus] at hdet_off
  change (1 : F) * (1 * 1 - (-1) * 1) - (-1) * (1 * 1 - (-1) * 1) + (-1) * (1 * 1 - 1 * 1) = 0 at hdet_off
  rw [mul_one (1 : F), sub_self (1 : F), mul_zero (-1 : F), add_zero,
      mul_one (-1 : F), sub_eq_add_neg (1 : F) (-1), neg_neg (1 : F),
      one_mul, neg_one_mul, sub_eq_add_neg, neg_neg] at hdet_off
  have hfour : ((1 : F) + 1) * ((1 : F) + 1) = ((1 : F) + 1) + ((1 : F) + 1) := by
    rw [left_distrib ((1 : F) + 1) 1 1, mul_one ((1 : F) + 1)]
  rw [← hfour] at hdet_off
  exact mul_ne_zero hchar hchar hdet_off

/-- Exact symmetric minimum completion rank of `S_{C₄}⁻` is `3`. -/
theorem S_C4_minus_minSymRank_three {F : Type u} [FieldR F] (hchar : (1 : F) + 1 ≠ 0) :
    IsMinSymCompletionRank F (S_C4_minus F) 3 := by
  constructor
  · let U : Mat F 4 3 := fun i t =>
      match i.val, t.val with
      | 0, 0 => 1
      | 1, 1 => 1
      | 2, 2 => 1
      | 3, 0 => -1
      | _, _ => 0
    let V : Mat F 3 4 := fun t j =>
      match t.val, j.val with
      | 0, 0 => 1  | 0, 1 => 1  | 0, 2 => -1 | 0, 3 => -1
      | 1, 0 => 1  | 1, 1 => 1  | 1, 2 => 1  | 1, 3 => -1
      | _, 0 => -1 | _, 1 => 1  | _, 2 => 1  | _, _ => 1
    let M : Mat F 4 4 := fun i j => finSum (fun t : Fin 3 => U i t * V t j)
    refine ⟨M, ⟨?_, ?_⟩, ⟨U, V, fun _ _ => rfl⟩⟩
    · refine fin4_cases ?_ ?_ ?_ ?_ <;> refine fin4_cases ?_ ?_ ?_ ?_ <;> first
        | rfl
        | (dsimp [M]; rw [finSum_three, finSum_three]; dsimp [U, V];
           simp only [one_mul, mul_one, zero_mul, mul_zero, neg_one_mul, neg_mul_neg, add_zero, zero_add, neg_neg])
    · refine fin4_cases ?_ ?_ ?_ ?_ <;> refine fin4_cases ?_ ?_ ?_ ?_ <;> intro hs <;> first
        | contradiction
        | (dsimp [M]; rw [finSum_three]; dsimp [U, V, S_C4_minus];
           simp only [one_mul, mul_one, zero_mul, mul_zero, neg_one_mul, neg_mul_neg, add_zero, zero_add, neg_neg])
  · intro r' hr' M hsym hrk
    have hle2 : r' ≤ 2 := by omega
    exact S_C4_minus_no_sym_rank_two hchar M hsym (HasRankAtMost.mono hle2 hrk)

/-! ### Odd `5`-Cycle `C₅` AND Even `6`-Cycle `C₆` with Unit Diagonal -/

def spec_C5_diag (i j : Fin 5) : Bool :=
  i == j || ((i.val + 1) % 5 == j.val) || ((j.val + 1) % 5 == i.val)

def spec_C6_diag (i j : Fin 6) : Bool :=
  i == j || ((i.val + 1) % 6 == j.val) || ((j.val + 1) % 6 == i.val)

def S_C5_minus (F : Type u) [FieldR F] : PartialMatrix F 5 5 where
  spec := spec_C5_diag
  val  := fun i j =>
    match i.val, j.val with
    | 0, 4 => -1
    | 4, 0 => -1
    | _, _ => 1

def S_C6_minus (F : Type u) [FieldR F] : PartialMatrix F 6 6 where
  spec := spec_C6_diag
  val  := fun i j =>
    match i.val, j.val with
    | 0, 5 => -1
    | 5, 0 => -1
    | _, _ => 1

set_option synthInstance.maxSize 2048 in
theorem spec_C5_diag_biclique :
    ∀ r₁ r₂ c₁ c₂ : Fin 5,
      r₁ ≠ r₂ → c₁ ≠ c₂ →
      spec_C5_diag r₁ c₁ = true → spec_C5_diag r₂ c₁ = true →
      spec_C5_diag r₁ c₂ = true → spec_C5_diag r₂ c₂ = true →
      (c₁ = r₁ ∨ c₁ = r₂) ∧ (c₂ = r₁ ∨ c₂ = r₂) := by
  decide

set_option synthInstance.maxSize 2048 in
theorem spec_C6_diag_biclique :
    ∀ r₁ r₂ c₁ c₂ : Fin 6,
      r₁ ≠ r₂ → c₁ ≠ c₂ →
      spec_C6_diag r₁ c₁ = true → spec_C6_diag r₂ c₁ = true →
      spec_C6_diag r₁ c₂ = true → spec_C6_diag r₂ c₂ = true →
      (c₁ = r₁ ∨ c₁ = r₂) ∧ (c₂ = r₁ ∨ c₂ = r₂) := by
  decide

theorem hasRankAtMost_one_of_two_val_edge {R : Type u} [CommRingR R] {n a b : Nat}
    (A : Mat R n n) (r₁ r₂ : Fin n)
    (hd1 : A r₁ r₁ = 1) (hd2 : A r₂ r₂ = 1)
    (hsym : A r₂ r₁ = A r₁ r₂) (hsq : A r₁ r₂ * A r₁ r₂ = 1)
    (rows : Fin a → Fin n) (cols : Fin b → Fin n)
    (hr : ∀ x, rows x = r₁ ∨ rows x = r₂)
    (hc : ∀ y, cols y = r₁ ∨ cols y = r₂) :
    HasRankAtMost R 1 (PartialMatrix.submatrix A rows cols) := by
  rw [hasRankAtMost_one_iff_outer]
  let s := A r₁ r₂
  let u : Fin a → R := fun x => if rows x = r₁ then 1 else s
  let v : Fin b → R := fun y => if cols y = r₁ then 1 else s
  refine ⟨u, v, ?_⟩
  intro x y
  unfold PartialMatrix.submatrix
  rcases hr x with hx1 | hx2 <;> rcases hc y with hy1 | hy2
  · simp [u, v, hx1, hy1, hd1, mul_one]
  · by_cases hrr : r₂ = r₁
    · subst hrr
      simp [u, v, hx1, hy2, hd1, mul_one]
    · have hcy : cols y ≠ r₁ := by rw [hy2]; exact hrr
      simp [u, v, hx1, hcy, one_mul]
      rw [hy2]
  · by_cases hrr : r₂ = r₁
    · subst hrr
      simp [u, v, hx2, hy1, hd1, mul_one]
    · have hrx : rows x ≠ r₁ := by rw [hx2]; exact hrr
      simp [u, v, hrx, hy1, mul_one]
      rw [hx2, hsym]
  · by_cases hrr : r₂ = r₁
    · subst hrr
      simp [u, v, hx2, hy2, hd1, mul_one]
    · have hrx : rows x ≠ r₁ := by rw [hx2]; exact hrr
      have hcy : cols y ≠ r₁ := by rw [hy2]; exact hrr
      simp [u, v, hrx, hcy]
      rw [hx2, hy2, hd2]
      exact hsq.symm

theorem S_C5_minus_locallyRankOne (F : Type u) [FieldR F] :
    PartialMatrix.LocallyRankAtMost F 1 (S_C5_minus F) := by
  intro a b rows cols hfull
  by_cases hrows : ∀ x₁ x₂ : Fin a, rows x₁ = rows x₂
  · apply hasRankAtMost_one_of_const_rows_or_cols
    left; intro x₁ x₂ y; unfold PartialMatrix.submatrix; rw [hrows x₁ x₂]
  · by_cases hcols : ∀ y₁ y₂ : Fin b, cols y₁ = cols y₂
    · apply hasRankAtMost_one_of_const_rows_or_cols
      right; intro y₁ y₂ x; unfold PartialMatrix.submatrix; rw [hcols y₁ y₂]
    · have hexR : ∃ x₁ x₂ : Fin a, rows x₁ ≠ rows x₂ := by
        by_cases h1 : ∃ x₁ x₂ : Fin a, rows x₁ ≠ rows x₂
        · exact h1
        · exfalso; apply hrows; intro x₁ x₂
          by_cases he : rows x₁ = rows x₂; exact he; exact absurd ⟨x₁, x₂, he⟩ h1
      have hexC : ∃ y₁ y₂ : Fin b, cols y₁ ≠ cols y₂ := by
        by_cases h1 : ∃ y₁ y₂ : Fin b, cols y₁ ≠ cols y₂
        · exact h1
        · exfalso; apply hcols; intro y₁ y₂
          by_cases he : cols y₁ = cols y₂; exact he; exact absurd ⟨y₁, y₂, he⟩ h1
      rcases hexR with ⟨x₁, x₂, hrx⟩
      rcases hexC with ⟨y₁, y₂, hcy⟩
      let r₁ := rows x₁
      let r₂ := rows x₂
      have hc_mem : ∀ y : Fin b, cols y = r₁ ∨ cols y = r₂ := by
        intro y
        by_cases hy1 : cols y = cols y₁
        · rw [hy1]
          exact (spec_C5_diag_biclique r₁ r₂ (cols y₁) (cols y₂) hrx hcy
            (hfull x₁ y₁) (hfull x₂ y₁) (hfull x₁ y₂) (hfull x₂ y₂)).1
        · exact (spec_C5_diag_biclique r₁ r₂ (cols y) (cols y₁) hrx hy1
            (hfull x₁ y) (hfull x₂ y) (hfull x₁ y₁) (hfull x₂ y₁)).1
      have hr_mem : ∀ x : Fin a, rows x = r₁ ∨ rows x = r₂ := by
        intro x
        by_cases hx1 : rows x = r₁
        · exact Or.inl hx1
        · have hc12 := spec_C5_diag_biclique r₁ r₂ (cols y₁) (cols y₂) hrx hcy
            (hfull x₁ y₁) (hfull x₂ y₁) (hfull x₁ y₂) (hfull x₂ y₂)
          have hcx := spec_C5_diag_biclique (rows x) r₁ (cols y₁) (cols y₂) hx1 hcy
            (hfull x y₁) (hfull x₁ y₁) (hfull x y₂) (hfull x₁ y₂)
          rcases hc12 with ⟨c1r, c2r⟩
          rcases hcx with ⟨c1x, c2x⟩
          rcases c1r with h1 | h1 <;> rcases c2r with h2 | h2
          · exact absurd (h1.trans h2.symm) hcy
          · rcases c2x with h3 | h3
            · right; exact h3.symm.trans h2
            · exact absurd (h1.trans h3.symm) hcy
          · rcases c1x with h3 | h3
            · right; exact h3.symm.trans h1
            · exact absurd (h1.symm.trans h3) hrx.symm
          · exact absurd (h1.trans h2.symm) hcy
      have hd_all : ∀ r : Fin 5, (S_C5_minus F).val r r = 1 := by
        refine fin5_cases ?_ ?_ ?_ ?_ ?_ <;> rfl
      have hsym_all : ∀ a b : Fin 5, (S_C5_minus F).val b a = (S_C5_minus F).val a b := by
        refine fin5_cases ?_ ?_ ?_ ?_ ?_ <;> refine fin5_cases ?_ ?_ ?_ ?_ ?_ <;> rfl
      have hd1 : (S_C5_minus F).val r₁ r₁ = 1 := hd_all r₁
      have hd2 : (S_C5_minus F).val r₂ r₂ = 1 := hd_all r₂
      have hsym : (S_C5_minus F).val r₂ r₁ = (S_C5_minus F).val r₁ r₂ := hsym_all r₁ r₂
      have hsq_all : ∀ a b : Fin 5, (S_C5_minus F).val a b * (S_C5_minus F).val a b = 1 := by
        refine fin5_cases ?_ ?_ ?_ ?_ ?_ <;> refine fin5_cases ?_ ?_ ?_ ?_ ?_ <;>
          (dsimp [S_C5_minus]; simp only [neg_mul_neg, mul_one])
      have hsq : (S_C5_minus F).val r₁ r₂ * (S_C5_minus F).val r₁ r₂ = 1 := hsq_all r₁ r₂
      exact hasRankAtMost_one_of_two_val_edge (S_C5_minus F).val r₁ r₂ hd1 hd2 hsym hsq rows cols hr_mem hc_mem

theorem S_C6_minus_locallyRankOne (F : Type u) [FieldR F] :
    PartialMatrix.LocallyRankAtMost F 1 (S_C6_minus F) := by
  intro a b rows cols hfull
  by_cases hrows : ∀ x₁ x₂ : Fin a, rows x₁ = rows x₂
  · apply hasRankAtMost_one_of_const_rows_or_cols
    left; intro x₁ x₂ y; unfold PartialMatrix.submatrix; rw [hrows x₁ x₂]
  · by_cases hcols : ∀ y₁ y₂ : Fin b, cols y₁ = cols y₂
    · apply hasRankAtMost_one_of_const_rows_or_cols
      right; intro y₁ y₂ x; unfold PartialMatrix.submatrix; rw [hcols y₁ y₂]
    · have hexR : ∃ x₁ x₂ : Fin a, rows x₁ ≠ rows x₂ := by
        by_cases h1 : ∃ x₁ x₂ : Fin a, rows x₁ ≠ rows x₂
        · exact h1
        · exfalso; apply hrows; intro x₁ x₂
          by_cases he : rows x₁ = rows x₂; exact he; exact absurd ⟨x₁, x₂, he⟩ h1
      have hexC : ∃ y₁ y₂ : Fin b, cols y₁ ≠ cols y₂ := by
        by_cases h1 : ∃ y₁ y₂ : Fin b, cols y₁ ≠ cols y₂
        · exact h1
        · exfalso; apply hcols; intro y₁ y₂
          by_cases he : cols y₁ = cols y₂; exact he; exact absurd ⟨y₁, y₂, he⟩ h1
      rcases hexR with ⟨x₁, x₂, hrx⟩
      rcases hexC with ⟨y₁, y₂, hcy⟩
      let r₁ := rows x₁
      let r₂ := rows x₂
      have hc_mem : ∀ y : Fin b, cols y = r₁ ∨ cols y = r₂ := by
        intro y
        by_cases hy1 : cols y = cols y₁
        · rw [hy1]
          exact (spec_C6_diag_biclique r₁ r₂ (cols y₁) (cols y₂) hrx hcy
            (hfull x₁ y₁) (hfull x₂ y₁) (hfull x₁ y₂) (hfull x₂ y₂)).1
        · exact (spec_C6_diag_biclique r₁ r₂ (cols y) (cols y₁) hrx hy1
            (hfull x₁ y) (hfull x₂ y) (hfull x₁ y₁) (hfull x₂ y₁)).1
      have hr_mem : ∀ x : Fin a, rows x = r₁ ∨ rows x = r₂ := by
        intro x
        by_cases hx1 : rows x = r₁
        · exact Or.inl hx1
        · have hc12 := spec_C6_diag_biclique r₁ r₂ (cols y₁) (cols y₂) hrx hcy
            (hfull x₁ y₁) (hfull x₂ y₁) (hfull x₁ y₂) (hfull x₂ y₂)
          have hcx := spec_C6_diag_biclique (rows x) r₁ (cols y₁) (cols y₂) hx1 hcy
            (hfull x y₁) (hfull x₁ y₁) (hfull x y₂) (hfull x₁ y₂)
          rcases hc12 with ⟨c1r, c2r⟩
          rcases hcx with ⟨c1x, c2x⟩
          rcases c1r with h1 | h1 <;> rcases c2r with h2 | h2
          · exact absurd (h1.trans h2.symm) hcy
          · rcases c2x with h3 | h3
            · right; exact h3.symm.trans h2
            · exact absurd (h1.trans h3.symm) hcy
          · rcases c1x with h3 | h3
            · right; exact h3.symm.trans h1
            · exact absurd (h1.symm.trans h3) hrx.symm
          · exact absurd (h1.trans h2.symm) hcy
      have hd_all : ∀ r : Fin 6, (S_C6_minus F).val r r = 1 := by
        refine fin6_cases ?_ ?_ ?_ ?_ ?_ ?_ <;> rfl
      have hsym_all : ∀ a b : Fin 6, (S_C6_minus F).val b a = (S_C6_minus F).val a b := by
        refine fin6_cases ?_ ?_ ?_ ?_ ?_ ?_ <;> refine fin6_cases ?_ ?_ ?_ ?_ ?_ ?_ <;> rfl
      have hd1 : (S_C6_minus F).val r₁ r₁ = 1 := hd_all r₁
      have hd2 : (S_C6_minus F).val r₂ r₂ = 1 := hd_all r₂
      have hsym : (S_C6_minus F).val r₂ r₁ = (S_C6_minus F).val r₁ r₂ := hsym_all r₁ r₂
      have hsq_all : ∀ a b : Fin 6, (S_C6_minus F).val a b * (S_C6_minus F).val a b = 1 := by
        refine fin6_cases ?_ ?_ ?_ ?_ ?_ ?_ <;> refine fin6_cases ?_ ?_ ?_ ?_ ?_ ?_ <;>
          (dsimp [S_C6_minus]; simp only [neg_mul_neg, mul_one])
      have hsq : (S_C6_minus F).val r₁ r₂ * (S_C6_minus F).val r₁ r₂ = 1 := hsq_all r₁ r₂
      exact hasRankAtMost_one_of_two_val_edge (S_C6_minus F).val r₁ r₂ hd1 hd2 hsym hsq rows cols hr_mem hc_mem

theorem S_C5_minus_not_rank_one {F : Type u} [FieldR F] (hchar : (1 : F) + 1 ≠ 0)
    (M : Mat F 5 5) (hcomp : (S_C5_minus F).IsCompletion M) :
    ¬ HasRankAtMost F 1 M := by
  intro hrk
  have hcyc := directed_cycle_diag_product_eq (k := 4) hrk (fun t => t)
  have hL : finProd (fun t : Fin 5 => M t (nextIdx t)) =
      M 0 1 * (M 1 2 * (M 2 3 * (M 3 4 * (M 4 0 * 1)))) := rfl
  have hR : finProd (fun t : Fin 5 => M t t) =
      M 0 0 * (M 1 1 * (M 2 2 * (M 3 3 * (M 4 4 * 1)))) := rfl
  rw [hL, hR] at hcyc
  rw [hcomp 0 1 rfl, hcomp 1 2 rfl, hcomp 2 3 rfl, hcomp 3 4 rfl, hcomp 4 0 rfl,
      hcomp 0 0 rfl, hcomp 1 1 rfl, hcomp 2 2 rfl, hcomp 3 3 rfl, hcomp 4 4 rfl] at hcyc
  dsimp [S_C5_minus] at hcyc
  simp only [mul_one, one_mul] at hcyc
  exact neg_one_ne_one hchar hcyc

theorem S_C6_minus_not_rank_one {F : Type u} [FieldR F] (hchar : (1 : F) + 1 ≠ 0)
    (M : Mat F 6 6) (hcomp : (S_C6_minus F).IsCompletion M) :
    ¬ HasRankAtMost F 1 M := by
  intro hrk
  have hcyc := directed_cycle_diag_product_eq (k := 5) hrk (fun t => t)
  have hL : finProd (fun t : Fin 6 => M t (nextIdx t)) =
      M 0 1 * (M 1 2 * (M 2 3 * (M 3 4 * (M 4 5 * (M 5 0 * 1))))) := rfl
  have hR : finProd (fun t : Fin 6 => M t t) =
      M 0 0 * (M 1 1 * (M 2 2 * (M 3 3 * (M 4 4 * (M 5 5 * 1))))) := rfl
  rw [hL, hR] at hcyc
  rw [hcomp 0 1 rfl, hcomp 1 2 rfl, hcomp 2 3 rfl, hcomp 3 4 rfl, hcomp 4 5 rfl, hcomp 5 0 rfl,
      hcomp 0 0 rfl, hcomp 1 1 rfl, hcomp 2 2 rfl, hcomp 3 3 rfl, hcomp 4 4 rfl, hcomp 5 5 rfl] at hcyc
  dsimp [S_C6_minus] at hcyc
  simp only [mul_one, one_mul] at hcyc
  exact neg_one_ne_one hchar hcyc

/-! ### Variant 2B: Free Diagonal on Undirected Graphs -/

def spec_C3_freeDiag (i j : Fin 3) : Bool := i != j

/-- Positive Theorem: On the odd `3`-cycle `C₃` with free diagonal, EVERY everywhere-nonzero
symmetric edge assignment `(a₀₁, a₀₂, a₁₂)` has exact symmetric AND general minimum completion rank `1`
over EVERY field `F`. -/
theorem freeDiag_odd_C3_always_rank_one {F : Type u} [FieldR F]
    (a01 a02 a12 : F) (h01 : a01 ≠ 0) (h02 : a02 ≠ 0) (h12 : a12 ≠ 0) :
    let P : PartialMatrix F 3 3 := {
      spec := spec_C3_freeDiag
      val  := fun i j =>
        match i.val, j.val with
        | 0, 1 => a01 | 1, 0 => a01
        | 0, 2 => a02 | 2, 0 => a02
        | 1, 2 => a12 | 2, 1 => a12
        | _, _ => 0
    }
    IsMinCompletionRank F P 1 ∧ IsMinSymCompletionRank F P 1 := by
  intro P
  let prod := a01 * (a02 * a12)
  have hprod : prod ≠ 0 := mul_ne_zero h01 (mul_ne_zero h02 h12)
  let lam := prod⁻¹
  let w : Fin 3 → F := fun i =>
    match i.val with
    | 0 => a01 * a02
    | 1 => a01 * a12
    | _ => a02 * a12
  let M : Mat F 3 3 := fun i j => (lam * w i) * w j
  have hsymM : IsSymmetric M := by
    intro i j
    dsimp [M]
    rw [mul_assoc, mul_comm (w i) (w j), ← mul_assoc]
  have hrkM : HasRankAtMost F 1 M :=
    (hasRankAtMost_one_iff_outer M).mpr ⟨fun i => lam * w i, w, fun _ _ => rfl⟩
  have h01_calc : (lam * (a01 * a02)) * (a01 * a12) = a01 := by
    dsimp [lam, prod]
    have hrearr : (a01 * a02) * (a01 * a12) = (a01 * (a02 * a12)) * a01 := by
      calc
        (a01 * a02) * (a01 * a12) = a01 * (a02 * (a01 * a12)) := by rw [mul_assoc]
        _ = a01 * ((a02 * a01) * a12) := by rw [← mul_assoc a02 a01 a12]
        _ = a01 * ((a01 * a02) * a12) := by rw [mul_comm a02 a01]
        _ = a01 * (a01 * (a02 * a12)) := by rw [mul_assoc a01 a02 a12]
        _ = (a01 * (a02 * a12)) * a01 := mul_comm a01 (a01 * (a02 * a12))
    rw [mul_assoc, hrearr, ← mul_assoc, inv_mul_cancel hprod, one_mul]
  have h02_calc : (lam * (a01 * a02)) * (a02 * a12) = a02 := by
    dsimp [lam, prod]
    have hrearr : (a01 * a02) * (a02 * a12) = (a01 * (a02 * a12)) * a02 := by
      calc
        (a01 * a02) * (a02 * a12) = a01 * (a02 * (a02 * a12)) := by rw [mul_assoc]
        _ = a01 * ((a02 * a12) * a02) := by rw [mul_comm a02 (a02 * a12)]
        _ = (a01 * (a02 * a12)) * a02 := by rw [← mul_assoc]
    rw [mul_assoc, hrearr, ← mul_assoc, inv_mul_cancel hprod, one_mul]
  have h12_calc : (lam * (a01 * a12)) * (a02 * a12) = a12 := by
    dsimp [lam, prod]
    have hrearr : (a01 * a12) * (a02 * a12) = (a01 * (a02 * a12)) * a12 := by
      calc
        (a01 * a12) * (a02 * a12) = a01 * (a12 * (a02 * a12)) := by rw [mul_assoc]
        _ = a01 * ((a12 * a02) * a12) := by rw [← mul_assoc a12 a02 a12]
        _ = a01 * ((a02 * a12) * a12) := by rw [mul_comm a12 a02]
        _ = (a01 * (a02 * a12)) * a12 := by rw [← mul_assoc]
    rw [mul_assoc, hrearr, ← mul_assoc, inv_mul_cancel hprod, one_mul]
  have hcompM : P.IsCompletion M := by
    refine fin3_cases ?_ ?_ ?_ <;> refine fin3_cases ?_ ?_ ?_ <;> intro hs
    · contradiction
    · exact h01_calc
    · exact h02_calc
    · rw [hsymM 1 0]; exact h01_calc
    · contradiction
    · exact h12_calc
    · rw [hsymM 2 0]; exact h02_calc
    · rw [hsymM 2 1]; exact h12_calc
    · contradiction
  constructor
  · refine ⟨⟨M, hcompM, hrkM⟩, ?_⟩
    intro r' hr' N hcompN
    have hr0 : r' = 0 := by omega
    subst hr0
    have hne : N 0 1 ≠ 0 := by rw [hcompN 0 1 rfl]; exact h01
    exact not_hasRankAtMost_zero_of_entry_ne_zero 0 1 hne
  · refine ⟨⟨M, ⟨hsymM, hcompM⟩, hrkM⟩, ?_⟩
    intro r' hr' N hcompN
    have hr0 : r' = 0 := by omega
    subst hr0
    have hne : N 0 1 ≠ 0 := by rw [hcompN.2 0 1 rfl]; exact h01
    exact not_hasRankAtMost_zero_of_entry_ne_zero 0 1 hne

def spec_C4_freeDiag (i j : Fin 4) : Bool :=
  (i == 0 && j == 1) || (i == 1 && j == 0) ||
  (i == 1 && j == 2) || (i == 2 && j == 1) ||
  (i == 2 && j == 3) || (i == 3 && j == 2) ||
  (i == 0 && j == 3) || (i == 3 && j == 0)

def P_C4_free_plus (F : Type u) [FieldR F] : PartialMatrix F 4 4 where
  spec := spec_C4_freeDiag
  val  := fun _ _ => 1

def P_C4_free_minus (F : Type u) [FieldR F] : PartialMatrix F 4 4 where
  spec := spec_C4_freeDiag
  val  := fun i j =>
    match i.val, j.val with
    | 0, 3 => -1
    | 3, 0 => -1
    | _, _ => 1

theorem freeDiag_even_C4_obstruction {F : Type u} [FieldR F] (hchar : (1 : F) + 1 ≠ 0) :
    IsMinCompletionRank F (P_C4_free_plus F) 1 ∧
    IsMinSymCompletionRank F (P_C4_free_plus F) 1 ∧
    IsMinCompletionRank F (P_C4_free_minus F) 2 ∧
    IsMinSymCompletionRank F (P_C4_free_minus F) 2 := by
  have hrk1 : HasRankAtMost F 1 (fun (_ _ : Fin 4) => (1 : F)) :=
    (hasRankAtMost_one_iff_outer _).mpr ⟨fun _ => 1, fun _ => 1, fun _ _ => (mul_one 1).symm⟩
  have hnot1 : ∀ M : Mat F 4 4, (P_C4_free_minus F).IsCompletion M → ¬ HasRankAtMost F 1 M := by
    intro M hcomp hrk
    have hmin := minor2_eq_of_rank_le_one hrk 0 2 1 3
    rw [hcomp 0 1 rfl, hcomp 2 3 rfl, hcomp 0 3 rfl, hcomp 2 1 rfl] at hmin
    dsimp [P_C4_free_minus] at hmin
    rw [mul_one, mul_one] at hmin
    exact neg_one_ne_one hchar hmin.symm
  let U : Mat F 4 2 := fun i t =>
    match i.val, t.val with
    | 0, 0 => 1  | 0, _ => 0
    | 1, 0 => 1  | 1, _ => 1
    | 2, 0 => 0  | 2, _ => 1
    | _, 0 => -1 | _, _ => 1
  let UT : Mat F 2 4 := fun t j => U j t
  let M2 : Mat F 4 4 := fun i j => finSum (fun t : Fin 2 => U i t * UT t j)
  have hcomm2 : ∀ a0 b0 a1 b1 : F, a0 * b0 + a1 * b1 = b0 * a0 + b1 * a1 :=
    fun a0 b0 a1 b1 => by rw [mul_comm a0 b0, mul_comm a1 b1]
  have hsym2 : IsSymmetric M2 := by
    intro i j
    dsimp [M2, UT]
    rw [finSum_two, finSum_two]
    exact hcomm2 _ _ _ _
  have hcomp2 : (P_C4_free_minus F).IsCompletion M2 := by
    refine fin4_cases ?_ ?_ ?_ ?_ <;> refine fin4_cases ?_ ?_ ?_ ?_ <;> intro hs <;> first
      | contradiction
      | (dsimp [M2, UT]; rw [finSum_two]; dsimp [U, P_C4_free_minus];
         simp only [one_mul, mul_one, zero_mul, mul_zero, neg_one_mul, neg_mul_neg, neg_neg, add_zero, zero_add])
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨⟨fun _ _ => 1, fun _ _ _ => rfl, hrk1⟩, ?_⟩
    intro r' hr' M hcomp
    have hr0 : r' = 0 := by omega
    subst hr0
    have hne : M 0 1 ≠ 0 := by rw [hcomp 0 1 rfl]; exact one_ne_zero
    exact not_hasRankAtMost_zero_of_entry_ne_zero 0 1 hne
  · refine ⟨⟨fun _ _ => 1, ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩, hrk1⟩, ?_⟩
    intro r' hr' M hcomp
    have hr0 : r' = 0 := by omega
    subst hr0
    have hne : M 0 1 ≠ 0 := by rw [hcomp.2 0 1 rfl]; exact one_ne_zero
    exact not_hasRankAtMost_zero_of_entry_ne_zero 0 1 hne
  · refine ⟨⟨M2, hcomp2, ⟨U, UT, fun _ _ => rfl⟩⟩, ?_⟩
    intro r' hr' M hcomp
    have hcases : r' = 0 ∨ r' = 1 := by omega
    cases hcases with
    | inl h0 =>
      subst h0
      have hne : M 0 1 ≠ 0 := by rw [hcomp 0 1 rfl]; exact one_ne_zero
      exact not_hasRankAtMost_zero_of_entry_ne_zero 0 1 hne
    | inr h1 =>
      subst h1
      exact hnot1 M hcomp
  · refine ⟨⟨M2, ⟨hsym2, hcomp2⟩, ⟨U, UT, fun _ _ => rfl⟩⟩, ?_⟩
    intro r' hr' M hcomp
    have hcases : r' = 0 ∨ r' = 1 := by omega
    cases hcases with
    | inl h0 =>
      subst h0
      have hne : M 0 1 ≠ 0 := by rw [hcomp.2 0 1 rfl]; exact one_ne_zero
      exact not_hasRankAtMost_zero_of_entry_ne_zero 0 1 hne
    | inr h1 =>
      subst h1
      exact hnot1 M hcomp.2

def spec_Butterfly_freeDiag (i j : Fin 5) : Bool :=
  (i == 0 && j == 1) || (i == 1 && j == 0) ||
  (i == 0 && j == 2) || (i == 2 && j == 0) ||
  (i == 1 && j == 2) || (i == 2 && j == 1) ||
  (i == 0 && j == 3) || (i == 3 && j == 0) ||
  (i == 0 && j == 4) || (i == 4 && j == 0) ||
  (i == 3 && j == 4) || (i == 4 && j == 3)

def P_Butterfly_plus (F : Type u) [FieldR F] : PartialMatrix F 5 5 where
  spec := spec_Butterfly_freeDiag
  val  := fun _ _ => 1

def P_Butterfly_minus (F : Type u) [FieldR F] : PartialMatrix F 5 5 where
  spec := spec_Butterfly_freeDiag
  val  := fun i j =>
    match i.val, j.val with
    | 0, 4 => -1
    | 4, 0 => -1
    | _, _ => 1

/-- Even on the purely-odd-cycle Butterfly graph `B₂` with free diagonal, `P_Butterfly_plus`
has `mr = smr = 1` whereas `P_Butterfly_minus` has `mr = smr = 2`. -/
theorem freeDiag_butterfly_odd_cycles_obstruct {F : Type u} [FieldR F] (hchar : (1 : F) + 1 ≠ 0) :
    IsMinCompletionRank F (P_Butterfly_plus F) 1 ∧
    IsMinSymCompletionRank F (P_Butterfly_plus F) 1 ∧
    IsMinCompletionRank F (P_Butterfly_minus F) 2 ∧
    IsMinSymCompletionRank F (P_Butterfly_minus F) 2 := by
  have hrk1 : HasRankAtMost F 1 (fun (_ _ : Fin 5) => (1 : F)) :=
    (hasRankAtMost_one_iff_outer _).mpr ⟨fun _ => 1, fun _ => 1, fun _ _ => (mul_one 1).symm⟩
  have hnot1 : ∀ M : Mat F 5 5, (P_Butterfly_minus F).IsCompletion M → ¬ HasRankAtMost F 1 M := by
    intro M hcomp hrk
    have ht1 := minor2_eq_of_rank_le_one hrk 0 2 0 1
    rw [hcomp 2 1 rfl, hcomp 0 1 rfl, hcomp 2 0 rfl] at ht1
    dsimp [P_Butterfly_minus] at ht1
    rw [mul_one, mul_one] at ht1
    have ht2 := minor2_eq_of_rank_le_one hrk 0 4 0 3
    rw [hcomp 4 3 rfl, hcomp 0 3 rfl, hcomp 4 0 rfl] at ht2
    dsimp [P_Butterfly_minus] at ht2
    rw [mul_one, one_mul] at ht2
    exact neg_one_ne_one hchar (ht2.symm.trans ht1)
  let x : Fin 5 → F := fun i =>
    match i.val with
    | 0 => 1 | 1 => 1 | 2 => 0 | 3 => 0 | _ => 1
  let y : Fin 5 → F := fun i =>
    match i.val with
    | 0 => 0 | 1 => 1 | 2 => 1 | 3 => 1 | _ => -1
  let U : Mat F 5 2 := fun i t => match t.val with | 0 => x i | _ => y i
  let V : Mat F 2 5 := fun t j => match t.val with | 0 => y j | _ => x j
  let M2 : Mat F 5 5 := fun i j => finSum (fun t : Fin 2 => U i t * V t j)
  have hsym_helper : ∀ a b c d : F, a * b + c * d = d * c + b * a :=
    fun a b c d => by rw [mul_comm a b, mul_comm c d, add_comm]
  have hsym2 : IsSymmetric M2 := by
    intro i j
    dsimp [M2]
    rw [finSum_two, finSum_two]
    dsimp [U, V]
    exact hsym_helper _ _ _ _
  have hcomp2 : (P_Butterfly_minus F).IsCompletion M2 := by
    refine fin5_cases ?_ ?_ ?_ ?_ ?_ <;> refine fin5_cases ?_ ?_ ?_ ?_ ?_ <;> intro hs <;> first
      | contradiction
      | (dsimp [M2]; rw [finSum_two]; dsimp [U, V, x, y, P_Butterfly_minus];
         simp only [one_mul, mul_one, zero_mul, mul_zero, neg_one_mul, neg_mul_neg, neg_neg, add_zero, zero_add])
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨⟨fun _ _ => 1, fun _ _ _ => rfl, hrk1⟩, ?_⟩
    intro r' hr' M hcomp
    have hr0 : r' = 0 := by omega
    subst hr0
    have hne : M 0 1 ≠ 0 := by rw [hcomp 0 1 rfl]; exact one_ne_zero
    exact not_hasRankAtMost_zero_of_entry_ne_zero 0 1 hne
  · refine ⟨⟨fun _ _ => 1, ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩, hrk1⟩, ?_⟩
    intro r' hr' M hcomp
    have hr0 : r' = 0 := by omega
    subst hr0
    have hne : M 0 1 ≠ 0 := by rw [hcomp.2 0 1 rfl]; exact one_ne_zero
    exact not_hasRankAtMost_zero_of_entry_ne_zero 0 1 hne
  · refine ⟨⟨M2, hcomp2, ⟨U, V, fun _ _ => rfl⟩⟩, ?_⟩
    intro r' hr' M hcomp
    have hcases : r' = 0 ∨ r' = 1 := by omega
    cases hcases with
    | inl h0 =>
      subst h0
      have hne : M 0 1 ≠ 0 := by rw [hcomp 0 1 rfl]; exact one_ne_zero
      exact not_hasRankAtMost_zero_of_entry_ne_zero 0 1 hne
    | inr h1 =>
      subst h1
      exact hnot1 M hcomp
  · refine ⟨⟨M2, ⟨hsym2, hcomp2⟩, ⟨U, V, fun _ _ => rfl⟩⟩, ?_⟩
    intro r' hr' M hcomp
    have hcases : r' = 0 ∨ r' = 1 := by omega
    cases hcases with
    | inl h0 =>
      subst h0
      have hne : M 0 1 ≠ 0 := by rw [hcomp.2 0 1 rfl]; exact one_ne_zero
      exact not_hasRankAtMost_zero_of_entry_ne_zero 0 1 hne
    | inr h1 =>
      subst h1
      exact hnot1 M hcomp.2

end Conjecture00000007178
