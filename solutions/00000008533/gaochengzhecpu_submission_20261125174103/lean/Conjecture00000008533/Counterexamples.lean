/-
Copyright (c) 2026. All rights reserved.
Core Lean 4.19.0 formalization for Conjecture 00000008533:
Parametric simple-matroid families (`directSumColoop` and `parallelConnUniform`) and
machine-checked refutations of:
  1. Classical rank-uniform LYM (`L34`, |L| = 34, rank 3: sum = 111/110 > 1);
  2. Rank-normalized two-sided Möbius LYM (`L46`, |L| = 46, rank 4: sum = 66/65 > 1);
  3. Rank-normalized upper Möbius LYM (`L922`, |L| = 922, rank 5: sum = 23788/23725 > 1);
  4. Optimality of rank-normalized lower Möbius weighting (`L10 = B_1 × M_3`, |L| = 10, rank 3:
     strictly suboptimal Sperner/maximin bound 1/5 < 2/9 < 1/4, non-dominant, and non-unique L^1).
-/
import Conjecture00000008533.Basic
import Conjecture00000008533.LubellLYM
import Conjecture00000008533.SimpleMatroid

namespace Conjecture00000008533

/-! ## 1. Rational Sum-Split Lemmas (Avoiding Unreduced Denominator Blowup) -/

namespace QRat

theorem eqv_symm {p q : QRat} (h : eqv p q) : eqv q p := h.symm

theorem eqv_trans {p q r : QRat} (h1 : eqv p q) (h2 : eqv q r) : eqv p r := by
  unfold eqv at h1 h2 ⊢
  have hq : (0 : Int) < (q.den : Int) := Int.ofNat_lt.mpr q.den_pos
  have e1 : (p.num * (r.den : Int)) * (q.den : Int) = (r.num * (p.den : Int)) * (q.den : Int) := by
    calc
      (p.num * (r.den : Int)) * (q.den : Int)
          = (p.num * (q.den : Int)) * (r.den : Int) := by
            rw [Int.mul_assoc, Int.mul_comm (r.den : Int) (q.den : Int), ← Int.mul_assoc]
      _ = (q.num * (p.den : Int)) * (r.den : Int) := by rw [h1]
      _ = (q.num * (r.den : Int)) * (p.den : Int) := by
            rw [Int.mul_assoc, Int.mul_comm (p.den : Int) (r.den : Int), ← Int.mul_assoc]
      _ = (r.num * (q.den : Int)) * (p.den : Int) := by rw [h2]
      _ = (r.num * (p.den : Int)) * (q.den : Int) := by
            rw [Int.mul_assoc, Int.mul_comm (q.den : Int) (p.den : Int), ← Int.mul_assoc]
  exact Int.eq_of_mul_eq_mul_right (by omega) e1

private theorem int_mul_swap_mid (a b c d : Int) : a * b * (c * d) = a * c * (b * d) := by
  calc
    a * b * (c * d) = a * (b * (c * d)) := Int.mul_assoc a b (c * d)
    _ = a * ((b * c) * d) := by rw [← Int.mul_assoc b c d]
    _ = a * ((c * b) * d) := by rw [Int.mul_comm b c]
    _ = a * (c * (b * d)) := by rw [Int.mul_assoc c b d]
    _ = a * c * (b * d) := (Int.mul_assoc a c (b * d)).symm

theorem add_eqv {p₁ p₂ q₁ q₂ : QRat} (hp : eqv p₁ p₂) (hq : eqv q₁ q₂) :
    eqv (add p₁ q₁) (add p₂ q₂) := by
  unfold eqv at hp hq
  unfold eqv add
  dsimp only []
  calc
    (p₁.num * (q₁.den : Int) + q₁.num * (p₁.den : Int)) * ((p₂.den * q₂.den : Nat) : Int)
        = (p₁.num * (p₂.den : Int)) * ((q₁.den : Int) * (q₂.den : Int)) +
          (q₁.num * (q₂.den : Int)) * ((p₁.den : Int) * (p₂.den : Int)) := by
          simp only [Int.ofNat_mul, Int.add_mul]
          have t1 : p₁.num * (q₁.den : Int) * ((p₂.den : Int) * (q₂.den : Int)) =
              (p₁.num * (p₂.den : Int)) * ((q₁.den : Int) * (q₂.den : Int)) :=
            int_mul_swap_mid p₁.num (q₁.den : Int) (p₂.den : Int) (q₂.den : Int)
          have t2 : q₁.num * (p₁.den : Int) * ((p₂.den : Int) * (q₂.den : Int)) =
              (q₁.num * (q₂.den : Int)) * ((p₁.den : Int) * (p₂.den : Int)) := by
            calc
              q₁.num * (p₁.den : Int) * ((p₂.den : Int) * (q₂.den : Int))
                  = q₁.num * (p₁.den : Int) * ((q₂.den : Int) * (p₂.den : Int)) := by
                    rw [Int.mul_comm (p₂.den : Int) (q₂.den : Int)]
              _ = (q₁.num * (q₂.den : Int)) * ((p₁.den : Int) * (p₂.den : Int)) :=
                    int_mul_swap_mid q₁.num (p₁.den : Int) (q₂.den : Int) (p₂.den : Int)
          rw [t1, t2]
    _ = (p₂.num * (p₁.den : Int)) * ((q₁.den : Int) * (q₂.den : Int)) +
        (q₂.num * (q₁.den : Int)) * ((p₁.den : Int) * (p₂.den : Int)) := by rw [hp, hq]
    _ = (p₂.num * (q₂.den : Int) + q₂.num * (p₂.den : Int)) * ((p₁.den * q₁.den : Nat) : Int) := by
          simp only [Int.ofNat_mul, Int.add_mul]
          have t1 : (p₂.num * (p₁.den : Int)) * ((q₁.den : Int) * (q₂.den : Int)) =
              p₂.num * (q₂.den : Int) * ((p₁.den : Int) * (q₁.den : Int)) := by
            calc
              (p₂.num * (p₁.den : Int)) * ((q₁.den : Int) * (q₂.den : Int))
                  = (p₂.num * (p₁.den : Int)) * ((q₂.den : Int) * (q₁.den : Int)) := by
                    rw [Int.mul_comm (q₁.den : Int) (q₂.den : Int)]
              _ = p₂.num * (q₂.den : Int) * ((p₁.den : Int) * (q₁.den : Int)) :=
                    (int_mul_swap_mid p₂.num (q₂.den : Int) (p₁.den : Int) (q₁.den : Int)).symm
          have t2 : (q₂.num * (q₁.den : Int)) * ((p₁.den : Int) * (p₂.den : Int)) =
              q₂.num * (p₂.den : Int) * ((p₁.den : Int) * (q₁.den : Int)) := by
            calc
              (q₂.num * (q₁.den : Int)) * ((p₁.den : Int) * (p₂.den : Int))
                  = (q₂.num * (q₁.den : Int)) * ((p₂.den : Int) * (p₁.den : Int)) := by
                    rw [Int.mul_comm (p₁.den : Int) (p₂.den : Int)]
              _ = q₂.num * (p₂.den : Int) * ((q₁.den : Int) * (p₁.den : Int)) :=
                    int_mul_swap_mid q₂.num (q₁.den : Int) (p₂.den : Int) (p₁.den : Int)
              _ = q₂.num * (p₂.den : Int) * ((p₁.den : Int) * (q₁.den : Int)) := by
                    rw [Int.mul_comm (q₁.den : Int) (p₁.den : Int)]
          rw [t1, t2]

theorem eqv_of_num_den_eq {p q : QRat} (hn : p.num = q.num) (hd : p.den = q.den) : eqv p q := by
  unfold eqv; rw [hn, hd]

theorem add_assoc_eqv (a b c : QRat) : eqv (add (add a b) c) (add a (add b c)) := by
  apply eqv_of_num_den_eq
  · dsimp only [add]
    simp only [Int.ofNat_mul, Int.add_mul, Int.mul_add]
    have t1 : a.num * (b.den : Int) * (c.den : Int) = a.num * ((b.den : Int) * (c.den : Int)) :=
      Int.mul_assoc _ _ _
    have t2 : b.num * (a.den : Int) * (c.den : Int) = b.num * (c.den : Int) * (a.den : Int) := by
      rw [Int.mul_assoc, Int.mul_comm (a.den : Int) (c.den : Int), ← Int.mul_assoc]
    have t3 : c.num * ((a.den : Int) * (b.den : Int)) = c.num * (b.den : Int) * (a.den : Int) := by
      rw [Int.mul_comm (a.den : Int) (b.den : Int), ← Int.mul_assoc]
    rw [t1, t2, t3, Int.add_assoc]
  · dsimp only [add]
    exact Nat.mul_assoc a.den b.den c.den

theorem sumList_append_eqv {α : Type} (xs ys : List α) (w : α → QRat) :
    eqv (sumList (xs ++ ys) w) (add (sumList xs w) (sumList ys w)) := by
  induction xs with
  | nil =>
    simp only [List.nil_append, sumList]
    apply eqv_of_num_den_eq
    · dsimp only [add, zero]; simp
    · dsimp only [add, zero]; simp
  | cons a as ih =>
    simp only [List.cons_append, sumList]
    exact eqv_trans (add_eqv (eqv_refl (w a)) ih) (eqv_symm (add_assoc_eqv (w a) _ _))

theorem lt_of_lt_of_eqv_right {p q₁ q₂ : QRat} (hl : lt p q₁) (he : eqv q₁ q₂) : lt p q₂ := by
  unfold eqv at he
  unfold lt at hl ⊢
  have hd1 : (0 : Int) < (q₁.den : Int) := Int.ofNat_lt.mpr q₁.den_pos
  have h1 : (p.num * (q₁.den : Int)) * (q₂.den : Int) < (q₁.num * (p.den : Int)) * (q₂.den : Int) :=
    Int.mul_lt_mul_of_pos_right hl (Int.ofNat_lt.mpr q₂.den_pos)
  have h2 : (q₁.num * (p.den : Int)) * (q₂.den : Int) = (q₂.num * (p.den : Int)) * (q₁.den : Int) := by
    calc
      (q₁.num * (p.den : Int)) * (q₂.den : Int)
          = (q₁.num * (q₂.den : Int)) * (p.den : Int) := by
            rw [Int.mul_assoc, Int.mul_comm (p.den : Int) (q₂.den : Int), ← Int.mul_assoc]
      _ = (q₂.num * (q₁.den : Int)) * (p.den : Int) := by rw [he]
      _ = (q₂.num * (p.den : Int)) * (q₁.den : Int) := by
            rw [Int.mul_assoc, Int.mul_comm (q₁.den : Int) (p.den : Int), ← Int.mul_assoc]
  have h4 : (p.num * (q₂.den : Int)) * (q₁.den : Int) = (p.num * (q₁.den : Int)) * (q₂.den : Int) := by
    rw [Int.mul_assoc, Int.mul_comm (q₂.den : Int) (q₁.den : Int), ← Int.mul_assoc]
  exact Classical.byContradiction fun hnot => by
    have hge : q₂.num * (p.den : Int) ≤ p.num * (q₂.den : Int) := by omega
    have hm : (q₂.num * (p.den : Int)) * (q₁.den : Int) ≤ (p.num * (q₂.den : Int)) * (q₁.den : Int) :=
      Int.mul_le_mul_of_nonneg_right hge (by omega)
    omega

theorem sumList_congr_eqv {α : Type} {xs : List α} {w₁ w₂ : α → QRat}
    (h : ∀ x ∈ xs, eqv (w₁ x) (w₂ x)) : eqv (sumList xs w₁) (sumList xs w₂) := by
  induction xs with
  | nil => exact eqv_refl zero
  | cons a as ih =>
    simp only [sumList]
    exact add_eqv (h a List.mem_cons_self) (ih (fun x hx => h x (List.mem_cons_of_mem a hx)))

end QRat

/-! ## 2. Corank-1 and Corank-2 Upper Möbius Formulas for Any `GeometricLattice` -/

namespace GeometricLattice

/-- For any coatom `x` (`rk x + 1 = rk ⊤`), `μ(x, ⊤) = -1` and `|μ(x, ⊤)| = 1`. -/
theorem mobius_coatom_top {α : Type} [DecidableEq α] (L : GeometricLattice α)
    {x : α} (hrk : L.rk x + 1 = L.rk L.top) :
    L.mobius x L.top = -1 ∧ L.absMobius x L.top = 1 := by
  have hne : x ≠ L.top := by intro h; rw [h] at hrk; omega
  have hmu : L.mobius x L.top = -1 := by
    rw [L.mobius_of_lt_upper (L.le_top x) hne]
    have hcongr : sumInt (L.intervalGt x L.top) (fun z => L.mobius z L.top) =
        sumInt L.elems (fun z => if z = L.top then L.mobius z L.top else 0) := by
      unfold intervalGt; rw [sumInt_filter_eq_sumInt_ite]
      apply sumInt_congr; intro z _
      by_cases hzt : z = L.top
      · subst hzt
        have hc : (L.leb x L.top && L.leb L.top L.top && !decide (L.top = x)) = true := by
          simp [L.le_top x, L.le_refl L.top, Ne.symm hne]
        simp [hc]
      · have hnc : (L.leb x z && L.leb z L.top && !decide (z = x)) = false := by
          apply Bool.eq_false_iff.mpr
          intro ht
          rcases (Bool.and_eq_true _ _).mp ht with ⟨h12, hzx_b⟩
          rcases (Bool.and_eq_true _ _).mp h12 with ⟨hxz, hzt_le⟩
          have hzx : x ≠ z := by intro h; subst h; simp at hzx_b
          have h1 := L.lt_rk hxz hzx
          have h2 := L.lt_rk hzt_le hzt
          omega
        simp [hzt, hnc]
    rw [hcongr, sumInt_single_hit L.nodup_elems (L.mem_elems L.top)]
    simp [L.mobius_self]
  exact ⟨hmu, by unfold absMobius; rw [hmu]; rfl⟩

theorem upperMobiusRankSum_coatom {α : Type} [DecidableEq α] (L : GeometricLattice α)
    {k : Nat} (hk : k + 1 = L.rk L.top) :
    L.upperMobiusRankSum k = (L.rankLevel k).length := by
  unfold upperMobiusRankSum
  rw [length_eq_sumNat_ones]
  apply sumNat_congr
  intro y hy
  unfold rankLevel at hy
  have hry : L.rk y = k := of_decide_eq_true ((mem_filter_iff_prop _ _ _).mp hy).2
  exact (L.mobius_coatom_top (by omega)).2

/-- For any corank-2 element `x` (`rk x + 2 = rk ⊤`), `|μ(x, ⊤)| = |upperCovers x| - 1`. -/
theorem absMobius_corank2_top {α : Type} [DecidableEq α] (L : GeometricLattice α)
    {x : α} (hrk : L.rk x + 2 = L.rk L.top) :
    L.absMobius x L.top = (L.upperCovers x).length - 1 := by
  have hne : x ≠ L.top := by intro h; rw [h] at hrk; omega
  rcases L.exists_step (L.le_top x) (by omega) with ⟨c₀, hxc₀, _, _, hrc₀⟩
  have hc₀_mem : c₀ ∈ L.upperCovers x := by
    unfold upperCovers; rw [mem_filter_iff_prop]
    exact ⟨L.mem_elems c₀, Bool.and_eq_true _ _ |>.mpr ⟨hxc₀, decide_eq_true hrc₀⟩⟩
  have hcov_pos : 1 ≤ (L.upperCovers x).length := by
    rw [length_eq_sumNat_ones]
    exact mem_sumNat_le hc₀_mem (fun _ => 1)
  have hsplit := sumInt_filter_split (L.intervalGt x L.top) (fun z => decide (z = L.top))
    (fun z => L.mobius z L.top)
  have htop_mem : L.top ∈ L.intervalGt x L.top := by
    unfold intervalGt; rw [mem_filter_iff_prop]
    exact ⟨L.mem_elems L.top, by simp [L.le_top x, L.le_refl L.top, Ne.symm hne]⟩
  have hhit : sumInt ((L.intervalGt x L.top).filter (fun z => decide (z = L.top)))
      (fun z => L.mobius z L.top) = 1 := by
    rw [sumInt_filter_eq_sumInt_ite]
    have hc : sumInt (L.intervalGt x L.top)
        (fun z => if decide (z = L.top) = true then L.mobius z L.top else 0) =
        sumInt (L.intervalGt x L.top) (fun z => if z = L.top then L.mobius z L.top else 0) := by
      apply sumInt_congr; intro z _; by_cases h : z = L.top <;> simp [h]
    rw [hc]
    exact (sumInt_single_hit (nodup_filter _ L.nodup_elems) htop_mem
      (fun z => L.mobius z L.top)).trans (L.mobius_self L.top)
  have hrest_eq : (L.intervalGt x L.top).filter (fun z => !decide (z = L.top)) = L.upperCovers x := by
    unfold intervalGt upperCovers
    apply filter_filter_eq L.elems
    intro z _
    by_cases hxz : L.leb x z = true
    · by_cases hzt : z = L.top
      · subst hzt
        have hrf : decide (L.rk L.top = L.rk x + 1) = false := decide_eq_false (by omega)
        simp [hxz, L.le_refl L.top, hrf]
      · by_cases hzx : z = x
        · subst hzx
          have hrf : decide (L.rk z = L.rk z + 1) = false := decide_eq_false (by omega)
          simp [hrf]
        · have h1 := L.lt_rk hxz (Ne.symm hzx)
          have h2 := L.lt_rk (L.le_top z) hzt
          have hr_eq : L.rk z = L.rk x + 1 := by omega
          simp [hxz, L.le_top z, hzx, hzt, hr_eq]
    · have hxz_f : L.leb x z = false := Bool.eq_false_iff.mpr hxz
      simp [hxz_f]
  have hrest_val : sumInt (L.upperCovers x) (fun z => L.mobius z L.top) =
      - ((L.upperCovers x).length : Int) := by
    have hall : ∀ z ∈ L.upperCovers x, L.mobius z L.top = -1 := by
      intro z hz
      unfold upperCovers at hz
      have hrz : L.rk z = L.rk x + 1 :=
        of_decide_eq_true ((Bool.and_eq_true _ _).mp ((mem_filter_iff_prop _ _ _).mp hz).2).2
      exact (L.mobius_coatom_top (by omega)).1
    rw [sumInt_congr hall, sumInt_const_neg_one]
  have hmu : L.mobius x L.top = ((L.upperCovers x).length : Int) - 1 := by
    rw [L.mobius_of_lt_upper (L.le_top x) hne]
    rw [← hsplit, hhit, hrest_eq, hrest_val]
    omega
  unfold absMobius
  rw [hmu]
  omega

end GeometricLattice

/-! ## 3. Parametric Matroid Family A: `directSumColoop r₀ m` (`U_{r₀, m} ⊕ U_{1, 1}`) -/

/-- Concave integer cap `capNat x r := if x ≤ r then x else r`. -/
def capNat (x r : Nat) : Nat := if x ≤ r then x else r

theorem capNat_of_le {x r : Nat} (h : x ≤ r) : capNat x r = x := by
  unfold capNat; split <;> omega

theorem capNat_of_ge {x r : Nat} (h : r ≤ x) : capNat x r = r := by
  unfold capNat; split <;> omega

theorem capNat_succ_pos {r : Nat} (hr : 2 ≤ r) (x : Nat) : 1 ≤ capNat (x + 1) r := by
  unfold capNat; split <;> omega

theorem capNat_step_bounds (x r : Nat) :
    capNat x r ≤ capNat (x + 1) r ∧ capNat (x + 1) r ≤ capNat x r + 1 := by
  unfold capNat; split <;> split <;> omega

theorem capNat_submod {r cI cU c₁ c₂ : Nat}
    (hsum : cI + cU = c₁ + c₂) (h1 : cI ≤ c₁) (h2 : cI ≤ c₂) :
    capNat cI r + capNat cU r ≤ capNat c₁ r + capNat c₂ r := by
  unfold capNat; split <;> split <;> split <;> split <;> omega

def directSumColoopRank (r₀ : Nat) {m : Nat} : Sub (m + 1) → Nat
  | .cons b₀ S => (if b₀ then 1 else 0) + capNat (Sub.card S) r₀

def directSumColoop (r₀ m : Nat) (hr₀ : 2 ≤ r₀) : SimpleMatroid (m + 1) where
  r := directSumColoopRank r₀
  r_empty := by
    change 0 + capNat (Sub.card (Sub.empty m)) r₀ = 0
    rw [Sub.card_empty, capNat_of_le (Nat.zero_le r₀)]
  r_singleton := by
    rintro ⟨k, hk⟩
    cases k with
    | zero =>
      change 1 + capNat (Sub.card (Sub.empty m)) r₀ = 1
      rw [Sub.card_empty, capNat_of_le (Nat.zero_le r₀)]
    | succ k =>
      change 0 + capNat (Sub.card (Sub.singleton ⟨k, Nat.lt_of_succ_lt_succ hk⟩)) r₀ = 1
      rw [Sub.card_singleton, capNat_of_le (by omega)]
  r_pair := by
    rintro ⟨k₁, h₁⟩ ⟨k₂, h₂⟩ hne
    cases k₁ with
    | zero =>
      cases k₂ with
      | zero => exact absurd rfl hne
      | succ k₂ =>
        change 1 + capNat (Sub.card (Sub.singleton ⟨k₂, Nat.lt_of_succ_lt_succ h₂⟩)) r₀ = 2
        rw [Sub.card_singleton, capNat_of_le (by omega)]
    | succ k₁ =>
      cases k₂ with
      | zero =>
        change 1 + capNat (Sub.card (Sub.insert ⟨k₁, Nat.lt_of_succ_lt_succ h₁⟩ (Sub.empty m))) r₀ = 2
        have hc := Sub.card_singleton (⟨k₁, Nat.lt_of_succ_lt_succ h₁⟩ : Fin m)
        unfold Sub.singleton at hc
        rw [hc, capNat_of_le (by omega)]
      | succ k₂ =>
        have hne' : (⟨k₁, Nat.lt_of_succ_lt_succ h₁⟩ : Fin m) ≠ ⟨k₂, Nat.lt_of_succ_lt_succ h₂⟩ := by
          intro h; cases h; exact hne rfl
        have hmem_f : Sub.mem ⟨k₁, Nat.lt_of_succ_lt_succ h₁⟩
            (Sub.singleton ⟨k₂, Nat.lt_of_succ_lt_succ h₂⟩) = false := by
          rw [Sub.mem_singleton]; simp [hne']
        change 0 + capNat (Sub.card (Sub.insert ⟨k₁, Nat.lt_of_succ_lt_succ h₁⟩
            (Sub.singleton ⟨k₂, Nat.lt_of_succ_lt_succ h₂⟩))) r₀ = 2
        rw [Sub.card_insert_of_not_mem _ _ hmem_f, Sub.card_singleton, capNat_of_le hr₀]
  r_insert_bounds := by
    intro X idx_full
    rcases X with _ | ⟨b₀, S⟩
    rcases idx_full with ⟨k, hk⟩
    cases k with
    | zero =>
      change ((if b₀ then 1 else 0) + capNat (Sub.card S) r₀ ≤ 1 + capNat (Sub.card S) r₀) ∧
             (1 + capNat (Sub.card S) r₀ ≤ ((if b₀ then 1 else 0) + capNat (Sub.card S) r₀) + 1)
      cases b₀ <;> simp <;> omega
    | succ k =>
      let idx : Fin m := ⟨k, Nat.lt_of_succ_lt_succ hk⟩
      change ((if b₀ then 1 else 0) + capNat (Sub.card S) r₀ ≤
              (if b₀ then 1 else 0) + capNat (Sub.card (Sub.insert idx S)) r₀) ∧
             ((if b₀ then 1 else 0) + capNat (Sub.card (Sub.insert idx S)) r₀ ≤
              ((if b₀ then 1 else 0) + capNat (Sub.card S) r₀) + 1)
      have hb := capNat_step_bounds (Sub.card S) r₀
      cases hm : Sub.mem idx S
      · rw [Sub.card_insert_of_not_mem idx S hm]
        cases b₀ <;> simp <;> omega
      · rw [Sub.insert_eq_of_mem hm]
        cases b₀ <;> simp <;> omega
  r_submod := by
    intro X₁ X₂
    rcases X₁ with _ | ⟨b₁, S₁⟩
    rcases X₂ with _ | ⟨b₂, S₂⟩
    simp only [Sub.inter, Sub.union, directSumColoopRank]
    have hcard := Sub.card_inter_add_union S₁ S₂
    have hle1 := Sub.card_mono (Sub.inter_subset_left S₁ S₂)
    have hle2 := Sub.card_mono (Sub.inter_subset_right S₁ S₂)
    have hsm := capNat_submod (r := r₀) hcard hle1 hle2
    cases b₁ <;> cases b₂ <;> simp <;> omega

/-! ### Counterexample on `L10 = B_1 × M_3` (`|L| = 10`, Rank 3): Lower-Möbius Suboptimality -/

def M10 : SimpleMatroid 4 := directSumColoop 2 3 (by decide)
def L10 : GeometricLattice M10.Flat := M10.defaultGeometricLattice

/-- Rank-uniform LYM weight `1 / W_{rk x}` on `L10` (`W = [1, 4, 4, 1]`). -/
def wUnif10 (x : M10.Flat) : QRat :=
  let k := L10.rk x
  if k = 1 ∨ k = 2 then QRat.mkNat 1 4 (by decide)
  else QRat.mkNat 1 1 (by decide)

/-- Rank-normalized lower-Möbius weight `|μ(⊥, x)| / |w_{rk x}(L10)|` on `L10`. -/
def wLow10 (x : M10.Flat) : QRat :=
  let k := L10.rk x
  let d := L10.absWhitney1 k
  if h : 0 < d then QRat.mkNat (L10.absMobius L10.bot x) d h
  else QRat.zero

/-- Symmetric chain decomposition indicator weight on `L10.maxChains` realizing `wUnif10`. -/
def scdChainWeight10 (C : List M10.Flat) : Nat :=
  let s1 : Sub 4 := .cons false (.cons true (.cons false (.cons false .nil)))
  let s123 : Sub 4 := .cons false (.cons true (.cons true (.cons true .nil)))
  let s2 : Sub 4 := .cons false (.cons false (.cons true (.cons false .nil)))
  let sp2 : Sub 4 := .cons true (.cons false (.cons true (.cons false .nil)))
  let s3 : Sub 4 := .cons false (.cons false (.cons false (.cons true .nil)))
  let sp3 : Sub 4 := .cons true (.cons false (.cons false (.cons true .nil)))
  let sp : Sub 4 := .cons true (.cons false (.cons false (.cons false .nil)))
  let sp1 : Sub 4 := .cons true (.cons true (.cons false (.cons false .nil)))
  let raws := C.map Subtype.val
  if (s1 ∈ raws ∧ s123 ∈ raws) ∨ (s2 ∈ raws ∧ sp2 ∈ raws) ∨
     (s3 ∈ raws ∧ sp3 ∈ raws) ∨ (sp ∈ raws ∧ sp1 ∈ raws) then 1 else 0

theorem wUnif10_is_valid_lym {A : List M10.Flat} (hA : L10.IsAntichain A) :
    QRat.le (QRat.sumList A wUnif10) QRat.one := by
  have hpt : ∀ x ∈ L10.elems, QRat.eqv (wUnif10 x)
      (QRat.mkNat (sumNat L10.maxChains (fun C => if x ∈ C then scdChainWeight10 C else 0)) 4 (by decide)) := by
    decide
  have heqv1 : QRat.eqv (QRat.sumList A wUnif10)
      (QRat.sumList A (fun x =>
        QRat.mkNat (sumNat L10.maxChains (fun C => if x ∈ C then scdChainWeight10 C else 0)) 4 (by decide))) :=
    QRat.sumList_congr_eqv (fun x _ => hpt x (L10.mem_elems x))
  have heqv2 := QRat.sumList_const_den A
    (fun x => sumNat L10.maxChains (fun C => if x ∈ C then scdChainWeight10 C else 0)) 4 (by decide)
  apply QRat.le_of_eqv_left (QRat.eqv_trans heqv1 heqv2)
  have htot : sumNat L10.maxChains scdChainWeight10 = 4 := by decide
  have hlym := L10.weighted_chain_lym_nat scdChainWeight10 hA
  rw [htot] at hlym
  dsimp only [QRat.le, QRat.mkNat, QRat.one]
  omega

/--
**Theorem (`lower_mobius_suboptimal_on_L10`):**
On the 10-element modular geometric lattice `L10 = B_1 × M_3`:
1. `wUnif10` (`1 / W_{rk x}`) is a valid tight LYM weighting (`∀ A, sumList A wUnif10 ≤ 1`, and `= 1` on `L_2`);
2. `L10.lubellWeight` is a valid tight LYM weighting;
3. Yet the rank-normalized lower-Möbius weighting `wLow10` (`|μ(⊥, x)| / |w_{rk x}|`) has strictly
   smaller minimum weight on proper flats (`1/5 < 2/9 < 1/4`), yielding a strictly weaker Sperner
   cardinality bound (`5` instead of the sharp width `4`), and fails pointwise dominance.
-/
theorem lower_mobius_suboptimal_on_L10 :
    L10.elems.length = 10 ∧
    L10.rk L10.top = 3 ∧
    (∀ A : List M10.Flat, L10.IsAntichain A → QRat.le (QRat.sumList A wUnif10) QRat.one) ∧
    QRat.eqv (QRat.sumList (L10.rankLevel 2) wUnif10) QRat.one ∧
    (∀ x ∈ L10.properElems, QRat.eqv (wUnif10 x) (QRat.mkNat 1 4 (by decide))) ∧
    (∀ x ∈ L10.properElems, QRat.le (QRat.mkNat 2 9 (by decide)) (L10.lubellWeight x)) ∧
    (∃ x₀ ∈ L10.properElems,
      QRat.eqv (wLow10 x₀) (QRat.mkNat 1 5 (by decide)) ∧
      QRat.lt (wLow10 x₀) (L10.lubellWeight x₀) ∧
      QRat.lt (L10.lubellWeight x₀) (wUnif10 x₀)) ∧
    (∃ x₁ ∈ L10.properElems, QRat.lt (wUnif10 x₁) (wLow10 x₁)) := by
  refine ⟨by decide, by decide, fun A hA => wUnif10_is_valid_lym hA,
          by decide, by decide, by decide, by decide, by decide⟩

/-! ### Counterexample on `L46 = L(U_{1,1} ⊕ U_{3,6})` (`|L| = 46`, Rank 4): Two-Sided |μ| Violation -/

def M46 : SimpleMatroid 7 := directSumColoop 3 6 (by decide)

def rawFlats46 : List (Sub 7) :=
  let subs6 := (Sub.allSubs 6).filter (fun S => decide (Sub.card S ≤ 2) || decide (S = Sub.univ 6))
  subs6.map (Sub.cons false) ++ subs6.map (Sub.cons true)

theorem nodup_rawFlats46 : NoDup rawFlats46 := by
  unfold rawFlats46
  let subs6 := (Sub.allSubs 6).filter (fun S => decide (Sub.card S ≤ 2) || decide (S = Sub.univ 6))
  have hnd6 : NoDup subs6 := nodup_filter _ (Sub.nodup_allSubs 6)
  exact GeometricLattice.nodup_append_of_disjoint
    (Sub.nodup_map_sub_cons false hnd6)
    (Sub.nodup_map_sub_cons true hnd6)
    (fun z h1 h2 => by
      rcases List.mem_map.mp h1 with ⟨_, _, rfl⟩
      rcases List.mem_map.mp h2 with ⟨_, _, heq⟩
      cases heq)

theorem rawFlats46_check_all :
    (Sub.allSubs 7).all (fun S => decide (S ∈ rawFlats46) == decide (M46.IsFlat S)) = true := by
  decide

theorem mem_rawFlats46_iff (S : Sub 7) : S ∈ rawFlats46 ↔ M46.IsFlat S := by
  have hall := List.all_eq_true.mp rawFlats46_check_all S (Sub.mem_allSubs S)
  have hbeq : decide (S ∈ rawFlats46) = decide (M46.IsFlat S) := of_decide_eq_true (by
    cases h1 : decide (S ∈ rawFlats46) <;> cases h2 : decide (M46.IsFlat S) <;> simp_all)
  constructor
  · intro h; exact of_decide_eq_true (hbeq ▸ decide_eq_true h)
  · intro h; exact of_decide_eq_true (hbeq.symm ▸ decide_eq_true h)

def L46 : GeometricLattice M46.Flat :=
  M46.toGeometricLattice rawFlats46 nodup_rawFlats46 mem_rawFlats46_iff

/-- Rank-normalized two-sided Möbius weighting `|μ(⊥, x) μ(x, ⊤)| / ∑_{rk y = rk x} |μ(⊥, y) μ(y, ⊤)|`. -/
def wTwoSided46 (x : M46.Flat) : QRat :=
  let k := L46.rk x
  let d := L46.twoSidedMobiusRankSum k
  if h : 0 < d then QRat.mkNat (L46.absMobius L46.bot x * L46.absMobius x L46.top) d h
  else QRat.zero

def antichain46 : List M46.Flat :=
  L46.elems.filter (fun x =>
    (decide (L46.rk x = 2) && Sub.mem ⟨0, Nat.zero_lt_succ 6⟩ x.1) ||
    (decide (L46.rk x = 3) && !Sub.mem ⟨0, Nat.zero_lt_succ 6⟩ x.1))

/--
**Theorem (`two_sided_mobius_lym_fails_on_L46`):**
On the 46-element rank-4 geometric lattice `L46 = L(U_{1,1} ⊕ U_{3,6})`, the 7-element antichain
`antichain46` achieves rank-normalized two-sided Möbius weight `66 / 65 > 1`.
-/
theorem two_sided_mobius_lym_fails_on_L46 :
    L46.elems.length = 46 ∧
    L46.rk L46.top = 4 ∧
    L46.IsAntichain antichain46 ∧
    antichain46.length = 7 ∧
    (∀ k ≤ 4, 0 < L46.twoSidedMobiusRankSum k) ∧
    QRat.eqv (QRat.sumList antichain46 wTwoSided46) (QRat.mkNat 66 65 (by decide)) ∧
    QRat.lt QRat.one (QRat.sumList antichain46 wTwoSided46) := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-! ## 4. Parametric Matroid Family B: `parallelConnUniform r₀ a b` (`U_{r₀, a+1} ⊕_{e₀} U_{r₀, b+1}`) -/

namespace Sub

/-- Split `Sub (a + b)` by recursing on `b` (matching `Nat.add` definitionally!). -/
def split : {a b : Nat} → Sub (a + b) → Sub a × Sub b
  | _, 0, S => (S, .nil)
  | a, b + 1, .cons x rest =>
    let p := split (a := a) (b := b) rest
    (p.1, .cons x p.2)

def append : {a b : Nat} → Sub a → Sub b → Sub (a + b)
  | _, 0, SA, .nil => SA
  | _, _ + 1, SA, .cons x restB => .cons x (append SA restB)

theorem split_append : {a b : Nat} → (SA : Sub a) → (SB : Sub b) →
    split (append SA SB) = (SA, SB)
  | _, 0, _, .nil => rfl
  | _, _ + 1, SA, .cons _ restB => by simp [append, split, split_append SA restB]

theorem split_append_fst {a b : Nat} (SA : Sub a) (SB : Sub b) :
    (split (append SA SB)).1 = SA := by
  rw [split_append]

theorem split_append_snd {a b : Nat} (SA : Sub a) (SB : Sub b) :
    (split (append SA SB)).2 = SB := by
  rw [split_append]

theorem append_split {a b : Nat} (S : Sub (a + b)) :
    append (split S).1 (split S).2 = S := by
  induction b with
  | zero => rfl
  | succ b ih =>
    rcases S with _ | ⟨x, rest⟩
    simp only [split, append]
    rw [ih rest]

theorem split_empty : {a b : Nat} → split (empty (a + b)) = (empty a, empty b)
  | _, 0 => rfl
  | a, b + 1 => by
    change ((split (empty (a + b))).1, cons false (split (empty (a + b))).2) =
      (empty a, cons false (empty b))
    rw [split_empty (a := a) (b := b)]

theorem split_inter : {a b : Nat} → (S T : Sub (a + b)) →
    split (inter S T) = (inter (split S).1 (split T).1, inter (split S).2 (split T).2)
  | _, 0, _, _ => rfl
  | a, b + 1, .cons b₁ r₁, .cons b₂ r₂ => by
    simp only [inter, split]
    rw [split_inter (a := a) (b := b) r₁ r₂]

theorem split_union : {a b : Nat} → (S T : Sub (a + b)) →
    split (union S T) = (union (split S).1 (split T).1, union (split S).2 (split T).2)
  | _, 0, _, _ => rfl
  | a, b + 1, .cons b₁ r₁, .cons b₂ r₂ => by
    simp only [union, split]
    rw [split_union (a := a) (b := b) r₁ r₂]

theorem card_append : {a b : Nat} → (SA : Sub a) → (SB : Sub b) →
    card (append SA SB) = card SA + card SB
  | _, 0, _, .nil => by simp [append, card]
  | _, _ + 1, SA, .cons x restB => by
    simp only [append, card, card_append SA restB]
    omega

theorem card_split_sum {a b : Nat} (S : Sub (a + b)) :
    card (split S).1 + card (split S).2 = card S := by
  have h := card_append (split S).1 (split S).2
  rw [append_split] at h
  exact h.symm

theorem split_insert_step : {a b : Nat} → (S : Sub (a + b)) → (i : Fin (a + b)) →
    ((card (split (insert i S)).1 = card (split S).1 ∧
      (card (split (insert i S)).2 = card (split S).2 ∨
       card (split (insert i S)).2 = card (split S).2 + 1)) ∨
     ((card (split (insert i S)).1 = card (split S).1 + 1) ∧
      card (split (insert i S)).2 = card (split S).2))
  | _, 0, S, i => by
    dsimp only [split, card]
    cases hm : mem i S
    · exact Or.inr ⟨card_insert_of_not_mem i S hm, rfl⟩
    · rw [insert_eq_of_mem hm]; exact Or.inl ⟨rfl, Or.inl rfl⟩
  | a, b + 1, .cons x rest, ⟨0, _⟩ => by
    change (card (split rest).1 = card (split rest).1 ∧
            ((if true then 1 else 0) + card (split rest).2 = (if x then 1 else 0) + card (split rest).2 ∨
             (if true then 1 else 0) + card (split rest).2 = ((if x then 1 else 0) + card (split rest).2) + 1)) ∨ _
    cases x
    · exact Or.inl ⟨rfl, Or.inr (by simp; omega)⟩
    · exact Or.inl ⟨rfl, Or.inl rfl⟩
  | a, b + 1, .cons x rest, ⟨k + 1, hk⟩ => by
    have ih := split_insert_step (a := a) (b := b) rest ⟨k, Nat.lt_of_succ_lt_succ hk⟩
    change ((card (split (insert ⟨k, _⟩ rest)).1 = card (split rest).1 ∧
             ((if x then 1 else 0) + card (split (insert ⟨k, _⟩ rest)).2 =
              (if x then 1 else 0) + card (split rest).2 ∨
              (if x then 1 else 0) + card (split (insert ⟨k, _⟩ rest)).2 =
              ((if x then 1 else 0) + card (split rest).2) + 1)) ∨
            (card (split (insert ⟨k, _⟩ rest)).1 = card (split rest).1 + 1 ∧
             (if x then 1 else 0) + card (split (insert ⟨k, _⟩ rest)).2 =
             (if x then 1 else 0) + card (split rest).2))
    rcases ih with ⟨h1, h2 | h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1, Or.inl (by omega)⟩
    · exact Or.inl ⟨h1, Or.inr (by omega)⟩
    · exact Or.inr ⟨h1, by omega⟩

theorem subset_append : {a b : Nat} → (SA TA : Sub a) → (SB TB : Sub b) →
    subset (append SA SB) (append TA TB) = (subset SA TA && subset SB TB)
  | _, 0, SA, TA, .nil, .nil => by simp [append, subset]
  | _, _ + 1, SA, TA, .cons x rB, .cons y tB => by
    simp only [append, subset, subset_append SA TA rB tB]
    cases (!x || y) <;> cases subset SA TA <;> cases subset rB tB <;> rfl

end Sub

/-- Parallel-connection rank formula. -/
def pcRankFormula (r₀ ca cb z : Nat) : Nat :=
  let u := capNat ca r₀ + capNat cb r₀ + z
  let v := capNat (ca + 1) r₀ + capNat (cb + 1) r₀ - 1
  if u ≤ v then u else v

theorem pcRankFormula_v_le_u1 {r₀ : Nat} (hr₀ : 2 ≤ r₀) (ca cb : Nat) :
    capNat (ca + 1) r₀ + capNat (cb + 1) r₀ - 1 ≤ capNat ca r₀ + capNat cb r₀ + 1 := by
  have ha := capNat_step_bounds ca r₀
  have hb := capNat_step_bounds cb r₀
  have hp := capNat_succ_pos hr₀ ca
  omega

theorem pcRankFormula_z1 {r₀ : Nat} (hr₀ : 2 ≤ r₀) (ca cb : Nat) :
    pcRankFormula r₀ ca cb 1 = capNat (ca + 1) r₀ + capNat (cb + 1) r₀ - 1 := by
  have hle := pcRankFormula_v_le_u1 hr₀ ca cb
  unfold pcRankFormula; dsimp only []; split <;> omega

theorem pcRankFormula_z0_of_lt {r₀ ca cb : Nat} (hr₀ : 2 ≤ r₀) (h : ca < r₀ ∨ cb < r₀) :
    pcRankFormula r₀ ca cb 0 = capNat ca r₀ + capNat cb r₀ := by
  have huv : capNat ca r₀ + capNat cb r₀ + 0 ≤ capNat (ca + 1) r₀ + capNat (cb + 1) r₀ - 1 := by
    unfold capNat; split <;> split <;> split <;> split <;> omega
  unfold pcRankFormula; dsimp only []; split <;> omega

theorem pcRankFormula_z0_of_ge {r₀ ca cb : Nat} (hr₀ : 2 ≤ r₀) (ha : r₀ ≤ ca) (hb : r₀ ≤ cb) :
    pcRankFormula r₀ ca cb 0 = 2 * r₀ - 1 := by
  unfold pcRankFormula; dsimp only []
  rw [capNat_of_ge ha, capNat_of_ge hb, capNat_of_ge (by omega), capNat_of_ge (by omega)]
  split <;> omega

theorem pcRankFormula_le_left (r₀ ca cb z : Nat) :
    pcRankFormula r₀ ca cb z ≤ capNat ca r₀ + capNat cb r₀ + z := by
  unfold pcRankFormula; dsimp only []; split <;> omega

theorem pcRankFormula_le_right (r₀ ca cb z : Nat) :
    pcRankFormula r₀ ca cb z ≤ capNat (ca + 1) r₀ + capNat (cb + 1) r₀ - 1 := by
  unfold pcRankFormula; dsimp only []; split <;> omega

theorem pcRankFormula_z_step {r₀ : Nat} (hr₀ : 2 ≤ r₀) (ca cb : Nat) (b₀ : Bool) :
    pcRankFormula r₀ ca cb (if b₀ then 1 else 0) ≤ pcRankFormula r₀ ca cb 1 ∧
    pcRankFormula r₀ ca cb 1 ≤ pcRankFormula r₀ ca cb (if b₀ then 1 else 0) + 1 := by
  have ha := capNat_step_bounds ca r₀
  have hb := capNat_step_bounds cb r₀
  have hp := capNat_succ_pos hr₀ ca
  cases b₀
  · change pcRankFormula r₀ ca cb 0 ≤ pcRankFormula r₀ ca cb 1 ∧
           pcRankFormula r₀ ca cb 1 ≤ pcRankFormula r₀ ca cb 0 + 1
    unfold pcRankFormula; dsimp only []; split <;> split <;> omega
  · change pcRankFormula r₀ ca cb 1 ≤ pcRankFormula r₀ ca cb 1 ∧
           pcRankFormula r₀ ca cb 1 ≤ pcRankFormula r₀ ca cb 1 + 1
    exact ⟨Nat.le_refl _, by omega⟩

theorem pcRankFormula_step_left {r₀ : Nat} (hr₀ : 2 ≤ r₀) (ca cb z : Nat) :
    pcRankFormula r₀ ca cb z ≤ pcRankFormula r₀ (ca + 1) cb z ∧
    pcRankFormula r₀ (ca + 1) cb z ≤ pcRankFormula r₀ ca cb z + 1 := by
  have ha1 := capNat_step_bounds ca r₀
  have ha2 := capNat_step_bounds (ca + 1) r₀
  have hp1 := capNat_succ_pos hr₀ ca
  unfold pcRankFormula; dsimp only []; split <;> split <;> omega

theorem pcRankFormula_step_right {r₀ : Nat} (hr₀ : 2 ≤ r₀) (ca cb z : Nat) :
    pcRankFormula r₀ ca cb z ≤ pcRankFormula r₀ ca (cb + 1) z ∧
    pcRankFormula r₀ ca (cb + 1) z ≤ pcRankFormula r₀ ca cb z + 1 := by
  have hb1 := capNat_step_bounds cb r₀
  have hb2 := capNat_step_bounds (cb + 1) r₀
  have hp1 := capNat_succ_pos hr₀ cb
  unfold pcRankFormula; dsimp only []; split <;> split <;> omega

private theorem pcRankFormula_submod_z {r₀ : Nat} (hr₀ : 2 ≤ r₀)
    {cAI cAU cA1 cA2 cBI cBU cB1 cB2 zI zU z1 z2 : Nat}
    (hcA : cAI + cAU = cA1 + cA2) (hlA1 : cAI ≤ cA1) (hlA2 : cAI ≤ cA2)
    (hcB : cBI + cBU = cB1 + cB2) (hlB1 : cBI ≤ cB1) (hlB2 : cBI ≤ cB2)
    (hz_sum : zI + zU = z1 + z2)
    (hz1 : z1 = 0 → zI = 0) (hz2 : z2 = 0 → zI = 0)
    (hz1_le : z1 ≤ 1) (hz2_le : z2 ≤ 1) :
    pcRankFormula r₀ cAI cBI zI + pcRankFormula r₀ cAU cBU zU ≤
      pcRankFormula r₀ cA1 cB1 z1 + pcRankFormula r₀ cA2 cB2 z2 := by
  have hsmA0 := capNat_submod (r := r₀) hcA hlA1 hlA2
  have hsmA1 := capNat_submod (r := r₀)
    (by omega : (cAI + 1) + (cAU + 1) = (cA1 + 1) + (cA2 + 1)) (by omega) (by omega)
  have hsmA01 := capNat_submod (r := r₀)
    (by omega : cAI + (cAU + 1) = cA1 + (cA2 + 1)) hlA1 (by omega)
  have hsmA10 := capNat_submod (r := r₀)
    (by omega : cAI + (cAU + 1) = (cA1 + 1) + cA2) (by omega) hlA2
  have hsmB0 := capNat_submod (r := r₀) hcB hlB1 hlB2
  have hsmB1 := capNat_submod (r := r₀)
    (by omega : (cBI + 1) + (cBU + 1) = (cB1 + 1) + (cB2 + 1)) (by omega) (by omega)
  have hsmB01 := capNat_submod (r := r₀)
    (by omega : cBI + (cBU + 1) = cB1 + (cB2 + 1)) hlB1 (by omega)
  have hsmB10 := capNat_submod (r := r₀)
    (by omega : cBI + (cBU + 1) = (cB1 + 1) + cB2) (by omega) hlB2
  have hv1 := pcRankFormula_v_le_u1 hr₀ cA1 cB1
  have hv2 := pcRankFormula_v_le_u1 hr₀ cA2 cB2
  have hpI := capNat_succ_pos hr₀ cAI
  have hpU := capNat_succ_pos hr₀ cAU
  have hp1 := capNat_succ_pos hr₀ cA1
  have hp2 := capNat_succ_pos hr₀ cA2
  have lI1 := pcRankFormula_le_left r₀ cAI cBI zI
  have lI2 := pcRankFormula_le_right r₀ cAI cBI zI
  have lU1 := pcRankFormula_le_left r₀ cAU cBU zU
  have lU2 := pcRankFormula_le_right r₀ cAU cBU zU
  conv => rhs; unfold pcRankFormula; dsimp only []
  split <;> split <;> omega

theorem pcRankFormula_submod {r₀ : Nat} (hr₀ : 2 ≤ r₀)
    {cAI cAU cA1 cA2 cBI cBU cB1 cB2 : Nat}
    (hcA : cAI + cAU = cA1 + cA2) (hlA1 : cAI ≤ cA1) (hlA2 : cAI ≤ cA2)
    (hcB : cBI + cBU = cB1 + cB2) (hlB1 : cBI ≤ cB1) (hlB2 : cBI ≤ cB2)
    (b₁ b₂ : Bool) :
    pcRankFormula r₀ cAI cBI (if (b₁ && b₂) then 1 else 0) +
      pcRankFormula r₀ cAU cBU (if (b₁ || b₂) then 1 else 0) ≤
    pcRankFormula r₀ cA1 cB1 (if b₁ then 1 else 0) +
      pcRankFormula r₀ cA2 cB2 (if b₂ then 1 else 0) := by
  cases b₁ <;> cases b₂
  · exact pcRankFormula_submod_z (zI := 0) (zU := 0) (z1 := 0) (z2 := 0)
      hr₀ hcA hlA1 hlA2 hcB hlB1 hlB2 rfl (fun _ => rfl) (fun _ => rfl) (by decide) (by decide)
  · exact pcRankFormula_submod_z (zI := 0) (zU := 1) (z1 := 0) (z2 := 1)
      hr₀ hcA hlA1 hlA2 hcB hlB1 hlB2 rfl (fun _ => rfl) (by omega) (by decide) (by decide)
  · exact pcRankFormula_submod_z (zI := 0) (zU := 1) (z1 := 1) (z2 := 0)
      hr₀ hcA hlA1 hlA2 hcB hlB1 hlB2 (by omega) (by omega) (fun _ => rfl) (by decide) (by decide)
  · exact pcRankFormula_submod_z (zI := 1) (zU := 1) (z1 := 1) (z2 := 1)
      hr₀ hcA hlA1 hlA2 hcB hlB1 hlB2 rfl (by omega) (by omega) (by decide) (by decide)

def parallelConnRank (r₀ a b : Nat) : Sub ((a + b) + 1) → Nat
  | .cons b₀ rest =>
    let p := Sub.split (a := a) (b := b) rest
    pcRankFormula r₀ (Sub.card p.1) (Sub.card p.2) (if b₀ then 1 else 0)

def parallelConnUniform (r₀ a b : Nat) (hr₀ : 2 ≤ r₀) : SimpleMatroid ((a + b) + 1) where
  r := parallelConnRank r₀ a b
  r_empty := by
    change pcRankFormula r₀ (Sub.card (Sub.split (Sub.empty (a + b))).1)
      (Sub.card (Sub.split (Sub.empty (a + b))).2) 0 = 0
    rw [Sub.split_empty, Sub.card_empty, Sub.card_empty,
        pcRankFormula_z0_of_lt hr₀ (Or.inl (by omega)),
        capNat_of_le (Nat.zero_le r₀)]
  r_singleton := by
    rintro ⟨k, hk⟩
    cases k with
    | zero =>
      change pcRankFormula r₀ (Sub.card (Sub.split (Sub.empty (a + b))).1)
        (Sub.card (Sub.split (Sub.empty (a + b))).2) 1 = 1
      rw [Sub.split_empty, Sub.card_empty, Sub.card_empty,
          pcRankFormula_z1 hr₀, capNat_of_le (by omega)]
    | succ k =>
      let S := Sub.singleton (⟨k, Nat.lt_of_succ_lt_succ hk⟩ : Fin (a + b))
      change pcRankFormula r₀ (Sub.card (Sub.split S).1) (Sub.card (Sub.split S).2) 0 = 1
      have hsum : Sub.card (Sub.split S).1 + Sub.card (Sub.split S).2 = 1 := by
        rw [Sub.card_split_sum, Sub.card_singleton]
      rw [pcRankFormula_z0_of_lt hr₀ (Or.inl (by omega)),
          capNat_of_le (by omega), capNat_of_le (by omega)]
      exact hsum
  r_pair := by
    rintro ⟨k₁, h₁⟩ ⟨k₂, h₂⟩ hne
    cases k₁ with
    | zero =>
      cases k₂ with
      | zero => exact absurd rfl hne
      | succ k₂ =>
        let S := Sub.singleton (⟨k₂, Nat.lt_of_succ_lt_succ h₂⟩ : Fin (a + b))
        change pcRankFormula r₀ (Sub.card (Sub.split S).1) (Sub.card (Sub.split S).2) 1 = 2
        have hsum : Sub.card (Sub.split S).1 + Sub.card (Sub.split S).2 = 1 := by
          rw [Sub.card_split_sum, Sub.card_singleton]
        rw [pcRankFormula_z1 hr₀, capNat_of_le (by omega), capNat_of_le (by omega)]
        omega
    | succ k₁ =>
      cases k₂ with
      | zero =>
        let S := Sub.insert (⟨k₁, Nat.lt_of_succ_lt_succ h₁⟩ : Fin (a + b)) (Sub.empty (a + b))
        change pcRankFormula r₀ (Sub.card (Sub.split S).1) (Sub.card (Sub.split S).2) 1 = 2
        have hsum : Sub.card (Sub.split S).1 + Sub.card (Sub.split S).2 = 1 := by
          rw [Sub.card_split_sum]; exact Sub.card_singleton _
        rw [pcRankFormula_z1 hr₀, capNat_of_le (by omega), capNat_of_le (by omega)]
        omega
      | succ k₂ =>
        let i₁ : Fin (a + b) := ⟨k₁, Nat.lt_of_succ_lt_succ h₁⟩
        let i₂ : Fin (a + b) := ⟨k₂, Nat.lt_of_succ_lt_succ h₂⟩
        have hne' : i₁ ≠ i₂ := by
          intro h
          have hv := congrArg Fin.val h
          dsimp only [i₁, i₂] at hv
          exact hne (Fin.ext (by dsimp only []; omega))
        let S := Sub.insert i₁ (Sub.singleton i₂)
        change pcRankFormula r₀ (Sub.card (Sub.split S).1) (Sub.card (Sub.split S).2) 0 = 2
        have hm : Sub.mem i₁ (Sub.singleton i₂) = false := by
          rw [Sub.mem_singleton]; simp [hne']
        have hsum : Sub.card (Sub.split S).1 + Sub.card (Sub.split S).2 = 2 := by
          rw [Sub.card_split_sum, Sub.card_insert_of_not_mem _ _ hm, Sub.card_singleton]
        rw [pcRankFormula_z0_of_lt hr₀ (by omega), capNat_of_le (by omega), capNat_of_le (by omega)]
        exact hsum
  r_insert_bounds := by
    intro X idx_full
    rcases X with _ | ⟨b₀, rest⟩
    rcases idx_full with ⟨k, hk⟩
    cases k with
    | zero =>
      exact pcRankFormula_z_step hr₀ (Sub.card (Sub.split rest).1) (Sub.card (Sub.split rest).2) b₀
    | succ k =>
      let idx : Fin (a + b) := ⟨k, Nat.lt_of_succ_lt_succ hk⟩
      change pcRankFormula r₀ (Sub.card (Sub.split rest).1) (Sub.card (Sub.split rest).2) _ ≤
             pcRankFormula r₀ (Sub.card (Sub.split (Sub.insert idx rest)).1)
               (Sub.card (Sub.split (Sub.insert idx rest)).2) _ ∧
             pcRankFormula r₀ (Sub.card (Sub.split (Sub.insert idx rest)).1)
               (Sub.card (Sub.split (Sub.insert idx rest)).2) _ ≤
             pcRankFormula r₀ (Sub.card (Sub.split rest).1) (Sub.card (Sub.split rest).2) _ + 1
      rcases Sub.split_insert_step rest idx with ⟨h1, h2 | h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]; exact ⟨Nat.le_refl _, by omega⟩
      · rw [h1, h2]; exact pcRankFormula_step_right hr₀ _ _ _
      · rw [h1, h2]; exact pcRankFormula_step_left hr₀ _ _ _
  r_submod := by
    intro X₁ X₂
    rcases X₁ with _ | ⟨b₁, r₁⟩
    rcases X₂ with _ | ⟨b₂, r₂⟩
    simp only [Sub.inter, Sub.union, parallelConnRank]
    rw [Sub.split_inter, Sub.split_union]
    exact pcRankFormula_submod hr₀
      (Sub.card_inter_add_union (Sub.split r₁).1 (Sub.split r₂).1)
      (Sub.card_mono (Sub.inter_subset_left (Sub.split r₁).1 (Sub.split r₂).1))
      (Sub.card_mono (Sub.inter_subset_right (Sub.split r₁).1 (Sub.split r₂).1))
      (Sub.card_inter_add_union (Sub.split r₁).2 (Sub.split r₂).2)
      (Sub.card_mono (Sub.inter_subset_left (Sub.split r₁).2 (Sub.split r₂).2))
      (Sub.card_mono (Sub.inter_subset_right (Sub.split r₁).2 (Sub.split r₂).2))
      b₁ b₂

/-! ### Exact Flat Characterization & Fast Enumeration for `parallelConnUniform` -/

theorem card_lt_univ_exists_not_mem {n : Nat} {S : Sub n} (hne : S ≠ Sub.univ n) :
    ∃ i : Fin n, Sub.mem i S = false := by
  rcases Sub.exists_not_mem_of_lt (Sub.subset_univ S) hne with ⟨i, _, hiS⟩
  exact ⟨i, hiS⟩

theorem card_univ_eq : (n : Nat) → Sub.card (Sub.univ n) = n
  | 0 => rfl
  | n + 1 => by simp [Sub.univ, Sub.card, card_univ_eq n]; omega

/-- Index into `SA` inside `append SA SB : Sub (a + b)` (shifted past the `b` outer bits of `SB`). -/
def liftFinLeft : {a b : Nat} → Fin a → Fin (a + b)
  | _, 0, i => i
  | a, b + 1, i =>
    let r := liftFinLeft (a := a) (b := b) i
    ⟨r.1 + 1, Nat.succ_lt_succ r.2⟩

/-- Index into `SB` inside `append SA SB : Sub (a + b)` (first `b` outer bits). -/
def liftFinRight : {a b : Nat} → Fin b → Fin (a + b)
  | a, b + 1, ⟨0, _⟩ => ⟨0, Nat.zero_lt_succ (a + b)⟩
  | a, b + 1, ⟨k + 1, hk⟩ =>
    let r := liftFinRight (a := a) (b := b) ⟨k, Nat.lt_of_succ_lt_succ hk⟩
    ⟨r.1 + 1, Nat.succ_lt_succ r.2⟩

theorem insert_append_left : {a b : Nat} → (i : Fin a) → (SA : Sub a) → (SB : Sub b) →
    Sub.insert (liftFinLeft i) (Sub.append SA SB) = Sub.append (Sub.insert i SA) SB
  | _, 0, _, _, .nil => rfl
  | a, b + 1, i, SA, .cons y rB => by
    change Sub.cons y (Sub.insert (liftFinLeft i) (Sub.append SA rB)) =
      Sub.cons y (Sub.append (Sub.insert i SA) rB)
    rw [insert_append_left (a := a) (b := b) i SA rB]

theorem insert_append_right : {a b : Nat} → (j : Fin b) → (SA : Sub a) → (SB : Sub b) →
    Sub.insert (liftFinRight j) (Sub.append SA SB) = Sub.append SA (Sub.insert j SB)
  | _, _ + 1, ⟨0, _⟩, _, .cons _ _ => rfl
  | a, b + 1, ⟨k + 1, hk⟩, SA, .cons y rB => by
    change Sub.cons y (Sub.insert (liftFinRight ⟨k, Nat.lt_of_succ_lt_succ hk⟩) (Sub.append SA rB)) =
      Sub.cons y (Sub.append SA (Sub.insert ⟨k, Nat.lt_of_succ_lt_succ hk⟩ rB))
    rw [insert_append_right (a := a) (b := b) ⟨k, Nat.lt_of_succ_lt_succ hk⟩ SA rB]

theorem mem_append_left : {a b : Nat} → (i : Fin a) → (SA : Sub a) → (SB : Sub b) →
    Sub.mem (liftFinLeft i) (Sub.append SA SB) = Sub.mem i SA
  | _, 0, _, _, .nil => rfl
  | a, b + 1, i, SA, .cons _ rB => mem_append_left (a := a) (b := b) i SA rB

theorem mem_append_right : {a b : Nat} → (j : Fin b) → (SA : Sub a) → (SB : Sub b) →
    Sub.mem (liftFinRight j) (Sub.append SA SB) = Sub.mem j SB
  | _, _ + 1, ⟨0, _⟩, _, .cons _ _ => rfl
  | a, b + 1, ⟨k + 1, hk⟩, SA, .cons _ rB =>
    mem_append_right (a := a) (b := b) ⟨k, Nat.lt_of_succ_lt_succ hk⟩ SA rB

theorem fin_add_cases : {a b : Nat} → (idx : Fin (a + b)) →
    (∃ i : Fin a, idx = liftFinLeft i) ∨ (∃ j : Fin b, idx = liftFinRight j)
  | _, 0, idx => Or.inl ⟨idx, rfl⟩
  | a, b + 1, ⟨0, _⟩ => Or.inr ⟨⟨0, Nat.zero_lt_succ b⟩, rfl⟩
  | a, b + 1, ⟨k + 1, hk⟩ => by
    rcases fin_add_cases (a := a) (b := b) ⟨k, Nat.lt_of_succ_lt_succ hk⟩ with ⟨i, hi⟩ | ⟨j, hj⟩
    · refine Or.inl ⟨i, ?_⟩
      change (⟨k + 1, hk⟩ : Fin ((a + b) + 1)) =
        ⟨(liftFinLeft (a := a) (b := b) i).1 + 1, _⟩
      apply Fin.ext
      have hv := congrArg Fin.val hi
      dsimp only [] at hv ⊢
      omega
    · refine Or.inr ⟨⟨j.1 + 1, Nat.succ_lt_succ j.2⟩, ?_⟩
      rcases j with ⟨jv, hjlt⟩
      change (⟨k + 1, hk⟩ : Fin ((a + b) + 1)) =
        ⟨(liftFinRight (a := a) (b := b) ⟨jv, hjlt⟩).1 + 1, _⟩
      apply Fin.ext
      have hv := congrArg Fin.val hj
      dsimp only [] at hv ⊢
      omega

/-- Exact algebraic characterization of flats of `parallelConnUniform r₀ a b` (`2 ≤ r₀ ≤ a, b`). -/
theorem parallelConn_isFlat_iff {r₀ a b : Nat} (hr₀ : 2 ≤ r₀) (_ha : r₀ ≤ a) (_hb : r₀ ≤ b)
    (b₀ : Bool) (SA : Sub a) (SB : Sub b) :
    (parallelConnUniform r₀ a b hr₀).IsFlat (.cons b₀ (Sub.append SA SB)) ↔
      (b₀ = false ∧ Sub.card SA < r₀ ∧ Sub.card SB < r₀) ∨
      (b₀ = true ∧ (Sub.card SA + 1 < r₀ ∨ SA = Sub.univ a) ∧
                   (Sub.card SB + 1 < r₀ ∨ SB = Sub.univ b)) := by
  let M := parallelConnUniform r₀ a b hr₀
  let S : Sub ((a + b) + 1) := .cons b₀ (Sub.append SA SB)
  have hca_max : Sub.card SA ≤ a := by
    have h := Sub.card_mono (Sub.subset_univ SA); rw [card_univ_eq] at h; exact h
  have hcb_max : Sub.card SB ≤ b := by
    have h := Sub.card_mono (Sub.subset_univ SB); rw [card_univ_eq] at h; exact h
  constructor
  · intro hflat
    have hnot_cl : ∀ idx : Fin ((a + b) + 1), Sub.mem idx S = false → M.r (Sub.insert idx S) ≠ M.r S := by
      intro idx hmem heq
      have hcl : Sub.mem idx (M.cl S) = true := (M.mem_cl_iff S idx).mpr heq
      rw [hflat, hmem] at hcl; contradiction
    cases b₀ with
    | false =>
      refine Or.inl ⟨rfl, ?_, ?_⟩
      · exact Classical.byContradiction fun hge => by
          apply hnot_cl ⟨0, Nat.zero_lt_succ _⟩ rfl
          change pcRankFormula r₀ (Sub.card (Sub.split (Sub.append SA SB)).1)
              (Sub.card (Sub.split (Sub.append SA SB)).2) 1 =
            pcRankFormula r₀ (Sub.card (Sub.split (Sub.append SA SB)).1)
              (Sub.card (Sub.split (Sub.append SA SB)).2) 0
          rw [Sub.split_append_fst, Sub.split_append_snd,
              pcRankFormula_z1 hr₀, capNat_of_ge (by omega : r₀ ≤ Sub.card SA + 1)]
          by_cases hcb : Sub.card SB < r₀
          · rw [pcRankFormula_z0_of_lt hr₀ (Or.inr hcb),
                capNat_of_ge (by omega : r₀ ≤ Sub.card SA),
                capNat_of_le (by omega : Sub.card SB + 1 ≤ r₀),
                capNat_of_le (by omega : Sub.card SB ≤ r₀)]
            omega
          · rw [pcRankFormula_z0_of_ge hr₀ (by omega) (by omega),
                capNat_of_ge (by omega : r₀ ≤ Sub.card SB + 1)]
            omega
      · exact Classical.byContradiction fun hge => by
          apply hnot_cl ⟨0, Nat.zero_lt_succ _⟩ rfl
          change pcRankFormula r₀ (Sub.card (Sub.split (Sub.append SA SB)).1)
              (Sub.card (Sub.split (Sub.append SA SB)).2) 1 =
            pcRankFormula r₀ (Sub.card (Sub.split (Sub.append SA SB)).1)
              (Sub.card (Sub.split (Sub.append SA SB)).2) 0
          rw [Sub.split_append_fst, Sub.split_append_snd,
              pcRankFormula_z1 hr₀, capNat_of_ge (by omega : r₀ ≤ Sub.card SB + 1)]
          by_cases hca : Sub.card SA < r₀
          · rw [pcRankFormula_z0_of_lt hr₀ (Or.inl hca),
                capNat_of_ge (by omega : r₀ ≤ Sub.card SB),
                capNat_of_le (by omega : Sub.card SA + 1 ≤ r₀),
                capNat_of_le (by omega : Sub.card SA ≤ r₀)]
            omega
          · rw [pcRankFormula_z0_of_ge hr₀ (by omega) (by omega),
                capNat_of_ge (by omega : r₀ ≤ Sub.card SA + 1)]
            omega
    | true =>
      refine Or.inr ⟨rfl, ?_, ?_⟩
      · by_cases hlt : Sub.card SA + 1 < r₀
        · exact Or.inl hlt
        · refine Or.inr (Classical.byContradiction fun hne => ?_)
          rcases card_lt_univ_exists_not_mem hne with ⟨i, hiSA⟩
          let idx : Fin ((a + b) + 1) := ⟨(liftFinLeft (b := b) i).1 + 1, Nat.succ_lt_succ (liftFinLeft i).2⟩
          have hmem_f : Sub.mem idx S = false := by
            change Sub.mem (liftFinLeft i) (Sub.append SA SB) = false
            rw [mem_append_left]; exact hiSA
          apply hnot_cl idx hmem_f
          change pcRankFormula r₀ (Sub.card (Sub.split (Sub.insert (liftFinLeft i) (Sub.append SA SB))).1)
              (Sub.card (Sub.split (Sub.insert (liftFinLeft i) (Sub.append SA SB))).2) 1 =
            pcRankFormula r₀ (Sub.card (Sub.split (Sub.append SA SB)).1)
              (Sub.card (Sub.split (Sub.append SA SB)).2) 1
          rw [insert_append_left, Sub.split_append_fst, Sub.split_append_snd,
              Sub.split_append_fst, Sub.split_append_snd, Sub.card_insert_of_not_mem i SA hiSA,
              pcRankFormula_z1 hr₀, pcRankFormula_z1 hr₀,
              capNat_of_ge (by omega : r₀ ≤ Sub.card SA + 1 + 1),
              capNat_of_ge (by omega : r₀ ≤ Sub.card SA + 1)]
      · by_cases hlt : Sub.card SB + 1 < r₀
        · exact Or.inl hlt
        · refine Or.inr (Classical.byContradiction fun hne => ?_)
          rcases card_lt_univ_exists_not_mem hne with ⟨j, hjSB⟩
          let idx : Fin ((a + b) + 1) := ⟨(liftFinRight (a := a) j).1 + 1, Nat.succ_lt_succ (liftFinRight j).2⟩
          have hmem_f : Sub.mem idx S = false := by
            change Sub.mem (liftFinRight j) (Sub.append SA SB) = false
            rw [mem_append_right]; exact hjSB
          apply hnot_cl idx hmem_f
          change pcRankFormula r₀ (Sub.card (Sub.split (Sub.insert (liftFinRight j) (Sub.append SA SB))).1)
              (Sub.card (Sub.split (Sub.insert (liftFinRight j) (Sub.append SA SB))).2) 1 =
            pcRankFormula r₀ (Sub.card (Sub.split (Sub.append SA SB)).1)
              (Sub.card (Sub.split (Sub.append SA SB)).2) 1
          rw [insert_append_right, Sub.split_append_fst, Sub.split_append_snd,
              Sub.split_append_fst, Sub.split_append_snd, Sub.card_insert_of_not_mem j SB hjSB,
              pcRankFormula_z1 hr₀, pcRankFormula_z1 hr₀,
              capNat_of_ge (by omega : r₀ ≤ Sub.card SB + 1 + 1),
              capNat_of_ge (by omega : r₀ ≤ Sub.card SB + 1)]
  · intro hcond
    unfold SimpleMatroid.IsFlat
    apply Sub.subset_antisymm _ (M.subset_cl S)
    rw [Sub.subset_iff_mem]
    intro ⟨k, hk⟩ hcl
    rw [M.mem_cl_iff] at hcl
    by_cases hmem : Sub.mem ⟨k, hk⟩ S = true
    · exact hmem
    · have hm_f : Sub.mem ⟨k, hk⟩ S = false := Bool.eq_false_iff.mpr hmem
      exfalso
      rcases hcond with ⟨hb0, hcA, hcB⟩ | ⟨hb0, hcA, hcB⟩
      · subst hb0
        cases k with
        | zero =>
          change pcRankFormula r₀ (Sub.card (Sub.split (Sub.append SA SB)).1)
              (Sub.card (Sub.split (Sub.append SA SB)).2) 1 =
            pcRankFormula r₀ (Sub.card (Sub.split (Sub.append SA SB)).1)
              (Sub.card (Sub.split (Sub.append SA SB)).2) 0 at hcl
          rw [Sub.split_append_fst, Sub.split_append_snd,
              pcRankFormula_z1 hr₀, pcRankFormula_z0_of_lt hr₀ (Or.inl hcA),
              capNat_of_le (by omega), capNat_of_le (by omega),
              capNat_of_le (by omega), capNat_of_le (by omega)] at hcl
          omega
        | succ k =>
          let idx : Fin (a + b) := ⟨k, Nat.lt_of_succ_lt_succ hk⟩
          change Sub.mem idx (Sub.append SA SB) = false at hm_f
          rcases fin_add_cases idx with ⟨i, hidx⟩ | ⟨j, hidx⟩
          · rw [hidx, mem_append_left] at hm_f
            change pcRankFormula r₀ (Sub.card (Sub.split (Sub.insert idx (Sub.append SA SB))).1)
                (Sub.card (Sub.split (Sub.insert idx (Sub.append SA SB))).2) 0 =
              pcRankFormula r₀ (Sub.card (Sub.split (Sub.append SA SB)).1)
                (Sub.card (Sub.split (Sub.append SA SB)).2) 0 at hcl
            rw [hidx, insert_append_left, Sub.split_append_fst, Sub.split_append_snd,
                Sub.split_append_fst, Sub.split_append_snd,
                Sub.card_insert_of_not_mem i SA hm_f,
                pcRankFormula_z0_of_lt hr₀ (Or.inr hcB), pcRankFormula_z0_of_lt hr₀ (Or.inr hcB),
                capNat_of_le (by omega), capNat_of_le (by omega), capNat_of_le (by omega)] at hcl
            omega
          · rw [hidx, mem_append_right] at hm_f
            change pcRankFormula r₀ (Sub.card (Sub.split (Sub.insert idx (Sub.append SA SB))).1)
                (Sub.card (Sub.split (Sub.insert idx (Sub.append SA SB))).2) 0 =
              pcRankFormula r₀ (Sub.card (Sub.split (Sub.append SA SB)).1)
                (Sub.card (Sub.split (Sub.append SA SB)).2) 0 at hcl
            rw [hidx, insert_append_right, Sub.split_append_fst, Sub.split_append_snd,
                Sub.split_append_fst, Sub.split_append_snd,
                Sub.card_insert_of_not_mem j SB hm_f,
                pcRankFormula_z0_of_lt hr₀ (Or.inl hcA), pcRankFormula_z0_of_lt hr₀ (Or.inl hcA),
                capNat_of_le (by omega), capNat_of_le (by omega), capNat_of_le (by omega)] at hcl
            omega
      · subst hb0
        cases k with
        | zero => contradiction
        | succ k =>
          let idx : Fin (a + b) := ⟨k, Nat.lt_of_succ_lt_succ hk⟩
          change Sub.mem idx (Sub.append SA SB) = false at hm_f
          rcases fin_add_cases idx with ⟨i, hidx⟩ | ⟨j, hidx⟩
          · rw [hidx, mem_append_left] at hm_f
            rcases hcA with hltA | rfl
            · change pcRankFormula r₀ (Sub.card (Sub.split (Sub.insert idx (Sub.append SA SB))).1)
                  (Sub.card (Sub.split (Sub.insert idx (Sub.append SA SB))).2) 1 =
                pcRankFormula r₀ (Sub.card (Sub.split (Sub.append SA SB)).1)
                  (Sub.card (Sub.split (Sub.append SA SB)).2) 1 at hcl
              rw [hidx, insert_append_left, Sub.split_append_fst, Sub.split_append_snd,
                  Sub.split_append_fst, Sub.split_append_snd,
                  Sub.card_insert_of_not_mem i SA hm_f,
                  pcRankFormula_z1 hr₀, pcRankFormula_z1 hr₀,
                  capNat_of_le (by omega : Sub.card SA + 1 + 1 ≤ r₀),
                  capNat_of_le (by omega : Sub.card SA + 1 ≤ r₀)] at hcl
              have hp := capNat_succ_pos hr₀ (Sub.card SB)
              omega
            · rw [Sub.mem_univ] at hm_f; contradiction
          · rw [hidx, mem_append_right] at hm_f
            rcases hcB with hltB | rfl
            · change pcRankFormula r₀ (Sub.card (Sub.split (Sub.insert idx (Sub.append SA SB))).1)
                  (Sub.card (Sub.split (Sub.insert idx (Sub.append SA SB))).2) 1 =
                pcRankFormula r₀ (Sub.card (Sub.split (Sub.append SA SB)).1)
                  (Sub.card (Sub.split (Sub.append SA SB)).2) 1 at hcl
              rw [hidx, insert_append_right, Sub.split_append_fst, Sub.split_append_snd,
                  Sub.split_append_fst, Sub.split_append_snd,
                  Sub.card_insert_of_not_mem j SB hm_f,
                  pcRankFormula_z1 hr₀, pcRankFormula_z1 hr₀,
                  capNat_of_le (by omega : Sub.card SB + 1 + 1 ≤ r₀),
                  capNat_of_le (by omega : Sub.card SB + 1 ≤ r₀)] at hcl
              have hp := capNat_succ_pos hr₀ (Sub.card SA)
              omega
            · rw [Sub.mem_univ] at hm_f; contradiction

/-- Cartesian product builder for fast duplicate-free flat generation. -/
def prodSubs (b₀ : Bool) {a b : Nat} (xs : List (Sub a)) (ys : List (Sub b)) :
    List (Sub ((a + b) + 1)) :=
  xs.foldr (fun SA acc => ys.map (fun SB => .cons b₀ (Sub.append SA SB)) ++ acc) []

theorem mem_prodSubs_iff (b₀ : Bool) {a b : Nat} (xs : List (Sub a)) (ys : List (Sub b))
    (S : Sub ((a + b) + 1)) :
    S ∈ prodSubs b₀ xs ys ↔
      ∃ SA ∈ xs, ∃ SB ∈ ys, S = .cons b₀ (Sub.append SA SB) := by
  unfold prodSubs
  rw [GeometricLattice.mem_foldr_map_append]
  constructor
  · rintro ⟨SA, hSA, hm⟩
    rcases List.mem_map.mp hm with ⟨SB, hSB, heq⟩
    exact ⟨SA, hSA, SB, hSB, heq.symm⟩
  · rintro ⟨SA, hSA, SB, hSB, rfl⟩
    exact ⟨SA, hSA, List.mem_map.mpr ⟨SB, hSB, rfl⟩⟩

theorem nodup_map_prodSub_inner (b₀ : Bool) {a b : Nat} (SA : Sub a)
    {ys : List (Sub b)} (hy : NoDup ys) :
    NoDup (ys.map (fun SB => Sub.cons b₀ (Sub.append SA SB))) := by
  induction hy with
  | nil => exact NoDup.nil
  | @cons SB _ hninB _ ihB =>
    refine NoDup.cons ?_ ihB
    intro hm
    rcases List.mem_map.mp hm with ⟨SB', hSB', heq⟩
    have hval : Sub.append SA SB' = Sub.append SA SB := (Sub.cons.inj heq).2
    have hsp := congrArg Sub.split hval
    simp only [Sub.split_append] at hsp
    injection hsp with _ hSB_eq
    rw [hSB_eq] at hSB'
    exact hninB hSB'

theorem nodup_prodSubs (b₀ : Bool) {a b : Nat} {xs : List (Sub a)} {ys : List (Sub b)}
    (hx : NoDup xs) (hy : NoDup ys) : NoDup (prodSubs b₀ xs ys) := by
  unfold prodSubs
  induction hx with
  | nil => exact NoDup.nil
  | @cons SA _ hninA _ ih =>
    simp only [List.foldr]
    apply GeometricLattice.nodup_append_of_disjoint (nodup_map_prodSub_inner b₀ SA hy) ih
    intro Z h1 h2
    rcases List.mem_map.mp h1 with ⟨SB₁, _, rfl⟩
    rw [GeometricLattice.mem_foldr_map_append] at h2
    rcases h2 with ⟨SA₂, hSA₂, hm2⟩
    rcases List.mem_map.mp hm2 with ⟨SB₂, _, heq⟩
    have hval : Sub.append SA₂ SB₂ = Sub.append SA SB₁ := (Sub.cons.inj heq).2
    have hsp := congrArg Sub.split hval
    simp only [Sub.split_append] at hsp
    injection hsp with hSA_eq _
    rw [hSA_eq] at hSA₂
    exact hninA hSA₂

def rawFlatsPC (r₀ a b : Nat) : List (Sub ((a + b) + 1)) :=
  let no0A := (Sub.allSubs a).filter (fun SA => decide (Sub.card SA < r₀))
  let no0B := (Sub.allSubs b).filter (fun SB => decide (Sub.card SB < r₀))
  let w0A := (Sub.allSubs a).filter (fun SA => decide (Sub.card SA + 1 < r₀) || decide (SA = Sub.univ a))
  let w0B := (Sub.allSubs b).filter (fun SB => decide (Sub.card SB + 1 < r₀) || decide (SB = Sub.univ b))
  prodSubs false no0A no0B ++ prodSubs true w0A w0B

theorem nodup_rawFlatsPC (r₀ a b : Nat) : NoDup (rawFlatsPC r₀ a b) := by
  unfold rawFlatsPC
  apply GeometricLattice.nodup_append_of_disjoint
    (nodup_prodSubs false (nodup_filter _ (Sub.nodup_allSubs a)) (nodup_filter _ (Sub.nodup_allSubs b)))
    (nodup_prodSubs true (nodup_filter _ (Sub.nodup_allSubs a)) (nodup_filter _ (Sub.nodup_allSubs b)))
  intro Z h1 h2
  rcases (mem_prodSubs_iff _ _ _ _).mp h1 with ⟨_, _, _, _, rfl⟩
  rcases (mem_prodSubs_iff _ _ _ _).mp h2 with ⟨_, _, _, _, heq⟩
  cases heq

theorem mem_rawFlatsPC_iff (r₀ a b : Nat) (hr₀ : 2 ≤ r₀) (ha : r₀ ≤ a) (hb : r₀ ≤ b)
    (S : Sub ((a + b) + 1)) :
    S ∈ rawFlatsPC r₀ a b ↔ (parallelConnUniform r₀ a b hr₀).IsFlat S := by
  rcases S with _ | ⟨b₀, rest⟩
  have hrest : rest = Sub.append (Sub.split rest).1 (Sub.split rest).2 := (Sub.append_split rest).symm
  rw [hrest, parallelConn_isFlat_iff hr₀ ha hb]
  unfold rawFlatsPC
  rw [List.mem_append, mem_prodSubs_iff, mem_prodSubs_iff]
  constructor
  · rintro (⟨SA', hSA', SB', hSB', heq⟩ | ⟨SA', hSA', SB', hSB', heq⟩)
    · rcases Sub.cons.inj heq with ⟨hb0, hval⟩
      have hsp := congrArg Sub.split hval
      simp only [Sub.split_append] at hsp
      injection hsp with h1 h2
      have pA := of_decide_eq_true ((mem_filter_iff_prop _ _ _).mp hSA').2
      have pB := of_decide_eq_true ((mem_filter_iff_prop _ _ _).mp hSB').2
      rw [← h1] at pA; rw [← h2] at pB
      exact Or.inl ⟨hb0, pA, pB⟩
    · rcases Sub.cons.inj heq with ⟨hb0, hval⟩
      have hsp := congrArg Sub.split hval
      simp only [Sub.split_append] at hsp
      injection hsp with h1 h2
      have pA := (Bool.or_eq_true _ _).mp ((mem_filter_iff_prop _ _ _).mp hSA').2
      have pB := (Bool.or_eq_true _ _).mp ((mem_filter_iff_prop _ _ _).mp hSB').2
      rw [← h1] at pA; rw [← h2] at pB
      exact Or.inr ⟨hb0,
        pA.elim (fun h => Or.inl (of_decide_eq_true h)) (fun h => Or.inr (of_decide_eq_true h)),
        pB.elim (fun h => Or.inl (of_decide_eq_true h)) (fun h => Or.inr (of_decide_eq_true h))⟩
  · rintro (⟨rfl, hcA, hcB⟩ | ⟨rfl, hcA, hcB⟩)
    · refine Or.inl ⟨(Sub.split rest).1, ?_, (Sub.split rest).2, ?_, rfl⟩
      · rw [mem_filter_iff_prop]; exact ⟨Sub.mem_allSubs _, decide_eq_true hcA⟩
      · rw [mem_filter_iff_prop]; exact ⟨Sub.mem_allSubs _, decide_eq_true hcB⟩
    · refine Or.inr ⟨(Sub.split rest).1, ?_, (Sub.split rest).2, ?_, rfl⟩
      · rw [mem_filter_iff_prop]; refine ⟨Sub.mem_allSubs _, Bool.or_eq_true _ _ |>.mpr ?_⟩
        exact hcA.elim (fun h => Or.inl (decide_eq_true h)) (fun h => Or.inr (decide_eq_true h))
      · rw [mem_filter_iff_prop]; refine ⟨Sub.mem_allSubs _, Bool.or_eq_true _ _ |>.mpr ?_⟩
        exact hcB.elim (fun h => Or.inl (decide_eq_true h)) (fun h => Or.inr (decide_eq_true h))

/-! ### Counterexample on `L34 = L(U_{2,5} ⊕_{e₀} U_{2,6})` (`|L| = 34`, Rank 3): Classical LYM Fails -/

def M34 : SimpleMatroid 10 := parallelConnUniform 2 4 5 (by decide)
def L34 : GeometricLattice M34.Flat :=
  M34.toGeometricLattice (rawFlatsPC 2 4 5) (nodup_rawFlatsPC 2 4 5)
    (mem_rawFlatsPC_iff 2 4 5 (by decide) (by decide) (by decide))

/-- Classical rank-uniform LYM weighting `1 / W_{rk x}` on `L34`. -/
def wClassical34 (x : M34.Flat) : QRat :=
  let k := L34.rk x
  let d := L34.whitney2 k
  if h : 0 < d then QRat.mkNat 1 d h else QRat.zero

def antichain34 : List M34.Flat :=
  let a1 := (L34.rankLevel 1).filter (fun x => Sub.mem ⟨0, Nat.zero_lt_succ 9⟩ x.1)
  let a2 := (L34.rankLevel 2).filter (fun x => !Sub.mem ⟨0, Nat.zero_lt_succ 9⟩ x.1)
  a1 ++ a2

/--
**Theorem (`classical_lym_fails_on_L34`):**
On the 34-element rank-3 geometric lattice `L34 = L(U_{2,5} ⊕_{e₀} U_{2,6})`, the 21-element
antichain `antichain34` has classical rank-uniform LYM weight `1/10 + 20/22 = 111/110 > 1`.
-/
theorem classical_lym_fails_on_L34 :
    L34.elems.length = 34 ∧
    L34.rk L34.top = 3 ∧
    L34.whitney2 1 = 10 ∧
    L34.whitney2 2 = 22 ∧
    L34.IsAntichain antichain34 ∧
    antichain34.length = 21 ∧
    QRat.eqv (QRat.sumList antichain34 wClassical34) (QRat.mkNat 111 110 (by decide)) ∧
    QRat.lt QRat.one (QRat.sumList antichain34 wClassical34) := by
  have hW1 : L34.whitney2 1 = 10 := by decide
  have hW2 : L34.whitney2 2 = 22 := by decide
  let a1 := (L34.rankLevel 1).filter (fun x => Sub.mem ⟨0, Nat.zero_lt_succ 9⟩ x.1)
  let a2 := (L34.rankLevel 2).filter (fun x => !Sub.mem ⟨0, Nat.zero_lt_succ 9⟩ x.1)
  have hsplit := QRat.sumList_append_eqv a1 a2 wClassical34
  have ha1_eqv : QRat.eqv (QRat.sumList a1 wClassical34) (QRat.mkNat 1 10 (by decide)) := by decide
  have ha2_congr : QRat.eqv (QRat.sumList a2 wClassical34)
      (QRat.sumList a2 (fun _ => QRat.mkNat 1 22 (by decide))) := by
    apply QRat.sumList_congr_eqv
    intro x hx
    have hkx : L34.rk x = 2 :=
      of_decide_eq_true ((mem_filter_iff_prop _ _ _).mp ((mem_filter_iff_prop _ _ _).mp hx).1).2
    unfold wClassical34
    simp [hkx, hW2, QRat.eqv]
  have ha2_sum : sumNat a2 (fun _ => 1) = 20 := by
    rw [← length_eq_sumNat_ones]
    decide
  have ha2_eqv : QRat.eqv (QRat.sumList a2 wClassical34) (QRat.mkNat 20 22 (by decide)) := by
    have hcd := QRat.sumList_const_den a2 (fun _ => 1) 22 (by decide)
    rw [ha2_sum] at hcd
    exact QRat.eqv_trans ha2_congr hcd
  have htot_eqv : QRat.eqv (QRat.sumList antichain34 wClassical34)
      (QRat.mkNat 111 110 (by decide)) := by
    have hadd := QRat.add_eqv ha1_eqv ha2_eqv
    have hnum : QRat.eqv (QRat.add (QRat.mkNat 1 10 (by decide)) (QRat.mkNat 20 22 (by decide)))
        (QRat.mkNat 111 110 (by decide)) := by decide
    exact QRat.eqv_trans hsplit (QRat.eqv_trans hadd hnum)
  have hgt : QRat.lt QRat.one (QRat.sumList antichain34 wClassical34) :=
    QRat.lt_of_lt_of_eqv_right (by decide : QRat.lt QRat.one (QRat.mkNat 111 110 (by decide)))
      (QRat.eqv_symm htot_eqv)
  exact ⟨by decide, by decide, hW1, hW2, by decide, by decide, htot_eqv, hgt⟩

/-! ### Counterexample on `L922 = L(U_{3,8} ⊕_{e₀} U_{3,8})` (`|L| = 922`, Rank 5): Upper-Möbius LYM Fails -/

abbrev M922 : SimpleMatroid ((7 + 7) + 1) := parallelConnUniform 3 7 7 (by decide)
def L922 : GeometricLattice M922.Flat :=
  M922.toGeometricLattice (rawFlatsPC 3 7 7) (nodup_rawFlatsPC 3 7 7)
    (mem_rawFlatsPC_iff 3 7 7 (by decide) (by decide) (by decide))

def wUpper922 (x : M922.Flat) : QRat :=
  let k := L922.rk x
  let d := L922.upperMobiusRankSum k
  if h : 0 < d then QRat.mkNat (L922.absMobius x L922.top) d h else QRat.zero

def subsEq2_7 : List (Sub 7) :=
  (Sub.allSubs 7).filter (fun S => decide (Sub.card S = 2))

def with0All_7 : List (Sub 7) :=
  (Sub.allSubs 7).filter (fun S => decide (Sub.card S + 1 < 3) || decide (S = Sub.univ 7))

def with0Rk4_15 : List (Sub ((7 + 7) + 1)) :=
  (prodSubs true with0All_7 with0All_7).filter (fun S => decide (M922.r S = 4))

def fastUpperCoversRk3 (S : Sub ((7 + 7) + 1)) : Nat :=
  match S with
  | .cons b₀ rest =>
    let p := Sub.split (a := 7) (b := 7) rest
    let cNo0 :=
      if b₀ then 0
      else (subsEq2_7.filter (fun TA => Sub.subset p.1 TA)).length *
           (subsEq2_7.filter (fun TB => Sub.subset p.2 TB)).length
    let cW0 := (with0Rk4_15.filter (fun T => Sub.subset S T)).length
    cNo0 + cW0

theorem filter_prodSubs_false_length {a b : Nat} (xs : List (Sub a)) (ys : List (Sub b))
    (SA : Sub a) (SB : Sub b) :
    ((prodSubs false xs ys).filter (fun T => Sub.subset (.cons false (Sub.append SA SB)) T)).length =
      (xs.filter (fun TA => Sub.subset SA TA)).length *
      (ys.filter (fun TB => Sub.subset SB TB)).length := by
  unfold prodSubs
  induction xs with
  | nil => simp [List.foldr, List.filter]
  | cons TA restA ih =>
    simp only [List.foldr, List.filter_append, List.length_append, List.filter]
    have hmap : ((ys.map (fun TB => Sub.cons false (Sub.append TA TB))).filter
        (fun T => Sub.subset (.cons false (Sub.append SA SB)) T)).length =
        if Sub.subset SA TA = true then (ys.filter (fun TB => Sub.subset SB TB)).length else 0 := by
      clear ih restA
      induction ys with
      | nil => cases Sub.subset SA TA <;> simp
      | cons TB restB ihB =>
        simp only [List.map, List.filter]
        have hsub : Sub.subset (.cons false (Sub.append SA SB)) (.cons false (Sub.append TA TB)) =
            (Sub.subset SA TA && Sub.subset SB TB) := by
          change ((!false || false) && Sub.subset (Sub.append SA SB) (Sub.append TA TB)) = _
          simp [Sub.subset_append]
        rw [hsub]
        cases hsa : Sub.subset SA TA <;> cases hsb : Sub.subset SB TB <;> simp_all <;> omega
    rw [hmap, ih]
    cases Sub.subset SA TA
    · simp
    · simp [Nat.add_mul, Nat.add_comm]

theorem filter_prodSubs_false_true_nil {a b : Nat} (xs : List (Sub a)) (ys : List (Sub b))
    (rest : Sub (a + b)) :
    ((prodSubs false xs ys).filter (fun T => Sub.subset (.cons true rest) T)) = [] := by
  apply filter_eq_nil_of_false
  intro T hT
  rcases (mem_prodSubs_iff _ _ _ _).mp hT with ⟨_, _, _, _, rfl⟩
  rfl

theorem length_pmap_filter {m : Nat} (M : SimpleMatroid m) (raws : List (Sub m))
    (hraw : ∀ S ∈ raws, M.IsFlat S) (p : Sub m → Bool) :
    ((raws.pmap Subtype.mk hraw).filter (fun x : M.Flat => p x.1)).length =
      (raws.filter p).length := by
  induction raws with
  | nil => rfl
  | cons a as ih =>
    simp only [List.pmap, List.filter]
    cases p a <;> simp [ih (fun S hS => hraw S (List.mem_cons_of_mem a hS))]

theorem sumNat_pmap {m : Nat} (M : SimpleMatroid m) (raws : List (Sub m))
    (hraw : ∀ S ∈ raws, M.IsFlat S) (p : Sub m → Bool) (g : Sub m → Nat) :
    sumNat ((raws.pmap Subtype.mk hraw).filter (fun x : M.Flat => p x.1)) (fun x => g x.1) =
      sumNat (raws.filter p) g := by
  induction raws with
  | nil => rfl
  | cons a as ih =>
    simp only [List.pmap, List.filter]
    cases p a <;> simp [sumNat, ih (fun S hS => hraw S (List.mem_cons_of_mem a hS))]

theorem filter_prodSubs_false_rk4 {xs ys : List (Sub 7)}
    (hx : ∀ SA ∈ xs, Sub.card SA < 3) (hy : ∀ SB ∈ ys, Sub.card SB < 3) :
    (prodSubs false xs ys).filter (fun y => decide (M922.r y = 4)) =
      prodSubs false (xs.filter (fun SA => decide (Sub.card SA = 2)))
                     (ys.filter (fun SB => decide (Sub.card SB = 2))) := by
  unfold prodSubs
  induction xs with
  | nil => simp [List.foldr, List.filter]
  | cons SA restA ih =>
    have hSA_lt : Sub.card SA < 3 := hx SA List.mem_cons_self
    have ih' := ih (fun X hX => hx X (List.mem_cons_of_mem SA hX))
    simp only [List.foldr, List.filter_append, List.filter]
    by_cases hSA2 : Sub.card SA = 2
    · simp only [hSA2, decide_true, List.foldr]
      rw [ih']
      congr 1
      clear ih ih' hx restA
      induction ys with
      | nil => rfl
      | cons SB restB ihB =>
        have hSB_lt : Sub.card SB < 3 := hy SB List.mem_cons_self
        have ihB' := ihB (fun Y hY => hy Y (List.mem_cons_of_mem SB hY))
        simp only [List.map, List.filter]
        have hr_eq : M922.r (.cons false (Sub.append SA SB)) = 2 + Sub.card SB := by
          change pcRankFormula 3 (Sub.card (Sub.split (Sub.append SA SB)).1)
            (Sub.card (Sub.split (Sub.append SA SB)).2) 0 = _
          rw [Sub.split_append_fst, Sub.split_append_snd, hSA2,
              pcRankFormula_z0_of_lt (by decide) (Or.inl (by omega)),
              capNat_of_le (by omega), capNat_of_le (by omega)]
        by_cases hSB2 : Sub.card SB = 2
        · have hr4 : M922.r (.cons false (Sub.append SA SB)) = 4 := by omega
          simp [hSB2, hr4, List.map, ihB']
        · have hne4 : M922.r (.cons false (Sub.append SA SB)) ≠ 4 := by omega
          simp [hSB2, hne4, ihB']
    · simp only [hSA2, decide_false]
      have hempty : ((ys.map (fun SB => Sub.cons false (Sub.append SA SB))).filter
          (fun y => decide (M922.r y = 4))) = [] := by
        apply filter_eq_nil_of_false
        intro y hy_map
        rcases List.mem_map.mp hy_map with ⟨SB, hSB, rfl⟩
        have hSB_lt : Sub.card SB < 3 := hy SB hSB
        have hr_lt : M922.r (.cons false (Sub.append SA SB)) ≠ 4 := by
          change pcRankFormula 3 (Sub.card (Sub.split (Sub.append SA SB)).1)
            (Sub.card (Sub.split (Sub.append SA SB)).2) 0 ≠ 4
          rw [Sub.split_append_fst, Sub.split_append_snd,
              pcRankFormula_z0_of_lt (by decide) (Or.inl hSA_lt),
              capNat_of_le (by omega), capNat_of_le (by omega)]
          omega
        simp [hr_lt]
      rw [hempty, List.nil_append, ih']

theorem upperCovers_rk3_eq_fast {x : M922.Flat} (hrx : L922.rk x = 3) :
    (L922.upperCovers x).length = fastUpperCoversRk3 x.1 := by
  unfold GeometricLattice.upperCovers
  rw [hrx]
  change ((L922.elems).filter (fun y => Sub.subset x.1 y.1 && decide (M922.r y.1 = 4))).length = _
  unfold L922 SimpleMatroid.toGeometricLattice
  dsimp only []
  rw [length_pmap_filter M922 (rawFlatsPC 3 7 7) _ (fun S => Sub.subset x.1 S && decide (M922.r S = 4))]
  unfold rawFlatsPC
  rw [List.filter_append, List.length_append]
  rcases hx : x.1 with _ | ⟨b₀, rest⟩
  dsimp only [fastUpperCoversRk3]
  have hw0 : ((prodSubs true with0All_7 with0All_7).filter
      (fun y => Sub.subset (.cons b₀ rest) y && decide (M922.r y = 4))).length =
      (with0Rk4_15.filter (fun T => Sub.subset (.cons b₀ rest) T)).length := by
    unfold with0Rk4_15
    rw [filter_filter_eq _ _ _ _ (fun _ _ => Bool.and_comm _ _)]
  let no0_7 := (Sub.allSubs 7).filter (fun S => decide (Sub.card S < 3))
  change (((prodSubs false no0_7 no0_7).filter
            (fun y => Sub.subset (.cons b₀ rest) y && decide (M922.r y = 4))).length +
          ((prodSubs true with0All_7 with0All_7).filter
            (fun y => Sub.subset (.cons b₀ rest) y && decide (M922.r y = 4))).length) = _
  rw [hw0]
  congr 1
  rw [← filter_filter_eq _ (fun y => decide (M922.r y = 4)) (fun y => Sub.subset (.cons b₀ rest) y)
        _ (fun _ _ => Bool.and_comm _ _)]
  have hno0_lt : ∀ S ∈ no0_7, Sub.card S < 3 :=
    fun _ hS => of_decide_eq_true ((mem_filter_iff_prop _ _ _).mp hS).2
  rw [filter_prodSubs_false_rk4 hno0_lt hno0_lt]
  have hsub_eq : no0_7.filter (fun S => decide (Sub.card S = 2)) = subsEq2_7 := by
    unfold no0_7 subsEq2_7
    apply filter_filter_eq
    intro S _
    by_cases h2 : Sub.card S = 2
    · have hlt : Sub.card S < 3 := by omega
      simp [h2, hlt]
    · simp [h2]
  rw [hsub_eq]
  cases b₀ with
  | true =>
    rw [filter_prodSubs_false_true_nil]
    rfl
  | false =>
    have hsp : rest = Sub.append (Sub.split (a := 7) (b := 7) rest).1
        (Sub.split (a := 7) (b := 7) rest).2 := (Sub.append_split (a := 7) (b := 7) rest).symm
    conv => lhs; rw [hsp]
    rw [filter_prodSubs_false_length]
    simp

set_option maxRecDepth 20000
set_option maxHeartbeats 800000

theorem L922_rk_top : L922.rk L922.top = 5 := by decide

theorem L922_upperMobiusRankSum_4 : L922.upperMobiusRankSum 4 = 455 := by
  rw [L922.upperMobiusRankSum_coatom (by rw [L922_rk_top])]
  unfold GeometricLattice.rankLevel L922 SimpleMatroid.toGeometricLattice
  dsimp only []
  rw [length_pmap_filter M922 (rawFlatsPC 3 7 7) _ (fun S => decide (M922.r S = 4))]
  decide

theorem L922_upperMobiusRankSum_3 : L922.upperMobiusRankSum 3 = 1825 := by
  unfold GeometricLattice.upperMobiusRankSum
  have hcongr : sumNat (L922.rankLevel 3) (fun y => L922.absMobius y L922.top) =
      sumNat (L922.rankLevel 3) (fun y => fastUpperCoversRk3 y.1 - 1) := by
    apply sumNat_congr
    intro y hy
    have hry : L922.rk y = 3 := of_decide_eq_true ((mem_filter_iff_prop _ _ _).mp hy).2
    rw [L922.absMobius_corank2_top (by rw [hry, L922_rk_top]), upperCovers_rk3_eq_fast hry]
  rw [hcongr]
  unfold GeometricLattice.rankLevel L922 SimpleMatroid.toGeometricLattice
  dsimp only []
  rw [sumNat_pmap M922 (rawFlatsPC 3 7 7) _ (fun S => decide (M922.r S = 3))
        (fun S => fastUpperCoversRk3 S - 1)]
  decide

def ac922_part3 : List M922.Flat :=
  (L922.rankLevel 3).filter (fun x => Sub.mem ⟨0, Nat.zero_lt_succ 14⟩ x.1)

def ac922_part4 : List M922.Flat :=
  (L922.rankLevel 4).filter (fun x => !Sub.mem ⟨0, Nat.zero_lt_succ 14⟩ x.1)

def antichain922 : List M922.Flat :=
  ac922_part3 ++ ac922_part4

theorem antichain922_isAntichain : L922.IsAntichain antichain922 := by
  unfold antichain922
  have hnd3 : NoDup ac922_part3 := nodup_filter _ (L922.rankLevel_isAntichain 3).1
  have hnd4 : NoDup ac922_part4 := nodup_filter _ (L922.rankLevel_isAntichain 4).1
  have hrk3 : ∀ x ∈ ac922_part3, L922.rk x = 3 ∧ Sub.mem ⟨0, Nat.zero_lt_succ 14⟩ x.1 = true := by
    intro x hx
    rcases (mem_filter_iff_prop _ _ _).mp hx with ⟨hxR, hm0⟩
    exact ⟨of_decide_eq_true ((mem_filter_iff_prop _ _ _).mp hxR).2, hm0⟩
  have hrk4 : ∀ y ∈ ac922_part4, L922.rk y = 4 ∧ Sub.mem ⟨0, Nat.zero_lt_succ 14⟩ y.1 = false := by
    intro y hy
    rcases (mem_filter_iff_prop _ _ _).mp hy with ⟨hyR, hm0⟩
    exact ⟨of_decide_eq_true ((mem_filter_iff_prop _ _ _).mp hyR).2, by simpa using hm0⟩
  refine ⟨GeometricLattice.nodup_append_of_disjoint hnd3 hnd4 (fun z h1 h2 => by
    have r1 := (hrk3 z h1).1; have r2 := (hrk4 z h2).1; omega), ?_⟩
  intro x hx y hy hxy
  rcases List.mem_append.mp hx with hx3 | hx4 <;> rcases List.mem_append.mp hy with hy3 | hy4
  · exact (L922.rankLevel_isAntichain 3).2 x ((mem_filter_iff_prop _ _ _).mp hx3).1
      y ((mem_filter_iff_prop _ _ _).mp hy3).1 hxy
  · have hm0x := (hrk3 x hx3).2
    have hm0y := (hrk4 y hy4).2
    have hxy_sub : Sub.subset x.1 y.1 = true := hxy
    have himp := (Sub.subset_iff_mem x.1 y.1).mp hxy_sub ⟨0, Nat.zero_lt_succ 14⟩ hm0x
    exact Bool.noConfusion (hm0y.symm.trans himp)
  · by_cases heq : x = y
    · exact heq
    · have hlt := L922.lt_rk hxy heq
      have r1 := (hrk4 x hx4).1
      have r2 := (hrk3 y hy3).1
      omega
  · exact (L922.rankLevel_isAntichain 4).2 x ((mem_filter_iff_prop _ _ _).mp hx4).1
      y ((mem_filter_iff_prop _ _ _).mp hy4).1 hxy

/--
**Theorem (`upper_mobius_lym_fails_on_L922`):**
On the rank-5 geometric lattice `L922 = L(U_{3,8} ⊕_{e₀} U_{3,8})` (`|L| = 922`), the antichain
`antichain922` achieves rank-normalized upper Möbius weight `61/1825 + 441/455 = 23788/23725 > 1`.
-/
theorem upper_mobius_lym_fails_on_L922 :
    L922.elems.length = 922 ∧
    L922.rk L922.top = 5 ∧
    L922.upperMobiusRankSum 3 = 1825 ∧
    L922.upperMobiusRankSum 4 = 455 ∧
    L922.IsAntichain antichain922 ∧
    QRat.eqv (QRat.sumList antichain922 wUpper922) (QRat.mkNat 23788 23725 (by decide)) ∧
    QRat.lt QRat.one (QRat.sumList antichain922 wUpper922) := by
  have hlen922 : L922.elems.length = 922 := by
    unfold L922 SimpleMatroid.toGeometricLattice
    dsimp only []
    rw [List.length_pmap]
    decide
  have hS3 := L922_upperMobiusRankSum_3
  have hS4 := L922_upperMobiusRankSum_4
  have hsplit := QRat.sumList_append_eqv ac922_part3 ac922_part4 wUpper922
  have hp3_congr : QRat.eqv (QRat.sumList ac922_part3 wUpper922)
      (QRat.sumList ac922_part3 (fun x => QRat.mkNat (L922.absMobius x L922.top) 1825 (by decide))) := by
    apply QRat.sumList_congr_eqv
    intro x hx
    have hrx : L922.rk x = 3 :=
      of_decide_eq_true ((mem_filter_iff_prop _ _ _).mp ((mem_filter_iff_prop _ _ _).mp hx).1).2
    unfold wUpper922
    simp [hrx, hS3, QRat.eqv]
  have hp3_num : sumNat ac922_part3 (fun x => L922.absMobius x L922.top) = 61 := by
    have hc : sumNat ac922_part3 (fun x => L922.absMobius x L922.top) =
        sumNat ac922_part3 (fun x => fastUpperCoversRk3 x.1 - 1) := by
      apply sumNat_congr
      intro x hx
      have hrx : L922.rk x = 3 :=
        of_decide_eq_true ((mem_filter_iff_prop _ _ _).mp ((mem_filter_iff_prop _ _ _).mp hx).1).2
      rw [L922.absMobius_corank2_top (by rw [hrx, L922_rk_top]), upperCovers_rk3_eq_fast hrx]
    rw [hc]
    unfold ac922_part3 GeometricLattice.rankLevel
    rw [filter_filter_eq L922.elems
          (fun x => decide (L922.rk x = 3))
          (fun x => Sub.mem ⟨0, Nat.zero_lt_succ 14⟩ x.1)
          (fun x => decide (L922.rk x = 3) && Sub.mem ⟨0, Nat.zero_lt_succ 14⟩ x.1)
          (fun _ _ => rfl)]
    unfold L922 SimpleMatroid.toGeometricLattice
    dsimp only []
    rw [sumNat_pmap M922 (rawFlatsPC 3 7 7) _
          (fun S => decide (M922.r S = 3) && Sub.mem ⟨0, Nat.zero_lt_succ 14⟩ S)
          (fun S => fastUpperCoversRk3 S - 1)]
    decide
  have hp3_eqv : QRat.eqv (QRat.sumList ac922_part3 wUpper922)
      (QRat.mkNat 61 1825 (by decide)) := by
    have hcd := QRat.sumList_const_den ac922_part3 (fun x => L922.absMobius x L922.top) 1825 (by decide)
    rw [hp3_num] at hcd
    exact QRat.eqv_trans hp3_congr hcd
  have hp4_congr : QRat.eqv (QRat.sumList ac922_part4 wUpper922)
      (QRat.sumList ac922_part4 (fun _ => QRat.mkNat 1 455 (by decide))) := by
    apply QRat.sumList_congr_eqv
    intro y hy
    have hry : L922.rk y = 4 :=
      of_decide_eq_true ((mem_filter_iff_prop _ _ _).mp ((mem_filter_iff_prop _ _ _).mp hy).1).2
    have hmu1 : L922.absMobius y L922.top = 1 :=
      (L922.mobius_coatom_top (by rw [hry, L922_rk_top])).2
    unfold wUpper922
    simp [hry, hS4, hmu1, QRat.eqv]
  have hp4_num : sumNat ac922_part4 (fun _ => 1) = 441 := by
    rw [← length_eq_sumNat_ones]
    unfold ac922_part4 GeometricLattice.rankLevel
    rw [filter_filter_eq L922.elems
          (fun x => decide (L922.rk x = 4))
          (fun x => !Sub.mem ⟨0, Nat.zero_lt_succ 14⟩ x.1)
          (fun x => decide (L922.rk x = 4) && !Sub.mem ⟨0, Nat.zero_lt_succ 14⟩ x.1)
          (fun _ _ => rfl)]
    unfold L922 SimpleMatroid.toGeometricLattice
    dsimp only []
    rw [length_pmap_filter M922 (rawFlatsPC 3 7 7) _
          (fun S => decide (M922.r S = 4) && !Sub.mem ⟨0, Nat.zero_lt_succ 14⟩ S)]
    decide
  have hp4_eqv : QRat.eqv (QRat.sumList ac922_part4 wUpper922)
      (QRat.mkNat 441 455 (by decide)) := by
    have hcd := QRat.sumList_const_den ac922_part4 (fun _ => 1) 455 (by decide)
    rw [hp4_num] at hcd
    exact QRat.eqv_trans hp4_congr hcd
  have htot_eqv : QRat.eqv (QRat.sumList antichain922 wUpper922)
      (QRat.mkNat 23788 23725 (by decide)) := by
    have hadd := QRat.add_eqv hp3_eqv hp4_eqv
    have hnum : QRat.eqv (QRat.add (QRat.mkNat 61 1825 (by decide)) (QRat.mkNat 441 455 (by decide)))
        (QRat.mkNat 23788 23725 (by decide)) := by decide
    exact QRat.eqv_trans hsplit (QRat.eqv_trans hadd hnum)
  have hgt : QRat.lt QRat.one (QRat.sumList antichain922 wUpper922) :=
    QRat.lt_of_lt_of_eqv_right (by decide : QRat.lt QRat.one (QRat.mkNat 23788 23725 (by decide)))
      (QRat.eqv_symm htot_eqv)
  exact ⟨hlen922, L922_rk_top, hS3, hS4, antichain922_isAntichain, htot_eqv, hgt⟩

end Conjecture00000008533
