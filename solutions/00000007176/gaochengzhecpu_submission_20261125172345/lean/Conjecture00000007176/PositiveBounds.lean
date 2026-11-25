/-
Copyright (c) 2026 The Last Math Competition Contributors. All rights reserved.
Sharp positive theorems and complete rigidity characterizations for symmetric tensor
eigenvalues in Core Lean 4.19.0:
1. Qi's entrywise Gershgorin `H`-eigenvalue bound `|λ| ≤ n^{m-1} B` over `R[i]` and `R`,
   attained by `J_{m, n}`.
2. Complete equality rigidity over `R[i]` (root-of-unity rank-`1`), over `R_{≥0}` (uniquely
   `B * J_{m, n}`), over `R` for odd `m` (`± B * J_{m, n}`), and over `R` for even `m`
   (`± B * s^{⊗ m}`, `s ∈ {±1}^n`).
3. Sharp entrywise `Z`-eigenvalue bound `λ^2 ≤ B^2 n^m`, attained rationally on `n = k^2`.
4. Banach's Frobenius `Z`-eigenvalue bound `λ^2 ≤ ‖A‖_F^2` with rank-`1` rigidity.
5. Sharp Frobenius `H`-eigenvalue bound `λ^2 ≤ n^{m-2} ‖A‖_F^2`, attained by `J_{m, n}`.
6. Weighted complex/real row-sum Gershgorin theorem and Vandermonde exact spectral radius
   `C(2m - 1, m - 1)` of the binomial-entry tensor `B_{m, 2}`.
-/
import Conjecture00000007176.SymmetricTensor

namespace Conjecture00000007176

section PositiveTheorems

variable {R : Type u} [OrderedDomain R]

/-! ### Helper: Maximum Coordinate Modulus on `Fin n` (`n ≥ 1`) -/

theorem exists_max_fin {n : Nat} (hn : n ≥ 1) (f : Fin n → R) :
    ∃ i₀ : Fin n, ∀ j : Fin n, leR (f j) (f i₀) := by
  have ⟨i₀, _, hmax⟩ := exists_max_mem_list (finList_ne_nil hn) f
  exact ⟨i₀, fun j => hmax j (mem_finList j)⟩

theorem idxProd_const_vec {S : Type v} [CommRing S] {n : Nat} (c : S) :
    ∀ {m : Nat} (α : Idx n m), idxProd (fun _ : Fin n => c) α = rpow c m
  | 0, .nil => rfl
  | _ + 1, .cons _ tail => by
    rw [idxProd_cons, idxProd_const_vec c tail, CommRing.mul_comm c, ← rpow_succ]

private theorem domain_mul_left_cancel {D : Type v} [IntegralDomain D] {a b c : D}
    (hc : c ≠ 0) (h : c * a = c * b) : a = b := by
  have hsub : c * (a - b) = 0 := by
    rw [mul_sub_distrib, h, sub_self_eq_zero]
  cases IntegralDomain.mul_eq_zero c (a - b) hsub with
  | inl hc0 => exact False.elim (hc hc0)
  | inr hab0 => exact sub_eq_zero_iff.mp hab0

/-- Head-tail product `y_i * x_{t_1} ⋯ x_{t_d}` on `Idx n (d + 1)`. -/
def headTailProd {S : Type v} [CommRing S] {n d : Nat} (y x : Fin n → S) : Idx n (d + 1) → S
  | Idx.cons i t => y i * idxProd x t

@[simp] theorem headTailProd_cons {S : Type v} [CommRing S] {n d : Nat}
    (y x : Fin n → S) (i : Fin n) (t : Idx n d) :
    headTailProd y x (Idx.cons i t) = y i * idxProd x t := rfl

theorem int_ofNat_mul : ∀ (a b : Nat), ((a * b : Nat) : Int) = (a : Int) * (b : Int)
  | 0, _ => by omega
  | a + 1, b => by
    rw [Nat.succ_mul]
    have h1 : ((a * b + b : Nat) : Int) = ((a * b : Nat) : Int) + (b : Int) := by omega
    have h2 : ((a + 1 : Nat) : Int) = (a : Int) + 1 := by omega
    rw [h1, h2, Int.add_mul, Int.one_mul, int_ofNat_mul a b]

/-! ### 1. Qi's Entrywise `H`-Eigenvalue Bound (Complex & Real) -/

/-- Complex entrywise `H`-eigenvalue modulus bound: for any order-`(d+1)` (`d ≥ 0`),
    dimension-`n` (`n ≥ 1`) tensor `A` over `ComplexOver R` with `|A(α)|^2 ≤ B^2` (`B ≥ 0`),
    every complex eigenpair `(z, λ)` satisfies `|λ|^2 ≤ (n^d * B)^2`. -/
theorem entrywise_H_bound_complex {n d : Nat} (hn : n ≥ 1) {B : R} (_hB : leR 0 B)
    {A : Idx n (d + 1) → ComplexOver R} (hA : EntryBoundedNormSq A B)
    {z : Fin n → ComplexOver R} {lam : ComplexOver R} (heig : IsHEigenpair A z lam) :
    leR (ComplexOver.normSq lam)
        ((rpow (natCastR n) d * B) * (rpow (natCastR n) d * B)) := by
  have ⟨j₀, hj₀⟩ := heig.1
  have ⟨i₀, hmax⟩ := exists_max_fin hn (fun j => ComplexOver.normSq (z j))
  let M2 := ComplexOver.normSq (z i₀)
  have hM2_pos : ltR 0 M2 :=
    ltR_of_ltR_of_leR (ComplexOver.normSq_pos_of_ne_zero hj₀) (hmax j₀)
  have hM2d_pos : ltR 0 (rpow M2 d) := rpow_pos hM2_pos d
  have hrow := congrArg ComplexOver.normSq (heig.2 i₀)
  rw [ComplexOver.normSq_mul, ComplexOver.normSq_rpow] at hrow
  -- Bound `normSq (contract A z i₀)` via `complex_normSq_sum_le`
  let w : Idx n d → ComplexOver R := fun t => A (Idx.cons i₀ t) * idxProd z t
  have hcs := complex_normSq_sum_le (idxList n d) w
  rw [length_idxList, natCastR_pow] at hcs
  have hterm : ∀ t : Idx n d, t ∈ idxList n d →
      leR (ComplexOver.normSq (w t)) ((B * B) * rpow M2 d) := by
    intro t _
    dsimp only [w]
    rw [ComplexOver.normSq_mul, normSq_idxProd]
    exact mul_leR_mul_nonneg
      (ComplexOver.normSq_nonneg _)
      (idxProd_nonneg (fun j => ComplexOver.normSq_nonneg (z j)) t)
      (hA (Idx.cons i₀ t))
      (idxProd_leR_rpow_of_leR (fun j => ComplexOver.normSq_nonneg (z j)) hmax t)
  have hsum_le := sumList_leR hterm
  rw [sumList_const, length_idxList, natCastR_pow] at hsum_le
  have hnd_nn : leR (0 : R) (rpow (natCastR n) d) := rpow_nonneg (natCastR_nonneg (R := R) n) d
  have hchain : leR (ComplexOver.normSq lam * rpow M2 d)
      (((rpow (natCastR n) d * B) * (rpow (natCastR n) d * B)) * rpow M2 d) := by
    rw [← hrow]
    change leR (ComplexOver.normSq (sumList (idxList n d) w)) _
    have h1 := leR_trans hcs (mul_leR_mul_of_nonneg_left hnd_nn hsum_le)
    have hrew : rpow (natCastR n) d * (rpow (natCastR n) d * ((B * B) * rpow M2 d)) =
        ((rpow (natCastR n) d * B) * (rpow (natCastR n) d * B)) * rpow M2 d := by
      let N := rpow (natCastR n : R) d
      calc
        N * (N * ((B * B) * rpow M2 d)) = ((N * N) * (B * B)) * rpow M2 d := by
          rw [← CommRing.mul_assoc N N, ← CommRing.mul_assoc (N * N)]
        _ = ((N * B) * (N * B)) * rpow M2 d := by
          have hNB : (N * N) * (B * B) = (N * B) * (N * B) := by
            rw [CommRing.mul_assoc N N, mul_left_comm_eq N B B, ← CommRing.mul_assoc]
          rw [hNB]
    rw [hrew] at h1
    exact h1
  exact leR_of_mul_leR_mul_pos_right hM2d_pos hchain

/-- Real `H`-eigenvalue modulus bound: for `A : Idx n (d + 1) → R` with `|A(α)| ≤ B` (`B ≥ 0`),
    every `H`-eigenpair `(x, λ)` satisfies `|λ| ≤ n^d * B`. -/
theorem entrywise_H_bound_real {n d : Nat} (hn : n ≥ 1) {B : R} (hB : leR 0 B)
    {A : Idx n (d + 1) → R} (hA : EntryBoundedAbs A B)
    {x : Fin n → R} {lam : R} (heig : IsHEigenpair A x lam) :
    leR (absR lam) (rpow (natCastR n) d * B) := by
  let Ac : Idx n (d + 1) → ComplexOver R := fun α => ComplexOver.ofReal (A α)
  let xc : Fin n → ComplexOver R := fun j => ComplexOver.ofReal (x j)
  have hAc : EntryBoundedNormSq Ac B := by
    intro α
    dsimp only [Ac]
    rw [ComplexOver.normSq_ofReal]
    exact (sq_leR_sq_iff_absR_leR hB).mpr (hA α)
  have heig_c : IsHEigenpair Ac xc (ComplexOver.ofReal lam) := by
    refine ⟨?_, ?_⟩
    · have ⟨j₀, hj₀⟩ := heig.1
      refine ⟨j₀, fun h0 => hj₀ (congrArg ComplexOver.re h0)⟩
    · intro i
      dsimp only [Ac, xc]
      rw [← ofReal_contract, heig.2 i, ComplexOver.ofReal_mul, ComplexOver.ofReal_rpow]
  have hb := entrywise_H_bound_complex hn hB hAc heig_c
  rw [ComplexOver.normSq_ofReal] at hb
  have hNB_nn : leR 0 (rpow (natCastR n) d * B) :=
    mul_nonneg_leR (rpow_nonneg (natCastR_nonneg n) d) hB
  exact (sq_leR_sq_iff_absR_leR hNB_nn).mp hb

/-- Sharp attainment of Qi's entrywise `H`-bound by the all-ones tensor `J_{m, n}` at `x = 1`. -/
theorem allOnes_attains_H_bound (n d : Nat) (hn : n ≥ 1) :
    IsSymmetric (allOnesTensor n (d + 1) : Idx n (d + 1) → R) ∧
    EntryBoundedAbs (allOnesTensor n (d + 1) : Idx n (d + 1) → R) 1 ∧
    IsHEigenpair (allOnesTensor n (d + 1) : Idx n (d + 1) → R)
      (fun _ => 1) (rpow (natCastR n) d) := by
  refine ⟨isSymmetric_allOnesTensor n (d + 1), ?_, ?_⟩
  · intro _
    unfold allOnesTensor
    rw [absR_of_nonneg zero_ltR_one.1]
    exact leR_refl 1
  · refine ⟨⟨⟨0, hn⟩, IntegralDomain.zero_ne_one.symm⟩, ?_⟩
    intro i
    rw [contract_allOnesTensor, sumFin_const, mul_one_eq, rpow_one_base, mul_one_eq]

/-! ### 2. Complete Rigidity Characterizations of Qi's Entrywise `H`-Bound -/

/-- Complete complex rigidity theorem for `|λ|^2 = (n^d * B)^2` (`n ≥ 1, d ≥ 1, B > 0`):
    if a symmetric complex tensor `A` with `|A(α)|^2 ≤ B^2` attains the bound at `(z, λ)`,
    then there exists `i₀` with `M_2 = |z_{i₀}|^2 > 0` such that:
    (1) all coordinates of `z` have equal modulus (`|z_j|^2 = M_2`),
    (2) all entries of `A` saturate the modulus bound (`|A(α)|^2 = B^2`),
    (3) all coordinates satisfy `z_i^{d+1} = z_j^{d+1}` (`(d+1)`-th root-of-unity phases), and
    (4) `A` satisfies the rank-`1` factorization `n^d M_2^{d+1} A(α) = (λ z_{i₀}^{d+1}) ∏ conj(z_{α_r})`. -/
theorem entrywise_H_rigidity_complex {n d : Nat} (hn : n ≥ 1) (hd : d ≥ 1)
    {B : R} (hB : ltR 0 B)
    {A : Idx n (d + 1) → ComplexOver R} (hSym : IsSymmetric A) (hA : EntryBoundedNormSq A B)
    {z : Fin n → ComplexOver R} {lam : ComplexOver R} (heig : IsHEigenpair A z lam)
    (heq_lam : ComplexOver.normSq lam = (rpow (natCastR n) d * B) * (rpow (natCastR n) d * B)) :
    ∃ i₀ : Fin n,
      ltR 0 (ComplexOver.normSq (z i₀)) ∧
      (∀ j : Fin n, ComplexOver.normSq (z j) = ComplexOver.normSq (z i₀)) ∧
      (∀ α : Idx n (d + 1), ComplexOver.normSq (A α) = B * B) ∧
      (∀ i j : Fin n, rpow (z i) (d + 1) = rpow (z j) (d + 1)) ∧
      (∀ α : Idx n (d + 1),
        ComplexOver.ofReal (rpow (natCastR n) d * rpow (ComplexOver.normSq (z i₀)) (d + 1)) * A α =
        (lam * rpow (z i₀) (d + 1)) * idxProd (fun j => ComplexOver.conj (z j)) α) := by
  have ⟨j₀, hj₀⟩ := heig.1
  have ⟨i₀, hmax⟩ := exists_max_fin hn (fun j => ComplexOver.normSq (z j))
  let M2 := ComplexOver.normSq (z i₀)
  have hM2_pos : ltR 0 M2 :=
    ltR_of_ltR_of_leR (ComplexOver.normSq_pos_of_ne_zero hj₀) (hmax j₀)
  have hM2d_pos : ltR 0 (rpow M2 d) := rpow_pos hM2_pos d
  have hnd_pos : ltR (0 : R) (rpow (natCastR n) d) := rpow_pos (natCastR_pos hn) d
  have hBB_pos : ltR 0 (B * B) := mul_pos_ltR hB hB
  -- Helper: for ANY row `i` with `normSq (z i) = M2`, both Cauchy-Schwarz and term saturation hold
  have hrow_sat : ∀ i : Fin n, ComplexOver.normSq (z i) = M2 →
      (∀ t : Idx n d,
        ComplexOver.normSq (A (Idx.cons i t)) * idxProd (fun j => ComplexOver.normSq (z j)) t =
          (B * B) * rpow M2 d) ∧
      (∀ t : Idx n d,
        ComplexOver.ofReal (rpow (natCastR n) d) * (A (Idx.cons i t) * idxProd z t) =
          lam * rpow (z i) d) := by
    intro i hiM
    let wi : Idx n d → ComplexOver R := fun t => A (Idx.cons i t) * idxProd z t
    have hrow := congrArg ComplexOver.normSq (heig.2 i)
    rw [ComplexOver.normSq_mul, ComplexOver.normSq_rpow, hiM, heq_lam] at hrow
    have hcs := complex_normSq_sum_le (idxList n d) wi
    rw [length_idxList, natCastR_pow] at hcs
    have hterm_le : ∀ t : Idx n d, t ∈ idxList n d →
        leR (ComplexOver.normSq (wi t)) ((B * B) * rpow M2 d) := by
      intro t _
      dsimp only [wi]
      rw [ComplexOver.normSq_mul, normSq_idxProd]
      exact mul_leR_mul_nonneg
        (ComplexOver.normSq_nonneg _)
        (idxProd_nonneg (fun j => ComplexOver.normSq_nonneg (z j)) t)
        (hA (Idx.cons i t))
        (idxProd_leR_rpow_of_leR (fun j => ComplexOver.normSq_nonneg (z j)) hmax t)
    have hsum_le := sumList_leR hterm_le
    have hconst_eq : sumList (idxList n d) (fun _ => (B * B) * rpow M2 d) =
        rpow (natCastR n) d * ((B * B) * rpow M2 d) := by
      rw [sumList_const, length_idxList, natCastR_pow]
    have hrew : rpow (natCastR n) d * (rpow (natCastR n) d * ((B * B) * rpow M2 d)) =
        ((rpow (natCastR n) d * B) * (rpow (natCastR n) d * B)) * rpow M2 d := by
      let N := rpow (natCastR n : R) d
      calc
        N * (N * ((B * B) * rpow M2 d)) = ((N * N) * (B * B)) * rpow M2 d := by
          rw [← CommRing.mul_assoc N N, ← CommRing.mul_assoc (N * N)]
        _ = ((N * B) * (N * B)) * rpow M2 d := by
          rw [CommRing.mul_assoc N N, mul_left_comm_eq N B B, ← CommRing.mul_assoc]
    have hupper : leR (rpow (natCastR n) d * sumList (idxList n d) (fun t => ComplexOver.normSq (wi t)))
        (ComplexOver.normSq (contract A z i)) := by
      rw [hrow, ← hrew, ← hconst_eq]
      exact mul_leR_mul_of_nonneg_left hnd_pos.1 hsum_le
    have hcs_eq : ComplexOver.normSq (sumList (idxList n d) wi) =
        natCastR (idxList n d).length * sumList (idxList n d) (fun t => ComplexOver.normSq (wi t)) := by
      rw [length_idxList, natCastR_pow]
      exact leR_antisymm hcs hupper
    have hsum_eq : sumList (idxList n d) (fun t => ComplexOver.normSq (wi t)) =
        sumList (idxList n d) (fun _ => (B * B) * rpow M2 d) := by
      apply eq_of_mul_eq_mul_ne_zero_left hnd_pos.2.symm
      rw [hconst_eq, hrew, ← hrow]
      change rpow (natCastR n) d * sumList (idxList n d) (fun t => ComplexOver.normSq (wi t)) =
             ComplexOver.normSq (sumList (idxList n d) wi)
      rw [hcs_eq, length_idxList, natCastR_pow]
    have hterm_eq := eq_of_sumList_eq_of_leR hterm_le hsum_eq
    have ⟨_, hconst_wi⟩ := complex_normSq_sum_eq_const hcs_eq
    refine ⟨?_, ?_⟩
    · intro t
      have ht := hterm_eq t (mem_idxList t)
      dsimp only [wi] at ht
      rw [ComplexOver.normSq_mul, normSq_idxProd] at ht
      exact ht
    · intro t
      have hw := hconst_wi t (mem_idxList t)
      rw [length_idxList, ← ComplexOver.ofReal_natCastR, natCastR_pow] at hw
      change ComplexOver.ofReal (rpow (natCastR n) d) * wi t = contract A z i at hw
      rw [heig.2 i] at hw
      exact hw
  -- Step A: deduce `normSq (z j) = M2` for ALL `j` from row `i₀` at `constIdx j d`
  have ⟨hsat_i0, _⟩ := hrow_sat i₀ rfl
  have hz_mod : ∀ j : Fin n, ComplexOver.normSq (z j) = M2 := by
    intro j
    have ht := hsat_i0 (constIdx j d)
    rw [idxProd_constIdx] at ht
    by_cases heq_j : ComplexOver.normSq (z j) = M2
    · exact heq_j
    · have hlt_j : ltR (ComplexOver.normSq (z j)) M2 := ⟨hmax j, heq_j⟩
      have hpow_lt : ltR (rpow (ComplexOver.normSq (z j)) d) (rpow M2 d) :=
        rpow_ltR_rpow_of_nonneg (ComplexOver.normSq_nonneg (z j)) hlt_j hd
      have hprod_le : leR (ComplexOver.normSq (A (Idx.cons i₀ (constIdx j d))) *
          rpow (ComplexOver.normSq (z j)) d)
          ((B * B) * rpow (ComplexOver.normSq (z j)) d) :=
        mul_leR_mul_of_nonneg_right
          (rpow_nonneg (ComplexOver.normSq_nonneg (z j)) d)
          (hA _)
      have hprod_lt : ltR ((B * B) * rpow (ComplexOver.normSq (z j)) d) ((B * B) * rpow M2 d) := by
        refine ⟨mul_leR_mul_of_nonneg_left hBB_pos.1 hpow_lt.1, ?_⟩
        intro heq_p
        exact hpow_lt.2 (eq_of_mul_eq_mul_ne_zero_left hBB_pos.2.symm heq_p)
      have hcontr := ltR_of_leR_of_ltR hprod_le hprod_lt
      rw [ht] at hcontr
      exact False.elim (ltR_irrefl _ hcontr)
  -- Step B: every entry of `A` has `normSq (A α) = B * B`, and every row/tail satisfies constancy
  have hA_mod : ∀ α : Idx n (d + 1), ComplexOver.normSq (A α) = B * B := by
    intro α
    cases α with
    | cons i t =>
      have ⟨hsat_i, _⟩ := hrow_sat i (hz_mod i)
      have ht := hsat_i t
      have hprod_eq : idxProd (fun j => ComplexOver.normSq (z j)) t = rpow M2 d := by
        have hc : (fun j : Fin n => ComplexOver.normSq (z j)) = (fun _ => M2) :=
          funext hz_mod
        rw [hc, idxProd_const_vec]
      rw [hprod_eq, CommRing.mul_comm (ComplexOver.normSq (A (Idx.cons i t))),
          CommRing.mul_comm (B * B)] at ht
      exact eq_of_mul_eq_mul_ne_zero_left hM2d_pos.2.symm ht
  have hterm_all : ∀ (i : Fin n) (t : Idx n d),
      ComplexOver.ofReal (rpow (natCastR n) d) * (A (Idx.cons i t) * idxProd z t) =
        lam * rpow (z i) d :=
    fun i t => (hrow_sat i (hz_mod i)).2 t
  -- Step C: symmetry swaps first two indices `i, j` (using `d = (d - 1) + 1`)
  have hlam_ne : lam ≠ 0 := by
    intro h0
    have hn0 : ComplexOver.normSq lam = 0 := (ComplexOver.normSq_eq_zero_iff lam).mpr h0
    rw [heq_lam] at hn0
    have hNB_pos : ltR 0 (rpow (natCastR n) d * B) := mul_pos_ltR hnd_pos hB
    exact (mul_pos_ltR hNB_pos hNB_pos).2 hn0.symm
  have hz_pow_eq : ∀ i j : Fin n, rpow (z i) (d + 1) = rpow (z j) (d + 1) := by
    intro i j
    cases d with
    | zero => omega
    | succ d' =>
      let t₀ : Idx n d' := constIdx i₀ d'
      have eq_i := congrArg (fun u => u * z i) (hterm_all i (Idx.cons j t₀))
      have eq_j := congrArg (fun u => u * z j) (hterm_all j (Idx.cons i t₀))
      dsimp only at eq_i eq_j
      rw [CommRing.mul_assoc lam, ← rpow_succ] at eq_i eq_j
      have hA_swap : A (Idx.cons i (Idx.cons j t₀)) = A (Idx.cons j (Idx.cons i t₀)) :=
        hSym _ _ (PermIdx.swap i j t₀)
      have hlhs : (ComplexOver.ofReal (rpow (natCastR n) (d' + 1)) *
          (A (Idx.cons i (Idx.cons j t₀)) * idxProd z (Idx.cons j t₀))) * z i =
          (ComplexOver.ofReal (rpow (natCastR n) (d' + 1)) *
          (A (Idx.cons j (Idx.cons i t₀)) * idxProd z (Idx.cons i t₀))) * z j := by
        rw [hA_swap, idxProd_cons, idxProd_cons,
            CommRing.mul_assoc (ComplexOver.ofReal _),
            CommRing.mul_assoc (ComplexOver.ofReal _),
            CommRing.mul_assoc (A _), CommRing.mul_assoc (A _),
            CommRing.mul_comm (z j * idxProd z t₀) (z i),
            CommRing.mul_comm (z i * idxProd z t₀) (z j),
            ← CommRing.mul_assoc (z i) (z j), ← CommRing.mul_assoc (z j) (z i),
            CommRing.mul_comm (z i) (z j)]
      rw [hlhs] at eq_i
      have hlam_eq : lam * rpow (z i) (d' + 2) = lam * rpow (z j) (d' + 2) :=
        Eq.trans eq_i.symm eq_j
      exact domain_mul_left_cancel hlam_ne hlam_eq
  -- Step D: Rank-1 factorization via `z_k * conj(z_k) = ofReal M2`
  have hrank1 : ∀ α : Idx n (d + 1),
      ComplexOver.ofReal (rpow (natCastR n) d * rpow M2 (d + 1)) * A α =
      (lam * rpow (z i₀) (d + 1)) * idxProd (fun j => ComplexOver.conj (z j)) α := by
    intro α
    cases α with
    | cons i t =>
      have eq1 := congrArg (fun u => u * z i) (hterm_all i t)
      dsimp only at eq1
      rw [CommRing.mul_assoc lam, ← rpow_succ, hz_pow_eq i i₀] at eq1
      have hlhs1 : (ComplexOver.ofReal (rpow (natCastR n) d) *
          (A (Idx.cons i t) * idxProd z t)) * z i =
          (ComplexOver.ofReal (rpow (natCastR n) d) * A (Idx.cons i t)) *
          idxProd z (Idx.cons i t) := by
        rw [idxProd_cons, ← CommRing.mul_assoc (ComplexOver.ofReal _) (A _),
            CommRing.mul_assoc (ComplexOver.ofReal _ * A _),
            CommRing.mul_comm (idxProd z t) (z i)]
      rw [hlhs1] at eq1
      have eq2 := congrArg (fun u => u * idxProd (fun j => ComplexOver.conj (z j)) (Idx.cons i t)) eq1
      dsimp only at eq2
      have hzc : idxProd z (Idx.cons i t) *
          idxProd (fun j => ComplexOver.conj (z j)) (Idx.cons i t) =
          ComplexOver.ofReal (rpow M2 (d + 1)) := by
        rw [← idxProd_mul_vec]
        have hveq : (fun j : Fin n => z j * ComplexOver.conj (z j)) =
            (fun _ => ComplexOver.ofReal M2) := by
          funext j
          rw [ComplexOver.mul_conj_eq, hz_mod j]
        rw [hveq, ComplexOver.ofReal_rpow, idxProd_const_vec]
      rw [CommRing.mul_assoc (ComplexOver.ofReal _ * A _), hzc,
          CommRing.mul_assoc (ComplexOver.ofReal (rpow (natCastR n) d)),
          CommRing.mul_comm (A _), ← CommRing.mul_assoc,
          ← ComplexOver.ofReal_mul] at eq2
      exact eq2
  exact ⟨i₀, hM2_pos, hz_mod, hA_mod, hz_pow_eq, hrank1⟩

/-- Nonnegative symmetric tensor rigidity: if `0 ≤ A(α) ≤ B` (`B > 0, n ≥ 1, d ≥ 1`) and `A`
    attains `|λ|^2 = (n^d * B)^2` at ANY complex eigenpair `(z, λ)`, then `A = B * J_{m, n}`
    uniquely (`∀ α, A α = B`). -/
theorem entrywise_H_rigidity_nonneg {n d : Nat} (hn : n ≥ 1) (hd : d ≥ 1)
    {B : R} (hB : ltR 0 B)
    {A : Idx n (d + 1) → R} (hSym : IsSymmetric A)
    (hnonneg : ∀ α, leR 0 (A α)) (hle : ∀ α, leR (A α) B)
    {z : Fin n → ComplexOver R} {lam : ComplexOver R}
    (heig : IsHEigenpair (fun α => ComplexOver.ofReal (A α)) z lam)
    (heq_lam : ComplexOver.normSq lam = (rpow (natCastR n) d * B) * (rpow (natCastR n) d * B)) :
    ∀ α : Idx n (d + 1), A α = B := by
  have hSym_c : IsSymmetric (fun α => ComplexOver.ofReal (A α)) := by
    intro u v hp
    dsimp only
    rw [hSym u v hp]
  have hBound_c : EntryBoundedNormSq (fun α => ComplexOver.ofReal (A α)) B := by
    intro α
    rw [ComplexOver.normSq_ofReal]
    exact mul_leR_mul_nonneg (hnonneg α) (hnonneg α) (hle α) (hle α)
  have ⟨_, _, _, hA_mod, _, _⟩ :=
    entrywise_H_rigidity_complex hn hd hB hSym_c hBound_c heig heq_lam
  intro α
  have hsq := hA_mod α
  rw [ComplexOver.normSq_ofReal] at hsq
  have habs := (sq_eq_sq_iff_absR_eq hB.1).mp hsq
  rw [absR_of_nonneg (hnonneg α)] at habs
  exact habs

/-- Odd-order real rigidity (`m = 2k + 3 ≥ 3`): if a real symmetric tensor `A` with `|A(α)| ≤ B`
    (`B > 0`) attains `|λ| = n^{2k+2} * B` at a real `H`-eigenpair `(x, λ)`, then `A` is
    uniquely `+B * J_{m, n}` or `-B * J_{m, n}`. -/
theorem entrywise_H_rigidity_odd_real {n k : Nat} (hn : n ≥ 1)
    {B : R} (hB : ltR 0 B)
    {A : Idx n (2 * k + 3) → R} (hSym : IsSymmetric A) (hA : EntryBoundedAbs A B)
    {x : Fin n → R} {lam : R} (heig : IsHEigenpair A x lam)
    (heq_lam : absR lam = rpow (natCastR n) (2 * k + 2) * B) :
    (∀ α : Idx n (2 * k + 3), A α = B) ∨ (∀ α : Idx n (2 * k + 3), A α = -B) := by
  let Ac : Idx n (2 * k + 3) → ComplexOver R := fun α => ComplexOver.ofReal (A α)
  let xc : Fin n → ComplexOver R := fun j => ComplexOver.ofReal (x j)
  have hSym_c : IsSymmetric Ac := fun u v hp => congrArg ComplexOver.ofReal (hSym u v hp)
  have hAc : EntryBoundedNormSq Ac B := by
    intro α; dsimp only [Ac]; rw [ComplexOver.normSq_ofReal]
    exact (sq_leR_sq_iff_absR_leR hB.1).mpr (hA α)
  have heig_c : IsHEigenpair Ac xc (ComplexOver.ofReal lam) := by
    refine ⟨?_, ?_⟩
    · have ⟨j₀, hj₀⟩ := heig.1
      exact ⟨j₀, fun h0 => hj₀ (congrArg ComplexOver.re h0)⟩
    · intro i; dsimp only [Ac, xc]
      rw [← ofReal_contract, heig.2 i, ComplexOver.ofReal_mul, ComplexOver.ofReal_rpow]
  have hNB_pos : ltR 0 (rpow (natCastR n) (2 * k + 2) * B) :=
    mul_pos_ltR (rpow_pos (natCastR_pos hn) _) hB
  have hsq_lam : ComplexOver.normSq (ComplexOver.ofReal lam) =
      (rpow (natCastR n) (2 * k + 2) * B) * (rpow (natCastR n) (2 * k + 2) * B) := by
    rw [ComplexOver.normSq_ofReal]
    exact (sq_eq_sq_iff_absR_eq hNB_pos.1).mpr heq_lam
  have ⟨i₀, hM2_pos, hz_mod, _, hz_pow_eq, hrank1⟩ :=
    entrywise_H_rigidity_complex (d := 2 * k + 2) hn (by omega) hB hSym_c hAc heig_c hsq_lam
  dsimp only [xc] at hM2_pos hz_mod hz_pow_eq hrank1
  rw [ComplexOver.normSq_ofReal] at hM2_pos
  have hxi0_ne : x i₀ ≠ 0 := by
    intro h0; rw [h0, mul_zero_eq] at hM2_pos; exact ltR_irrefl 0 hM2_pos
  -- Show `x j = x i₀` for every `j`
  have hxj_eq : ∀ j : Fin n, x j = x i₀ := by
    intro j
    have hsq := hz_mod j
    rw [ComplexOver.normSq_ofReal, ComplexOver.normSq_ofReal] at hsq
    have hdiff : (x j - x i₀) * (x j + x i₀) = 0 := by
      rw [diff_sq_eq, hsq, sub_self_eq_zero]
    cases IntegralDomain.mul_eq_zero _ _ hdiff with
    | inl hminus => exact sub_eq_zero_iff.mp hminus
    | inr hplus =>
      have hneg : x j = -(x i₀) := by
        rw [CommRing.add_comm] at hplus
        exact (neg_eq_of_add_eq_zero hplus).symm
      have hp := hz_pow_eq j i₀
      rw [← ComplexOver.ofReal_rpow, ← ComplexOver.ofReal_rpow] at hp
      have hp_re : rpow (x j) (2 * (k + 1) + 1) = rpow (x i₀) (2 * (k + 1) + 1) :=
        congrArg ComplexOver.re hp
      rw [hneg, rpow_neg_odd] at hp_re
      have h2pow : natCastR 2 * rpow (x i₀) (2 * (k + 1) + 1) = 0 := by
        rw [natCastR_two, CommRing.right_distrib, one_mul_eq]
        have hsum : rpow (x i₀) (2 * (k + 1) + 1) + -(rpow (x i₀) (2 * (k + 1) + 1)) = 0 :=
          add_neg_cancel _
        rw [hp_re] at hsum
        exact hsum
      have hp0 := eq_of_mul_eq_mul_ne_zero_left
        (a := rpow (x i₀) (2 * (k + 1) + 1)) (b := 0) (two_pos (R := R)).2.symm
        (by rw [mul_zero_eq]; exact h2pow)
      exact False.elim (rpow_ne_zero hxi0_ne _ hp0)
  -- Extract `rpow n (2k+2) * A α = lam` from `hrank1`
  have hA_const : ∀ α : Idx n (2 * k + 3),
      rpow (natCastR n) (2 * k + 2) * A α = lam := by
    intro α
    have hr := hrank1 α
    have hconj : (fun j : Fin n => ComplexOver.conj (ComplexOver.ofReal (x j))) =
        (fun _ => ComplexOver.ofReal (x i₀)) := by
      funext j
      rw [hxj_eq j]
      apply ComplexOver.ext
      · rfl
      · exact neg_zero_eq
    have hprod : idxProd (fun j => ComplexOver.conj (ComplexOver.ofReal (x j))) α =
        ComplexOver.ofReal (rpow (x i₀) (2 * k + 3)) := by
      rw [hconj, ← ofReal_idxProd, idxProd_const_vec]
    dsimp only [Ac] at hr
    rw [ComplexOver.normSq_ofReal, hprod, ← ComplexOver.ofReal_rpow, ← ComplexOver.ofReal_mul,
        ← ComplexOver.ofReal_mul, ← ComplexOver.ofReal_mul] at hr
    have hr_re := congrArg ComplexOver.re hr
    dsimp only [ComplexOver.ofReal] at hr_re
    have hpow_sq : rpow (x i₀) (2 * k + 3) * rpow (x i₀) (2 * k + 3) =
        rpow (x i₀ * x i₀) (2 * k + 3) := (rpow_mul_distrib _ _ _).symm
    rw [CommRing.mul_assoc lam, hpow_sq,
        CommRing.mul_assoc (rpow (natCastR n) (2 * k + 2)),
        mul_left_comm_eq (rpow (natCastR n) (2 * k + 2)) (rpow (x i₀ * x i₀) (2 * k + 3)) (A α),
        ← CommRing.mul_assoc (rpow (x i₀ * x i₀) (2 * k + 3))] at hr_re
    have hM2m_pos : ltR 0 (rpow (x i₀ * x i₀) (2 * k + 3)) := rpow_pos hM2_pos (2 * k + 3)
    rw [CommRing.mul_assoc (rpow (x i₀ * x i₀) (2 * k + 3)),
        CommRing.mul_comm lam (rpow (x i₀ * x i₀) (2 * k + 3))] at hr_re
    exact eq_of_mul_eq_mul_ne_zero_left hM2m_pos.2.symm hr_re
  have hnd_ne : (rpow (natCastR n) (2 * k + 2) : R) ≠ 0 :=
    (rpow_pos (natCastR_pos hn) (2 * k + 2)).2.symm
  cases leR_total 0 lam with
  | inl hlam_nn =>
    rw [absR_of_nonneg hlam_nn] at heq_lam
    left
    intro α
    apply eq_of_mul_eq_mul_ne_zero_left hnd_ne
    rw [hA_const α, heq_lam]
  | inr hlam_np =>
    rw [absR_of_nonpos hlam_np] at heq_lam
    have hlam_eq : lam = rpow (natCastR n) (2 * k + 2) * (-B) := by
      have h1 := congrArg Neg.neg heq_lam
      rw [neg_neg_eq, ← mul_neg_eq] at h1
      exact h1
    right
    intro α
    apply eq_of_mul_eq_mul_ne_zero_left hnd_ne
    rw [hA_const α, hlam_eq]

/-- Even-order real rigidity (`m = 2k + 2 ≥ 2`): if a real symmetric tensor `A` with `|A(α)| ≤ B`
    (`B > 0`) attains `|λ| = n^{2k+1} * B` at a real `H`-eigenpair `(x, λ)`, then `A = ± B * s^{⊗ m}`
    for some sign vector `s : Fin n → {-1, +1}`. -/
theorem entrywise_H_rigidity_even_real {n k : Nat} (hn : n ≥ 1)
    {B : R} (hB : ltR 0 B)
    {A : Idx n (2 * k + 2) → R} (hSym : IsSymmetric A) (hA : EntryBoundedAbs A B)
    {x : Fin n → R} {lam : R} (heig : IsHEigenpair A x lam)
    (heq_lam : absR lam = rpow (natCastR n) (2 * k + 1) * B) :
    ∃ s : Fin n → R,
      (∀ j : Fin n, s j = 1 ∨ s j = -1) ∧
      (A = rankOneTensor B s ∨ A = rankOneTensor (-B) s) := by
  let Ac : Idx n (2 * k + 2) → ComplexOver R := fun α => ComplexOver.ofReal (A α)
  let xc : Fin n → ComplexOver R := fun j => ComplexOver.ofReal (x j)
  have hSym_c : IsSymmetric Ac := fun u v hp => congrArg ComplexOver.ofReal (hSym u v hp)
  have hAc : EntryBoundedNormSq Ac B := by
    intro α; dsimp only [Ac]; rw [ComplexOver.normSq_ofReal]
    exact (sq_leR_sq_iff_absR_leR hB.1).mpr (hA α)
  have heig_c : IsHEigenpair Ac xc (ComplexOver.ofReal lam) := by
    refine ⟨?_, ?_⟩
    · have ⟨j₀, hj₀⟩ := heig.1
      exact ⟨j₀, fun h0 => hj₀ (congrArg ComplexOver.re h0)⟩
    · intro i; dsimp only [Ac, xc]
      rw [← ofReal_contract, heig.2 i, ComplexOver.ofReal_mul, ComplexOver.ofReal_rpow]
  have hNB_pos : ltR 0 (rpow (natCastR n) (2 * k + 1) * B) :=
    mul_pos_ltR (rpow_pos (natCastR_pos hn) _) hB
  have hsq_lam : ComplexOver.normSq (ComplexOver.ofReal lam) =
      (rpow (natCastR n) (2 * k + 1) * B) * (rpow (natCastR n) (2 * k + 1) * B) := by
    rw [ComplexOver.normSq_ofReal]
    exact (sq_eq_sq_iff_absR_eq hNB_pos.1).mpr heq_lam
  have ⟨i₀, hM2_pos, hz_mod, _, _, hrank1⟩ :=
    entrywise_H_rigidity_complex (d := 2 * k + 1) hn (by omega) hB hSym_c hAc heig_c hsq_lam
  dsimp only [xc] at hM2_pos hz_mod hrank1
  rw [ComplexOver.normSq_ofReal] at hM2_pos
  let s : Fin n → R := fun j =>
    haveI := Classical.propDecidable (x j = x i₀)
    if x j = x i₀ then 1 else -1
  have hs_pm : ∀ j : Fin n, s j = 1 ∨ s j = -1 := by
    intro j
    dsimp only [s]
    by_cases h : x j = x i₀ <;> simp [h]
  have hx_eq : ∀ j : Fin n, x j = s j * x i₀ := by
    intro j
    have hsq := hz_mod j
    rw [ComplexOver.normSq_ofReal, ComplexOver.normSq_ofReal] at hsq
    have hdiff : (x j - x i₀) * (x j + x i₀) = 0 := by
      rw [diff_sq_eq, hsq, sub_self_eq_zero]
    dsimp only [s]
    by_cases h : x j = x i₀
    · rw [if_pos h, one_mul_eq]; exact h
    · rw [if_neg h]
      cases IntegralDomain.mul_eq_zero _ _ hdiff with
      | inl hminus => exact False.elim (h (sub_eq_zero_iff.mp hminus))
      | inr hplus =>
        rw [neg_mul_eq, one_mul_eq]
        rw [CommRing.add_comm] at hplus
        exact (neg_eq_of_add_eq_zero hplus).symm
  have hA_rel : ∀ α : Idx n (2 * k + 2),
      rpow (natCastR n) (2 * k + 1) * A α = lam * idxProd s α := by
    intro α
    have hr := hrank1 α
    have hconj : (fun j : Fin n => ComplexOver.conj (ComplexOver.ofReal (x j))) =
        (fun j => ComplexOver.ofReal (s j * x i₀)) := by
      funext j
      rw [hx_eq j]
      apply ComplexOver.ext
      · rfl
      · exact neg_zero_eq
    have hprod : idxProd (fun j => ComplexOver.conj (ComplexOver.ofReal (x j))) α =
        ComplexOver.ofReal (idxProd s α * rpow (x i₀) (2 * k + 2)) := by
      rw [hconj, ← ofReal_idxProd, idxProd_mul_vec, idxProd_const_vec]
    dsimp only [Ac] at hr
    rw [ComplexOver.normSq_ofReal, hprod, ← ComplexOver.ofReal_rpow, ← ComplexOver.ofReal_mul,
        ← ComplexOver.ofReal_mul, ← ComplexOver.ofReal_mul] at hr
    have hr_re := congrArg ComplexOver.re hr
    dsimp only [ComplexOver.ofReal] at hr_re
    have hM2_split : rpow (x i₀ * x i₀) (2 * k + 2) =
        rpow (x i₀) (2 * k + 2) * rpow (x i₀) (2 * k + 2) :=
      rpow_mul_distrib _ _ _
    -- Cancel `rpow (x i₀ * x i₀) (2 * k + 2) > 0`
    have hrhs_rew : (lam * rpow (x i₀) (2 * k + 2)) * (idxProd s α * rpow (x i₀) (2 * k + 2)) =
        rpow (x i₀ * x i₀) (2 * k + 2) * (lam * idxProd s α) := by
      rw [hM2_split]
      calc
        (lam * rpow (x i₀) (2 * k + 2)) * (idxProd s α * rpow (x i₀) (2 * k + 2)) =
            lam * (rpow (x i₀) (2 * k + 2) * (idxProd s α * rpow (x i₀) (2 * k + 2))) :=
          CommRing.mul_assoc _ _ _
        _ = lam * (idxProd s α * (rpow (x i₀) (2 * k + 2) * rpow (x i₀) (2 * k + 2))) := by
          rw [mul_left_comm_eq (rpow (x i₀) (2 * k + 2)) (idxProd s α)]
        _ = (lam * idxProd s α) * (rpow (x i₀) (2 * k + 2) * rpow (x i₀) (2 * k + 2)) :=
          (CommRing.mul_assoc _ _ _).symm
        _ = (rpow (x i₀) (2 * k + 2) * rpow (x i₀) (2 * k + 2)) * (lam * idxProd s α) :=
          CommRing.mul_comm _ _
    have hlhs_rew : (rpow (natCastR n) (2 * k + 1) * rpow (x i₀ * x i₀) (2 * k + 2)) * A α =
        rpow (x i₀ * x i₀) (2 * k + 2) * (rpow (natCastR n) (2 * k + 1) * A α) := by
      rw [CommRing.mul_comm (rpow (natCastR n) (2 * k + 1)), CommRing.mul_assoc]
    rw [hlhs_rew, hrhs_rew] at hr_re
    have hM2m_pos : ltR 0 (rpow (x i₀ * x i₀) (2 * k + 2)) := rpow_pos hM2_pos (2 * k + 2)
    exact eq_of_mul_eq_mul_ne_zero_left hM2m_pos.2.symm hr_re
  have hnd_ne : (rpow (natCastR n) (2 * k + 1) : R) ≠ 0 :=
    (rpow_pos (natCastR_pos hn) (2 * k + 1)).2.symm
  refine ⟨s, hs_pm, ?_⟩
  cases leR_total 0 lam with
  | inl hlam_nn =>
    rw [absR_of_nonneg hlam_nn] at heq_lam
    left
    funext α
    unfold rankOneTensor
    apply eq_of_mul_eq_mul_ne_zero_left hnd_ne
    rw [hA_rel α, heq_lam, CommRing.mul_assoc]
  | inr hlam_np =>
    rw [absR_of_nonpos hlam_np] at heq_lam
    have hlam_eq : lam = rpow (natCastR n) (2 * k + 1) * (-B) := by
      have h1 := congrArg Neg.neg heq_lam
      rw [neg_neg_eq, ← mul_neg_eq] at h1
      exact h1
    right
    funext α
    unfold rankOneTensor
    apply eq_of_mul_eq_mul_ne_zero_left hnd_ne
    rw [hA_rel α, hlam_eq, CommRing.mul_assoc]

/-! ### 3. Sharp Entrywise `Z`-Eigenvalue Bound -/

/-- Entrywise `Z`-eigenvalue modulus-squared bound: for `A : Idx n (d + 1) → R` with
    `|A(α)| ≤ B` (`B ≥ 0`), every `Z`-eigenpair `(x, λ)` satisfies `λ^2 ≤ B^2 * n^{d+1}`
    (i.e. `|λ_Z| ≤ B * n^{m/2}`). -/
theorem entrywise_Z_bound {n d : Nat} {B : R} (hB : leR 0 B)
    {A : Idx n (d + 1) → R} (hA : EntryBoundedAbs A B)
    {x : Fin n → R} {lam : R} (hz : IsZEigenpair A x lam) :
    leR (lam * lam) ((B * B) * rpow (natCastR n) (d + 1)) := by
  have hlam : lam = homForm A x := (zEigenpair_homForm_eq hz).symm
  have habs_lam : leR (absR lam) (B * rpow (sumFin (fun i => absR (x i))) (d + 1)) := by
    rw [hlam]
    unfold homForm sumIdx
    have htri := sumList_absR_leR (idxList n (d + 1)) (fun α => A α * idxProd x α)
    have hterm : ∀ α : Idx n (d + 1), α ∈ idxList n (d + 1) →
        leR (absR (A α * idxProd x α)) (B * idxProd (fun i => absR (x i)) α) := by
      intro α _
      rw [absR_mul, absR_idxProd]
      exact mul_leR_mul_of_nonneg_right (idxProd_nonneg (fun i => absR_nonneg (x i)) α) (hA α)
    have h2 := sumList_leR hterm
    rw [sumList_mul_left] at h2
    change leR _ (B * sumIdx (fun α => idxProd (fun i => absR (x i)) α)) at h2
    rw [sumIdx_idxProd] at h2
    exact leR_trans htri h2
  have hsum_abs_nn : leR 0 (sumFin (fun i => absR (x i))) :=
    sumList_nonneg (fun i _ => absR_nonneg (x i))
  have hrhs_nn : leR 0 (B * rpow (sumFin (fun i => absR (x i))) (d + 1)) :=
    mul_nonneg_leR hB (rpow_nonneg hsum_abs_nn (d + 1))
  have hsq1 : leR (lam * lam)
      ((B * B) * rpow (sumFin (fun i => absR (x i)) * sumFin (fun i => absR (x i))) (d + 1)) := by
    have h := (sq_leR_sq_iff_absR_leR hrhs_nn).mpr habs_lam
    let S1 := sumFin (fun i => absR (x i))
    have hrew : (B * rpow S1 (d + 1)) * (B * rpow S1 (d + 1)) =
        (B * B) * rpow (S1 * S1) (d + 1) := by
      rw [rpow_mul_distrib, CommRing.mul_assoc B (rpow S1 (d + 1)),
          mul_left_comm_eq (rpow S1 (d + 1)) B, ← CommRing.mul_assoc B B]
    rw [hrew] at h
    exact h
  -- Apply Cauchy-Schwarz `(∑ 1 * |x_i|)^2 ≤ (∑ 1^2) * (∑ |x_i|^2) = n * 1 = n`
  have hcs := cauchy_schwarz_list (finList n) (fun _ => (1 : R)) (fun i => absR (x i))
  have h1s : sumList (finList n) (fun i => (1 : R) * absR (x i)) =
      sumFin (fun i => absR (x i)) := by
    apply sumList_congr; intro i _; exact one_mul_eq _
  have h1sq : sumList (finList n) (fun _ => (1 : R) * 1) = natCastR n := by
    rw [mul_one_eq, sumList_const, length_finList, mul_one_eq]
  have hxsq : sumList (finList n) (fun i => absR (x i) * absR (x i)) = 1 := by
    have hc : sumList (finList n) (fun i => absR (x i) * absR (x i)) =
        sumFin (fun i => x i * x i) := by
      apply sumList_congr; intro i _; exact absR_sq (x i)
    rw [hc, hz.1]
  rw [h1s, h1sq, hxsq, mul_one_eq] at hcs
  have hpow_cs : leR
      (rpow (sumFin (fun i => absR (x i)) * sumFin (fun i => absR (x i))) (d + 1))
      (rpow (natCastR n) (d + 1)) :=
    rpow_leR_rpow_of_nonneg (sq_nonneg _) hcs (d + 1)
  exact leR_trans hsq1 (mul_leR_mul_of_nonneg_left (sq_nonneg B) hpow_cs)

/-- Exact rational attainment of the entrywise `Z`-bound `λ^2 = n^m` on square dimensions
    `n = k^2` (`k ≥ 1`): `J_{m, k^2}` at `x = (1/k, ..., 1/k) ∈ ℚ^{k^2}` has `Z`-eigenvalue `k^m`. -/
theorem allOnes_attains_Z_bound_rat (k d : Nat) (hk : k ≥ 1) :
    let n := k * k
    let x : Fin n → RatField := fun _ => RatField.mk 1 (k : Int) (by omega)
    let lam : RatField := natCastR (k ^ (d + 1))
    IsZEigenpair (allOnesTensor n (d + 1)) x lam ∧
    lam * lam = rpow (natCastR n) (d + 1) := by
  dsimp only
  let x : Fin (k * k) → RatField := fun _ => RatField.mk 1 (k : Int) (by omega)
  have hsum_x : sumFin x = natCastR k := by
    dsimp only [x]
    rw [sumFin_const, RatField.natCastR_eq_mk, RatField.natCastR_eq_mk,
        RatField.mk_mul, RatField.mk_eq_iff]
    change (((k * k : Nat) : Int) * 1) * 1 = (k : Int) * (1 * (k : Int))
    simp only [int_ofNat_mul, Int.mul_one, Int.one_mul]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- `∑ x_i^2 = k^2 * (1/k^2) = 1`
    change sumFin (fun _ : Fin (k * k) =>
      RatField.mk 1 (k : Int) (by omega) * RatField.mk 1 (k : Int) (by omega)) = 1
    rw [sumFin_const, RatField.natCastR_eq_mk, RatField.mk_mul, RatField.mk_mul]
    change RatField.mk _ _ _ = RatField.mk 1 1 (by omega)
    rw [RatField.mk_eq_iff]
    simp only [int_ofNat_mul, Int.mul_one, Int.one_mul]
  · -- `(J x^d)_i = (∑ x)^d = k^d = k^{d+1} * (1/k)`
    intro i
    rw [contract_allOnesTensor, hsum_x, ← natCastR_pow,
        RatField.natCastR_eq_mk, RatField.natCastR_eq_mk]
    rw [RatField.mk_mul, RatField.mk_eq_iff]
    simp only [Nat.pow_succ, int_ofNat_mul, Int.mul_one, Int.one_mul]
  · -- `(k^{d+1})^2 = (k^2)^{d+1}`
    rw [natCastR_pow, ← rpow_mul_distrib, ← natCastR_mul]

/-! ### 4. Banach's Frobenius `Z`-Eigenvalue Bound & Rank-`1` Rigidity -/

/-- Banach's Frobenius `Z`-eigenvalue bound: every `Z`-eigenpair `(x, λ)` of `A` satisfies
    `λ^2 ≤ ‖A‖_F^2` (so for `‖A‖_F^2 ≤ 1`, `|λ| ≤ 1`). -/
theorem frob_Z_bound {n d : Nat} {A : Idx n (d + 1) → R}
    {x : Fin n → R} {lam : R} (hz : IsZEigenpair A x lam) :
    leR (lam * lam) (frobNormSq A) := by
  have hlam : lam = homForm A x := (zEigenpair_homForm_eq hz).symm
  rw [hlam]
  unfold homForm frobNormSq sumIdx
  have hcs := cauchy_schwarz_list (idxList n (d + 1)) A (fun α => idxProd x α)
  have hx2 : sumList (idxList n (d + 1)) (fun α => idxProd x α * idxProd x α) = 1 := by
    have hc : sumList (idxList n (d + 1)) (fun α => idxProd x α * idxProd x α) =
        sumIdx (fun α : Idx n (d + 1) => idxProd (fun i => x i * x i) α) := by
      apply sumList_congr; intro α _; exact (idxProd_mul_vec x x α).symm
    rw [hc, sumIdx_idxProd, hz.1, rpow_one_base]
  rw [hx2, mul_one_eq] at hcs
  exact hcs

/-- Rank-`1` rigidity of Banach's Frobenius `Z`-bound: if `λ^2 = ‖A‖_F^2` at a `Z`-eigenpair
    `(x, λ)`, then `A = λ * x^{⊗ (d+1)}` (`rankOneTensor lam x`). -/
theorem frob_Z_rigidity {n d : Nat} {A : Idx n (d + 1) → R}
    {x : Fin n → R} {lam : R} (hz : IsZEigenpair A x lam)
    (heq : lam * lam = frobNormSq A) :
    A = rankOneTensor lam x := by
  have hlam : homForm A x = lam := zEigenpair_homForm_eq hz
  have hx2 : sumList (idxList n (d + 1)) (fun α => idxProd x α * idxProd x α) = 1 := by
    have hc : sumList (idxList n (d + 1)) (fun α => idxProd x α * idxProd x α) =
        sumIdx (fun α : Idx n (d + 1) => idxProd (fun i => x i * x i) α) := by
      apply sumList_congr; intro α _; exact (idxProd_mul_vec x x α).symm
    rw [hc, sumIdx_idxProd, hz.1, rpow_one_base]
  have hcs_eq : sumList (idxList n (d + 1)) (fun α => A α * idxProd x α) *
      sumList (idxList n (d + 1)) (fun β => A β * idxProd x β) =
      sumList (idxList n (d + 1)) (fun α => A α * A α) *
      sumList (idxList n (d + 1)) (fun β => idxProd x β * idxProd x β) := by
    change homForm A x * homForm A x = frobNormSq A * _
    rw [hlam, hx2, mul_one_eq, heq]
  have ⟨_, hprop⟩ := cauchy_schwarz_eq_cross hcs_eq
  funext α
  have hα := hprop α (mem_idxList α)
  change sumList _ _ * A α = homForm A x * idxProd x α at hα
  rw [hx2, one_mul_eq, hlam] at hα
  exact hα

/-- Sharp attainment of Banach's Frobenius `Z`-bound `‖A‖_F^2 = 1, λ = 1` by the single-variable
    monomial tensor `e_0^{⊗ (d+1)}`. -/
theorem monomial_attains_frob_Z_bound (n d : Nat) (hn : n ≥ 1) :
    let k0 : Fin n := ⟨0, hn⟩
    IsSymmetric (monomialTensor (d + 1) k0 : Idx n (d + 1) → R) ∧
    frobNormSq (monomialTensor (d + 1) k0 : Idx n (d + 1) → R) = 1 ∧
    IsZEigenpair (monomialTensor (d + 1) k0 : Idx n (d + 1) → R) (stdBasisVec k0) 1 := by
  dsimp only
  let k0 : Fin n := ⟨0, hn⟩
  have hbasis_sq : ∀ j : Fin n, stdBasisVec (S := R) k0 j * stdBasisVec k0 j = stdBasisVec k0 j := by
    intro j
    unfold stdBasisVec
    by_cases h : j = k0
    · rw [if_pos h, mul_one_eq]
    · rw [if_neg h, mul_zero_eq]
  have hsum_basis : sumFin (stdBasisVec (S := R) k0) = 1 := by
    have hc : sumFin (stdBasisVec (S := R) k0) =
        sumFin (fun j => stdBasisVec (S := R) k0 j * 1) := by
      apply sumFin_congr; intro j; exact (mul_one_eq _).symm
    rw [hc, sumFin_stdBasis_mul]
  refine ⟨isSymmetric_monomialTensor (d + 1) k0, ?_, ?_⟩
  · unfold frobNormSq monomialTensor rankOneTensor
    have hc : sumIdx (fun α : Idx n (d + 1) =>
        (1 * idxProd (stdBasisVec (S := R) k0) α) * (1 * idxProd (stdBasisVec k0) α)) =
        sumIdx (fun α : Idx n (d + 1) => idxProd (stdBasisVec (S := R) k0) α) := by
      apply sumIdx_congr; intro α
      rw [one_mul_eq, ← idxProd_mul_vec]
      congr 1; funext j; exact hbasis_sq j
    rw [hc, sumIdx_idxProd, hsum_basis, rpow_one_base]
  · refine ⟨?_, ?_⟩
    · have hc : sumFin (fun j : Fin n => stdBasisVec (S := R) k0 j * stdBasisVec k0 j) =
          sumFin (stdBasisVec (S := R) k0) := by
        apply sumFin_congr; intro j; exact hbasis_sq j
      rw [hc, hsum_basis]
    · intro i
      rw [contract_monomialTensor]
      have hk0 : stdBasisVec (S := R) k0 k0 = 1 := by unfold stdBasisVec; rw [if_pos rfl]
      rw [hk0, rpow_one_base, mul_one_eq, one_mul_eq]
      rfl

/-! ### 5. Sharp Frobenius `H`-Eigenvalue Bound (`λ^2 ≤ n^{m-2} ‖A‖_F^2`) -/

private theorem nat_even_or_odd : ∀ d : Nat, (∃ k, d = 2 * k) ∨ (∃ k, d = 2 * k + 1)
  | 0 => Or.inl ⟨0, rfl⟩
  | d + 1 => by
    cases nat_even_or_odd d with
    | inl he =>
      rcases he with ⟨k, rfl⟩
      exact Or.inr ⟨k, rfl⟩
    | inr ho =>
      rcases ho with ⟨k, rfl⟩
      exact Or.inl ⟨k + 1, by omega⟩

/-- Sharp Frobenius `H`-eigenvalue bound: for any order-`(d+2)` (`m = d + 2 ≥ 2`), dimension-`n`
    tensor `A : Idx n (d + 2) → R` and any real `H`-eigenpair `(x, λ)`,
    `λ^2 ≤ n^d * ‖A‖_F^2` (i.e., `|λ_H| ≤ n^{(m-2)/2} ‖A‖_F`). -/
theorem frob_H_bound {n d : Nat} {A : Idx n (d + 2) → R}
    {x : Fin n → R} {lam : R} (heig : IsHEigenpair A x lam) :
    leR (lam * lam) (rpow (natCastR n) d * frobNormSq A) := by
  -- Construct `y : Fin n → R` with `y_i^2 = x_i^2` and `y_i * x_i^{d+1} = |x_i|^{d+2}`
  have hex_y : ∃ y : Fin n → R,
      (∀ i : Fin n, y i * y i = x i * x i) ∧
      (∀ i : Fin n, y i * rpow (x i) (d + 1) = rpow (absR (x i)) (d + 2)) := by
    cases nat_even_or_odd d with
    | inl he =>
      rcases he with ⟨k, rfl⟩
      refine ⟨x, fun _ => rfl, fun i => ?_⟩
      have h1 : x i * rpow (x i) (2 * k + 1) = rpow (x i) (2 * (k + 1)) := by
        rw [CommRing.mul_comm (x i), ← rpow_succ]
        have hm : 2 * k + 1 + 1 = 2 * (k + 1) := by omega
        rw [hm]
      have h2 : rpow (absR (x i)) (2 * k + 2) = rpow (x i) (2 * (k + 1)) := by
        have hm : 2 * k + 2 = 2 * (k + 1) := by omega
        rw [hm, rpow_mul_exp, rpow_mul_exp, rpow_two, rpow_two, absR_sq]
      rw [h1, h2]
    | inr ho =>
      rcases ho with ⟨k, rfl⟩
      refine ⟨fun i => absR (x i), fun i => absR_sq (x i), fun i => ?_⟩
      have h1 : rpow (x i) (2 * k + 1 + 1) = rpow (absR (x i)) (2 * k + 2) := by
        have hm1 : 2 * k + 1 + 1 = 2 * (k + 1) := by omega
        rw [hm1, rpow_mul_exp, rpow_mul_exp, rpow_two, rpow_two, absR_sq]
      rw [h1, CommRing.mul_comm (absR (x i)), ← rpow_succ]
  rcases hex_y with ⟨y, hy_sq, hy_pow⟩
  let g : Idx n (d + 2) → R := headTailProd y x
  -- Identity: `∑_α A(α) * g(α) = lam * ∑_i |x_i|^{d+2}`
  let Sm := sumFin (fun i : Fin n => rpow (absR (x i)) (d + 2))
  have hinner : sumList (idxList n (d + 2)) (fun α => A α * g α) = lam * Sm := by
    change sumIdx (fun α : Idx n (d + 2) => A α * g α) = lam * Sm
    rw [sumIdx_succ_ord]
    have hc : sumFin (fun i => sumIdx (fun t : Idx n (d + 1) => A (Idx.cons i t) * g (Idx.cons i t))) =
        sumFin (fun i => y i * contract A x i) := by
      apply sumFin_congr; intro i
      unfold contract sumIdx
      rw [← sumList_mul_left]
      apply sumList_congr; intro t _
      dsimp only [g]
      rw [headTailProd_cons, mul_left_comm_eq (y i) (A (Idx.cons i t))]
    rw [hc]
    have hc2 : sumFin (fun i => y i * contract A x i) =
        lam * sumFin (fun i => rpow (absR (x i)) (d + 2)) := by
      rw [← sumFin_mul_left]
      apply sumFin_congr; intro i
      rw [heig.2 i, mul_left_comm_eq (y i) lam, hy_pow i]
    exact hc2
  -- Compute `∑_α g(α)^2 = (∑_i |x_i|^2)^{d+2}`
  let S2 := sumList (finList n) (fun i => rpow (absR (x i)) 2)
  have hg2 : sumList (idxList n (d + 2)) (fun α => g α * g α) = rpow S2 (d + 2) := by
    change sumIdx (fun α : Idx n (d + 2) => g α * g α) = rpow S2 (d + 2)
    rw [sumIdx_succ_ord]
    have hS2_eq : S2 = sumFin (fun i => x i * x i) := by
      apply sumList_congr; intro i _
      rw [rpow_two, absR_sq]
    have hc : sumFin (fun i => sumIdx (fun t : Idx n (d + 1) => g (Idx.cons i t) * g (Idx.cons i t))) =
        sumFin (fun i => (x i * x i) * rpow S2 (d + 1)) := by
      apply sumFin_congr; intro i
      dsimp only [g]
      simp only [headTailProd_cons]
      have htail : sumIdx (fun t : Idx n (d + 1) =>
          (y i * idxProd x t) * (y i * idxProd x t)) =
          (y i * y i) * sumIdx (fun t : Idx n (d + 1) => idxProd (fun j => x j * x j) t) := by
        unfold sumIdx
        rw [← sumList_mul_left]
        apply sumList_congr; intro t _
        rw [idxProd_mul_vec, CommRing.mul_assoc (y i), mul_left_comm_eq (idxProd x t) (y i),
            ← CommRing.mul_assoc (y i) (y i)]
      rw [htail, hy_sq i, sumIdx_idxProd, ← hS2_eq]
    rw [hc, sumFin_mul_right, ← hS2_eq, CommRing.mul_comm, ← rpow_succ]
  -- Cauchy-Schwarz + `powSum_two_m_le`
  have hcs := cauchy_schwarz_list (idxList n (d + 2)) A g
  rw [hinner, hg2] at hcs
  change leR ((lam * Sm) * (lam * Sm)) (frobNormSq A * rpow S2 (d + 2)) at hcs
  have hmuir := powSum_two_m_le (l := finList n) (r := fun i => absR (x i))
    (fun i _ => absR_nonneg (x i)) d
  rw [length_finList] at hmuir
  change leR (rpow S2 (d + 2)) (rpow (natCastR n) d * (Sm * Sm)) at hmuir
  have hF_nn : leR 0 (frobNormSq A) :=
    sumList_nonneg (fun α _ => sq_nonneg (A α))
  have hcomb := leR_trans hcs (mul_leR_mul_of_nonneg_left hF_nn hmuir)
  -- Cancel `Sm * Sm > 0`
  have ⟨j₀, hj₀⟩ := heig.1
  have hxj0_pos : ltR 0 (absR (x j₀)) := by
    refine ⟨absR_nonneg (x j₀), ?_⟩
    intro h0
    exact hj₀ ((absR_eq_zero_iff (x j₀)).mp h0.symm)
  have hSm_pos : ltR 0 Sm := by
    -- `Sm ≥ |x_{j₀}|^{d+2} > 0`
    have hpow_pos : ltR 0 (rpow (absR (x j₀)) (d + 2)) := rpow_pos hxj0_pos (d + 2)
    -- Show single term `≤ sumList` when all terms `≥ 0`
    have hmem_le : leR (rpow (absR (x j₀)) (d + 2)) Sm := by
      suffices ∀ (l : List (Fin n)), j₀ ∈ l →
          leR (rpow (absR (x j₀)) (d + 2)) (sumList l (fun i => rpow (absR (x i)) (d + 2))) from
        this (finList n) (mem_finList j₀)
      intro l hmem
      induction l with
      | nil => cases hmem
      | cons a l ihl =>
        simp only [sumList_cons]
        cases List.mem_cons.mp hmem with
        | inl hja =>
          subst hja
          have hrest : leR 0 (sumList l (fun i => rpow (absR (x i)) (d + 2))) :=
            sumList_nonneg (fun i _ => rpow_nonneg (absR_nonneg (x i)) (d + 2))
          have h := add_leR_add (leR_refl (rpow (absR (x j₀)) (d + 2))) hrest
          rw [add_zero_eq] at h
          exact h
        | inr hjl =>
          have ha_nn : leR 0 (rpow (absR (x a)) (d + 2)) :=
            rpow_nonneg (absR_nonneg (x a)) (d + 2)
          have h := add_leR_add ha_nn (ihl hjl)
          rw [zero_add_eq] at h
          exact h
    exact ltR_of_ltR_of_leR hpow_pos hmem_le
  have hSm2_pos : ltR 0 (Sm * Sm) := mul_pos_ltR hSm_pos hSm_pos
  have hrew_l : (lam * Sm) * (lam * Sm) = (lam * lam) * (Sm * Sm) := by
    rw [CommRing.mul_assoc lam Sm, mul_left_comm_eq Sm lam Sm, ← CommRing.mul_assoc]
  have hrew_r : frobNormSq A * (rpow (natCastR n) d * (Sm * Sm)) =
      (rpow (natCastR n) d * frobNormSq A) * (Sm * Sm) := by
    rw [← CommRing.mul_assoc, CommRing.mul_comm (frobNormSq A)]
  rw [hrew_l, hrew_r] at hcomb
  exact leR_of_mul_leR_mul_pos_right hSm2_pos hcomb

/-- Sharp attainment of the Frobenius `H`-bound `λ^2 = n^d * ‖A‖_F^2` by `J_{m, n}` (`m = d + 2`). -/
theorem allOnes_attains_frob_H_bound (n d : Nat) (hn : n ≥ 1) :
    let A : Idx n (d + 2) → R := allOnesTensor n (d + 2)
    let lam : R := rpow (natCastR n) (d + 1)
    IsHEigenpair A (fun _ => 1) lam ∧
    lam * lam = rpow (natCastR n) d * frobNormSq A := by
  dsimp only
  refine ⟨(allOnes_attains_H_bound n (d + 1) hn).2.2, ?_⟩
  unfold frobNormSq allOnesTensor
  rw [mul_one_eq, sumIdx_const, mul_one_eq, ← rpow_add, ← rpow_add]
  congr 1
  omega

/-! ### 6. Nonnegative Row-Sum Gershgorin Bound & Exact Spectrum of `B_{m, 2}` -/

/-- Qi's row-sum Gershgorin bound for nonnegative real tensors: if `A(α) ≥ 0` and every row sum
    `(A 1^d)_i ≤ S_max` (`S_max ≥ 0`), then every real `H`-eigenpair `(x, λ)` satisfies `|λ| ≤ S_max`. -/
theorem gershgorin_nonneg_row_bound_real {n d : Nat} (hn : n ≥ 1)
    {A : Idx n (d + 1) → R} (hnn : ∀ α, leR 0 (A α))
    {Smax : R} (hS : ∀ i : Fin n, leR (contract A (fun _ => 1) i) Smax)
    {x : Fin n → R} {lam : R} (heig : IsHEigenpair A x lam) :
    leR (absR lam) Smax := by
  have ⟨j₀, hj₀⟩ := heig.1
  have ⟨i₀, hmax⟩ := exists_max_fin hn (fun j => absR (x j))
  let M := absR (x i₀)
  have hxj0_pos : ltR 0 (absR (x j₀)) :=
    ⟨absR_nonneg _, fun h0 => hj₀ ((absR_eq_zero_iff _).mp h0.symm)⟩
  have hM_pos : ltR 0 M := ltR_of_ltR_of_leR hxj0_pos (hmax j₀)
  have hMd_pos : ltR 0 (rpow M d) := rpow_pos hM_pos d
  have hrow := congrArg absR (heig.2 i₀)
  rw [absR_mul, absR_rpow] at hrow
  have htri := sumList_absR_leR (idxList n d) (fun t => A (Idx.cons i₀ t) * idxProd x t)
  have hterm : ∀ t : Idx n d, t ∈ idxList n d →
      leR (absR (A (Idx.cons i₀ t) * idxProd x t))
          ((A (Idx.cons i₀ t) * idxProd (fun _ => (1 : R)) t) * rpow M d) := by
    intro t _
    rw [absR_mul, absR_of_nonneg (hnn _), absR_idxProd, idxProd_ones, mul_one_eq]
    exact mul_leR_mul_of_nonneg_left (hnn _)
      (idxProd_leR_rpow_of_leR (fun j => absR_nonneg (x j)) hmax t)
  have hsum := sumList_leR hterm
  rw [sumList_mul_right] at hsum
  have hchain : leR (absR lam * rpow M d) (Smax * rpow M d) := by
    rw [← hrow]
    exact leR_trans htri (leR_trans hsum (mul_leR_mul_of_nonneg_right hMd_pos.1 (hS i₀)))
  exact leR_of_mul_leR_mul_pos_right hMd_pos hchain

/-- Exact real `H`-spectral radius of the binary binomial-entry tensor `B_{m, 2}` (`m = d + 1`):
    (1) `B_{m, 2}` is symmetric,
    (2) `x = (1, 1)` is an `H`-eigenvector with eigenvalue `C(2m - 1, m - 1)`, and
    (3) every real `H`-eigenpair `(x, λ)` satisfies `|λ| ≤ C(2m - 1, m - 1)`. -/
theorem binomialEntry_exact_H_radius (d : Nat) :
    let B := (binomialEntryTensor (d + 1) : Idx 2 (d + 1) → R)
    let rad : R := natCastR (binom (2 * d + 1) d)
    IsSymmetric B ∧
    IsHEigenpair B (fun _ => 1) rad ∧
    (∀ (x : Fin 2 → R) (lam : R), IsHEigenpair B x lam → leR (absR lam) rad) := by
  refine ⟨isSymmetric_binomialEntryTensor (d + 1), ?_, ?_⟩
  · refine ⟨⟨⟨0, by omega⟩, IntegralDomain.zero_ne_one.symm⟩, ?_⟩
    intro i
    change contract (binomialEntryTensor (S := R) (d + 1)) (fun _ => 1) i = _
    rw [contract_binomialEntryTensor_ones, rpow_one_base, mul_one_eq]
  · intro x lam heig
    apply gershgorin_nonneg_row_bound_real (by omega)
      (fun _ => natCastR_nonneg _)
      (fun i => by
        change leR (contract (binomialEntryTensor (S := R) (d + 1)) (fun _ => 1) i) _
        rw [contract_binomialEntryTensor_ones]; exact leR_refl _)
      heig

end PositiveTheorems

end Conjecture00000007176
