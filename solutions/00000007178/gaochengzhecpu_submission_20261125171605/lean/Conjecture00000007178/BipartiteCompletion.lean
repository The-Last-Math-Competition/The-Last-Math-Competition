/-
  Conjecture 00000007178 — Pillar 1: Bipartite / Rectangular Partial Matrix Completion
  1. Universal alternating cycle-product identity along arbitrary `2k`-cycles.
  2. Positive non-vacuity theorem: every everywhere-nonzero partial matrix on an
     acyclic bipartite forest pattern admits an exact rank-`1` completion over any field.
  3. Sharp refutation on the incomplete chordless even `6`-cycle `E_{C_6}`:
     - `B(E_{C_6}) ≅ C_6` has ONLY an even cycle (zero odd cycles);
     - EVERY fully specified submatrix of `E_{C_6}` has rank at most `1`;
     - Yet `mr_F(P_C6_plus) = 1` whereas `mr_F(P_C6_alpha α) = 2` for every field `F`
       with `α ∈ F \ {0, 1}` (in particular `α = -1` whenever `char(F) ≠ 2`, and
       `α = ω` in `𝔽₄` of `char = 2`), refuting both purely combinatorial pattern
       characterization and cycle-parity obstruction.
-/

import Conjecture00000007178.MatrixRank

namespace Conjecture00000007178

universe u

open CommRingR FieldR

/-- Product over `Fin r` in a commutative ring `R`. -/
def finProd {R : Type u} [CommRingR R] : {r : Nat} → (Fin r → R) → R
  | 0, _ => 1
  | r + 1, f => f ⟨0, Nat.zero_lt_succ r⟩ * finProd (fun t : Fin r => f ⟨t.val + 1, Nat.succ_lt_succ t.isLt⟩)

theorem finProd_congr {R : Type u} [CommRingR R] {r : Nat} {f g : Fin r → R}
    (h : ∀ t, f t = g t) : finProd f = finProd g := by
  have hfg : f = g := funext h
  rw [hfg]

theorem finProd_snoc {R : Type u} [CommRingR R] :
    ∀ {r : Nat} (g : Fin (r + 1) → R),
      finProd g =
      finProd (fun s : Fin r => g ⟨s.val, Nat.lt_succ_of_lt s.isLt⟩) * g ⟨r, Nat.lt_succ_self r⟩
  | 0, g => by
    show g ⟨0, Nat.zero_lt_succ 0⟩ * 1 = 1 * g ⟨0, Nat.zero_lt_succ 0⟩
    rw [mul_one, one_mul]
  | r + 1, g => by
    unfold finProd
    have ih := finProd_snoc (fun t : Fin (r + 1) => g ⟨t.val + 1, Nat.succ_lt_succ t.isLt⟩)
    rw [ih, ← mul_assoc]

/-- Cyclic shift `t ↦ (t + 1) mod (k + 1)` on `Fin (k + 1)`. -/
def nextIdx {k : Nat} (t : Fin (k + 1)) : Fin (k + 1) :=
  if h : t.val + 1 < k + 1 then ⟨t.val + 1, h⟩ else ⟨0, Nat.zero_lt_succ k⟩

theorem finProd_cycleShift {R : Type u} [CommRingR R] {k : Nat} (f : Fin (k + 1) → R) :
    finProd (fun t => f (nextIdx t)) = finProd f := by
  rw [finProd_snoc (fun t : Fin (k + 1) => f (nextIdx t))]
  have hinit :
      finProd (fun s : Fin k => f (nextIdx ⟨s.val, Nat.lt_succ_of_lt s.isLt⟩)) =
      finProd (fun s : Fin k => f ⟨s.val + 1, Nat.succ_lt_succ s.isLt⟩) := by
    apply finProd_congr
    intro s
    have hlt : s.val + 1 < k + 1 := Nat.succ_lt_succ s.isLt
    simp [nextIdx, hlt]
  have hlast : f (nextIdx ⟨k, Nat.lt_succ_self k⟩) = f ⟨0, Nat.zero_lt_succ k⟩ := by
    have hnot : ¬ (k + 1 < k + 1) := Nat.lt_irrefl (k + 1)
    simp [nextIdx, hnot]
  rw [hinit, hlast, mul_comm]
  rfl

theorem finProd_mul {R : Type u} [CommRingR R] :
    ∀ {r : Nat} (f g : Fin r → R),
      finProd (fun t => f t * g t) = finProd f * finProd g
  | 0, _, _ => (mul_one 1).symm
  | r + 1, f, g => by
    unfold finProd
    rw [finProd_mul (fun t : Fin r => f ⟨t.val + 1, Nat.succ_lt_succ t.isLt⟩)
                    (fun t : Fin r => g ⟨t.val + 1, Nat.succ_lt_succ t.isLt⟩)]
    let a := f ⟨0, Nat.zero_lt_succ r⟩
    let b := g ⟨0, Nat.zero_lt_succ r⟩
    let P := finProd (fun t : Fin r => f ⟨t.val + 1, Nat.succ_lt_succ t.isLt⟩)
    let Q := finProd (fun t : Fin r => g ⟨t.val + 1, Nat.succ_lt_succ t.isLt⟩)
    show (a * b) * (P * Q) = (a * P) * (b * Q)
    calc
      (a * b) * (P * Q) = a * (b * (P * Q)) := by rw [mul_assoc]
      _ = a * ((b * P) * Q) := by rw [← mul_assoc b P Q]
      _ = a * ((P * b) * Q) := by rw [mul_comm b P]
      _ = a * (P * (b * Q)) := by rw [mul_assoc P b Q]
      _ = (a * P) * (b * Q) := by rw [← mul_assoc]

/-- Universal bipartite even-cycle cocycle identity: if `HasRankAtMost R 1 M`, then along
any `2(k + 1)`-cycle `(rows 0, cols 0, rows 1, cols 1, ...)` in the bipartite graph `[m] ⊔ [n]`,
the alternating forward and backward edge products are equal. -/
theorem bipartite_even_cycle_product_eq {R : Type u} [CommRingR R] {m n k : Nat}
    {M : Mat R m n} (hrk : HasRankAtMost R 1 M)
    (rows : Fin (k + 1) → Fin m) (cols : Fin (k + 1) → Fin n) :
    finProd (fun t => M (rows t) (cols t)) =
    finProd (fun t => M (rows (nextIdx t)) (cols t)) := by
  rcases (hasRankAtMost_one_iff_outer M).mp hrk with ⟨u, v, huv⟩
  have hL : finProd (fun t => M (rows t) (cols t)) =
      finProd (fun t => u (rows t)) * finProd (fun t => v (cols t)) := by
    rw [finProd_congr (fun t => huv (rows t) (cols t)), finProd_mul]
  have hR : finProd (fun t => M (rows (nextIdx t)) (cols t)) =
      finProd (fun t => u (rows (nextIdx t))) * finProd (fun t => v (cols t)) := by
    rw [finProd_congr (fun t => huv (rows (nextIdx t)) (cols t)), finProd_mul]
  rw [hL, hR, finProd_cycleShift (fun t => u (rows t))]

/-- Universal directed cycle vs. diagonal product identity: if `HasRankAtMost R 1 M`
for a square `n × n` matrix `M`, then along ANY cycle `verts : Fin (k + 1) → Fin n`
(whether odd or even length!), the cycle edge product equals the diagonal product. -/
theorem directed_cycle_diag_product_eq {R : Type u} [CommRingR R] {n k : Nat}
    {M : Mat R n n} (hrk : HasRankAtMost R 1 M)
    (verts : Fin (k + 1) → Fin n) :
    finProd (fun t => M (verts t) (verts (nextIdx t))) =
    finProd (fun t => M (verts t) (verts t)) := by
  rcases (hasRankAtMost_one_iff_outer M).mp hrk with ⟨u, v, huv⟩
  have hL : finProd (fun t => M (verts t) (verts (nextIdx t))) =
      finProd (fun t => u (verts t)) * finProd (fun t => v (verts (nextIdx t))) := by
    rw [finProd_congr (fun t => huv (verts t) (verts (nextIdx t))), finProd_mul]
  have hR : finProd (fun t => M (verts t) (verts t)) =
      finProd (fun t => u (verts t)) * finProd (fun t => v (verts t)) := by
    rw [finProd_congr (fun t => huv (verts t) (verts t)), finProd_mul]
  rw [hL, hR, finProd_cycleShift (fun t => v (verts t))]

/-! ### Positive Non-Vacuity Theorem: Acyclic / Forest Patterns Always Have Rank-`1` Completions -/

/-- Inductive leaf-addition characterization of acyclic bipartite specification patterns
(forests in `K_{m, n}`). -/
inductive IsForestSpec {m n : Nat} : (Fin m → Fin n → Bool) → Prop where
  | empty : IsForestSpec (fun _ _ => false)
  | addRowLeaf (spec : Fin m → Fin n → Bool) (i₀ : Fin m) (j₀ : Fin n)
      (hfresh : ∀ j : Fin n, spec i₀ j = false)
      (hprev : IsForestSpec spec) :
      IsForestSpec (fun i j => if i = i₀ ∧ j = j₀ then true else spec i j)
  | addColLeaf (spec : Fin m → Fin n → Bool) (i₀ : Fin m) (j₀ : Fin n)
      (hfresh : ∀ i : Fin m, spec i j₀ = false)
      (hprev : IsForestSpec spec) :
      IsForestSpec (fun i j => if i = i₀ ∧ j = j₀ then true else spec i j)

/-- Nowhere-zero multiplicative potentials exist for every everywhere-nonzero partial matrix
on an acyclic bipartite forest pattern over any field `F`. -/
theorem forest_potentials_exist {F : Type u} [FieldR F] {m n : Nat}
    {spec : Fin m → Fin n → Bool} (hf : IsForestSpec spec)
    (val : Fin m → Fin n → F)
    (hnz : ∀ i j, spec i j = true → val i j ≠ 0) :
    ∃ (u : Fin m → F) (v : Fin n → F),
      (∀ i, u i ≠ 0) ∧ (∀ j, v j ≠ 0) ∧
      (∀ i j, spec i j = true → u i * v j = val i j) := by
  induction hf with
  | empty =>
    refine ⟨fun _ => 1, fun _ => 1, fun _ => one_ne_zero, fun _ => one_ne_zero, ?_⟩
    intro _ _ h
    contradiction
  | addRowLeaf spec' i₀ j₀ hfresh _ ih =>
    have hnz' : ∀ i j, spec' i j = true → val i j ≠ 0 := by
      intro i j hs
      apply hnz i j
      by_cases hij : i = i₀ ∧ j = j₀
      · simp [hij]
      · simp [hij, hs]
    rcases ih hnz' with ⟨u, v, hu, hv, huv⟩
    let u' : Fin m → F := fun i => if i = i₀ then val i₀ j₀ * (v j₀)⁻¹ else u i
    refine ⟨u', v, ?_, hv, ?_⟩
    · intro i
      by_cases hi : i = i₀
      · simp only [u', hi, ↓reduceIte]
        have hv0 : val i₀ j₀ ≠ 0 := hnz i₀ j₀ (by simp)
        exact mul_ne_zero hv0 (inv_ne_zero (hv j₀))
      · simp only [u', hi, ↓reduceIte]
        exact hu i
    · intro i j hs
      by_cases hij : i = i₀ ∧ j = j₀
      · rcases hij with ⟨rfl, rfl⟩
        simp only [u', ↓reduceIte]
        rw [mul_assoc, inv_mul_cancel (hv j), mul_one]
      · simp only [hij, ↓reduceIte] at hs
        have hi : i ≠ i₀ := by
          intro hEq
          rw [hEq] at hs
          rw [hfresh j] at hs
          contradiction
        simp only [u', hi, ↓reduceIte]
        exact huv i j hs
  | addColLeaf spec' i₀ j₀ hfresh _ ih =>
    have hnz' : ∀ i j, spec' i j = true → val i j ≠ 0 := by
      intro i j hs
      apply hnz i j
      by_cases hij : i = i₀ ∧ j = j₀
      · simp [hij]
      · simp [hij, hs]
    rcases ih hnz' with ⟨u, v, hu, hv, huv⟩
    let v' : Fin n → F := fun j => if j = j₀ then (u i₀)⁻¹ * val i₀ j₀ else v j
    refine ⟨u, v', hu, ?_, ?_⟩
    · intro j
      by_cases hj : j = j₀
      · simp only [v', hj, ↓reduceIte]
        have hv0 : val i₀ j₀ ≠ 0 := hnz i₀ j₀ (by simp)
        exact mul_ne_zero (inv_ne_zero (hu i₀)) hv0
      · simp only [v', hj, ↓reduceIte]
        exact hv j
    · intro i j hs
      by_cases hij : i = i₀ ∧ j = j₀
      · rcases hij with ⟨rfl, rfl⟩
        simp only [v', ↓reduceIte]
        rw [← mul_assoc, FieldR.mul_inv_cancel (u i) (hu i), one_mul]
      · simp only [hij, ↓reduceIte] at hs
        have hj : j ≠ j₀ := by
          intro hEq
          rw [hEq] at hs
          rw [hfresh i] at hs
          contradiction
        simp only [v', hj, ↓reduceIte]
        exact huv i j hs

/-- Universal Forest Completion Theorem: every everywhere-nonzero partial matrix with at least
one specified entry on an acyclic bipartite forest pattern has exact minimum completion rank `1`. -/
theorem forest_partial_matrix_minRank_one {F : Type u} [FieldR F] {m n : Nat}
    (P : PartialMatrix F m n) (hf : IsForestSpec P.spec)
    (hnz : P.EverywhereNonzero)
    (hne : ∃ i₀ j₀, P.spec i₀ j₀ = true) :
    IsMinCompletionRank F P 1 := by
  constructor
  · rcases forest_potentials_exist hf P.val hnz with ⟨u, v, _, _, huv⟩
    refine ⟨fun i j => u i * v j, ?_, ?_⟩
    · intro i j hs
      exact huv i j hs
    · exact (hasRankAtMost_one_iff_outer _).mpr ⟨u, v, fun _ _ => rfl⟩
  · intro r' hr' M hcomp
    have hr0 : r' = 0 := by omega
    subst hr0
    rcases hne with ⟨i₀, j₀, hs₀⟩
    have hM0 : M i₀ j₀ ≠ 0 := by
      rw [hcomp i₀ j₀ hs₀]
      exact hnz i₀ j₀ hs₀
    exact not_hasRankAtMost_zero_of_entry_ne_zero i₀ j₀ hM0

/-- The `5`-edge spanning tree `T₅ = {(0,0),(0,1),(1,1),(1,2),(2,2)}` of `K_{3,3}`. -/
def spec_T5 (i j : Fin 3) : Bool :=
  (i == 0 && j == 0) || (i == 0 && j == 1) ||
  (i == 1 && j == 1) || (i == 1 && j == 2) ||
  (i == 2 && j == 2)

theorem spec_T5_isForest : IsForestSpec spec_T5 := by
  let s0 : Fin 3 → Fin 3 → Bool := fun _ _ => false
  let s1 : Fin 3 → Fin 3 → Bool := fun i j => if i = 0 ∧ j = 0 then true else s0 i j
  let s2 : Fin 3 → Fin 3 → Bool := fun i j => if i = 0 ∧ j = 1 then true else s1 i j
  let s3 : Fin 3 → Fin 3 → Bool := fun i j => if i = 1 ∧ j = 1 then true else s2 i j
  let s4 : Fin 3 → Fin 3 → Bool := fun i j => if i = 1 ∧ j = 2 then true else s3 i j
  let s5 : Fin 3 → Fin 3 → Bool := fun i j => if i = 2 ∧ j = 2 then true else s4 i j
  have h0 : IsForestSpec s0 := IsForestSpec.empty
  have h1 : IsForestSpec s1 := IsForestSpec.addRowLeaf s0 0 0 (by decide) h0
  have h2 : IsForestSpec s2 := IsForestSpec.addColLeaf s1 0 1 (by decide) h1
  have h3 : IsForestSpec s3 := IsForestSpec.addRowLeaf s2 1 1 (by decide) h2
  have h4 : IsForestSpec s4 := IsForestSpec.addColLeaf s3 1 2 (by decide) h3
  have h5 : IsForestSpec s5 := IsForestSpec.addRowLeaf s4 2 2 (by decide) h4
  have heq : s5 = spec_T5 := by
    funext i j
    revert i j
    decide
  rw [← heq]
  exact h5

/-! ### Sharp Refutation on the Incomplete Even `6`-Cycle `E_{C_6}` -/

/-- The `6`-entry incomplete `3 × 3` pattern `E_{C_6} = T₅ ∪ {(2, 0)}`, whose bipartite
specification graph `B(E_{C_6})` is an induced chordless `6`-cycle `C₆` (even length `6`,
zero odd cycles, and `K_{2,2}`-free). -/
def spec_C6 (i j : Fin 3) : Bool :=
  (i == 0 && j == 0) || (i == 0 && j == 1) ||
  (i == 1 && j == 1) || (i == 1 && j == 2) ||
  (i == 2 && j == 2) || (i == 2 && j == 0)

/-- `spec_C6` is `K_{2,2}`-free: any two distinct rows share at most one specified column. -/
theorem spec_C6_no_K22 :
    ∀ r₁ r₂ c₁ c₂ : Fin 3,
      r₁ ≠ r₂ →
      spec_C6 r₁ c₁ = true → spec_C6 r₂ c₁ = true →
      spec_C6 r₁ c₂ = true → spec_C6 r₂ c₂ = true →
      c₁ = c₂ := by
  decide

/-- Any matrix whose rows are all identical or whose columns are all identical has rank `≤ 1`. -/
theorem hasRankAtMost_one_of_const_rows_or_cols {R : Type u} [CommRingR R] {a b : Nat}
    (N : Mat R a b)
    (h : (∀ x₁ x₂ : Fin a, ∀ y : Fin b, N x₁ y = N x₂ y) ∨
         (∀ y₁ y₂ : Fin b, ∀ x : Fin a, N x y₁ = N x y₂)) :
    HasRankAtMost R 1 N := by
  rw [hasRankAtMost_one_iff_outer]
  cases h with
  | inl hrows =>
    cases a with
    | zero =>
      exact ⟨fun x => Fin.elim0 x, fun _ => 0, fun x => Fin.elim0 x⟩
    | succ a' =>
      refine ⟨fun _ => 1, fun y => N ⟨0, Nat.zero_lt_succ a'⟩ y, ?_⟩
      intro x y
      rw [one_mul]
      exact hrows x ⟨0, Nat.zero_lt_succ a'⟩ y
  | inr hcols =>
    cases b with
    | zero =>
      exact ⟨fun _ => 0, fun y => Fin.elim0 y, fun _ y => Fin.elim0 y⟩
    | succ b' =>
      refine ⟨fun x => N x ⟨0, Nat.zero_lt_succ b'⟩, fun _ => 1, ?_⟩
      intro x y
      rw [mul_one]
      exact hcols y ⟨0, Nat.zero_lt_succ b'⟩ x

/-- Every partial matrix `P` supported on `spec_C6` automatically satisfies
`LocallyRankAtMost R 1 P` (every fully specified submatrix of any size has rank `≤ 1`). -/
theorem locallyRankAtMost_one_of_spec_C6 {R : Type u} [CommRingR R]
    (P : PartialMatrix R 3 3) (hspec : P.spec = spec_C6) :
    PartialMatrix.LocallyRankAtMost R 1 P := by
  intro a b rows cols hfull
  apply hasRankAtMost_one_of_const_rows_or_cols
  by_cases hrows : ∀ x₁ x₂ : Fin a, rows x₁ = rows x₂
  · left
    intro x₁ x₂ y
    unfold PartialMatrix.submatrix
    rw [hrows x₁ x₂]
  · right
    intro y₁ y₂ x
    unfold PartialMatrix.submatrix
    -- Extract `x₁, x₂` with `rows x₁ ≠ rows x₂` via classical logic on `Prop`
    have hex : ∃ x₁ x₂ : Fin a, rows x₁ ≠ rows x₂ := by
      by_cases h1 : ∃ x₁ x₂ : Fin a, rows x₁ ≠ rows x₂
      · exact h1
      · exfalso
        apply hrows
        intro x₁ x₂
        by_cases heq : rows x₁ = rows x₂
        · exact heq
        · exact absurd ⟨x₁, x₂, heq⟩ h1
    rcases hex with ⟨x₁, x₂, hne⟩
    have hs : ∀ x' y', spec_C6 (rows x') (cols y') = true := by
      intro x' y'
      rw [← hspec]
      exact hfull x' y'
    have hc : cols y₁ = cols y₂ :=
      spec_C6_no_K22 (rows x₁) (rows x₂) (cols y₁) (cols y₂) hne
        (hs x₁ y₁) (hs x₂ y₁) (hs x₁ y₂) (hs x₂ y₂)
    rw [hc]

/-- All-ones partial matrix `A⁺` on the chordless even `6`-cycle `spec_C6`. -/
def P_C6_plus (F : Type u) [FieldR F] : PartialMatrix F 3 3 where
  spec := spec_C6
  val  := fun _ _ => 1

/-- Twisted partial matrix `A^α` on the exact same chordless even `6`-cycle `spec_C6`,
with entry `(2, 2)` equal to `α` and all other `5` cycle entries equal to `1`. -/
def P_C6_alpha {F : Type u} [FieldR F] (α : F) : PartialMatrix F 3 3 where
  spec := spec_C6
  val  := fun i j => if i == 2 && j == 2 then α else 1

theorem P_C6_plus_minRank_one (F : Type u) [FieldR F] :
    IsMinCompletionRank F (P_C6_plus F) 1 := by
  constructor
  · refine ⟨fun _ _ => 1, ?_, ?_⟩
    · intro _ _ _
      rfl
    · exact (hasRankAtMost_one_iff_outer _).mpr ⟨fun _ => 1, fun _ => 1, fun _ _ => (mul_one 1).symm⟩
  · intro r' hr' M hcomp
    have hr0 : r' = 0 := by omega
    subst hr0
    have h00 : M 0 0 = 1 := hcomp 0 0 rfl
    have hne : M 0 0 ≠ 0 := by rw [h00]; exact one_ne_zero
    exact not_hasRankAtMost_zero_of_entry_ne_zero 0 0 hne

theorem P_C6_alpha_not_rank_one {F : Type u} [FieldR F] {α : F} (hα1 : α ≠ 1)
    (M : Mat F 3 3) (hcomp : (P_C6_alpha α).IsCompletion M) :
    ¬ HasRankAtMost F 1 M := by
  intro hrk
  let id3 : Fin 3 → Fin 3 := fun t => t
  let rowsC : Fin 3 → Fin 3 := fun t =>
    match t.val with
    | 0 => 2
    | 1 => 0
    | _ => 1
  have hcyc' := bipartite_even_cycle_product_eq (k := 2) hrk rowsC id3
  have hL' : finProd (fun t : Fin 3 => M (rowsC t) t) = M 2 0 * (M 0 1 * (M 1 2 * 1)) := rfl
  have hR' : finProd (fun t : Fin 3 => M (rowsC (nextIdx t)) t) = M 0 0 * (M 1 1 * (M 2 2 * 1)) := rfl
  rw [hL', hR'] at hcyc'
  have m00 : M 0 0 = 1 := hcomp 0 0 rfl
  have m11 : M 1 1 = 1 := hcomp 1 1 rfl
  have m22 : M 2 2 = α := hcomp 2 2 rfl
  have m01 : M 0 1 = 1 := hcomp 0 1 rfl
  have m12 : M 1 2 = 1 := hcomp 1 2 rfl
  have m20 : M 2 0 = 1 := hcomp 2 0 rfl
  rw [m00, m11, m22, m01, m12, m20] at hcyc'
  rw [mul_one, mul_one, mul_one, mul_one, one_mul, one_mul] at hcyc'
  exact hα1 hcyc'.symm

theorem P_C6_alpha_minRank_two {F : Type u} [FieldR F] {α : F}
    (_hα0 : α ≠ 0) (hα1 : α ≠ 1) :
    IsMinCompletionRank F (P_C6_alpha α) 2 := by
  constructor
  · -- Explicit rank-2 completion: Row 0 = (1, 1, α), Row 1 = (1, 1, 1), Row 2 = (1, 1, α)
    let U : Mat F 3 2 := fun i t =>
      match i.val, t.val with
      | 1, 1 => 1
      | 0, 0 => 1
      | 2, 0 => 1
      | _, _ => 0
    let V : Mat F 2 3 := fun t j =>
      match t.val, j.val with
      | 0, 2 => α
      | _, _ => 1
    let M : Mat F 3 3 := fun i j => finSum (fun t : Fin 2 => U i t * V t j)
    refine ⟨M, ?_, ⟨U, V, fun _ _ => rfl⟩⟩
    refine fin3_cases ?_ ?_ ?_ <;> refine fin3_cases ?_ ?_ ?_ <;> intro hs <;> first
      | contradiction
      | (dsimp [M]; rw [finSum_two]; dsimp [U, V, P_C6_alpha];
         simp only [one_mul, mul_one, zero_mul, mul_zero, add_zero, zero_add])
  · intro r' hr' M hcomp
    have hcases : r' = 0 ∨ r' = 1 := by omega
    cases hcases with
    | inl h0 =>
      subst h0
      have h00 : M 0 0 = 1 := hcomp 0 0 rfl
      have hne : M 0 0 ≠ 0 := by rw [h00]; exact one_ne_zero
      exact not_hasRankAtMost_zero_of_entry_ne_zero 0 0 hne
    | inr h1 =>
      subst h1
      exact P_C6_alpha_not_rank_one hα1 M hcomp

/-- Master Theorem 1 (Bipartite Partial Matrix Refutation on Even `C₆`):
For EVERY field `F` and `α ∈ F \ {0, 1}`, `P_C6_plus F` and `P_C6_alpha α` have:
1. the exact same incomplete chordless even `6`-cycle pattern `spec_C6` (zero odd cycles),
2. everywhere-nonzero specified entries,
3. rank `≤ 1` on EVERY fully specified submatrix (`LocallyRankAtMost F 1`),
4. yet `mr_F(P_C6_plus) = 1 ≠ 2 = mr_F(P_C6_alpha α)`. -/
theorem even_C6_refutes_combinatorial_and_parity {F : Type u} [FieldR F]
    {α : F} (hα0 : α ≠ 0) (hα1 : α ≠ 1) :
    PartialMatrix.SamePattern (P_C6_plus F) (P_C6_alpha α) ∧
    (P_C6_plus F).EverywhereNonzero ∧
    (P_C6_alpha α).EverywhereNonzero ∧
    PartialMatrix.LocallyRankAtMost F 1 (P_C6_plus F) ∧
    PartialMatrix.LocallyRankAtMost F 1 (P_C6_alpha α) ∧
    IsMinCompletionRank F (P_C6_plus F) 1 ∧
    IsMinCompletionRank F (P_C6_alpha α) 2 := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, P_C6_plus_minRank_one F, P_C6_alpha_minRank_two hα0 hα1⟩
  · intro _ _ _
    exact one_ne_zero
  · intro i j _
    unfold P_C6_alpha
    dsimp only
    cases h22 : (i == 2 && j == 2)
    · exact one_ne_zero
    · exact hα0
  · exact locallyRankAtMost_one_of_spec_C6 (P_C6_plus F) rfl
  · exact locallyRankAtMost_one_of_spec_C6 (P_C6_alpha α) rfl

end Conjecture00000007178
