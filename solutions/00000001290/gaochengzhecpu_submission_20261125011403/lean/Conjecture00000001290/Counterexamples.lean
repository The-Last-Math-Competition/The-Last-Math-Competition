/-
  Conjecture 00000001290 — Counterexamples Separating Rationality, Shortness, and Locality
  Core Lean 4.19.0 (zero external dependencies)
-/
import Conjecture00000001290.PositiveSubtraction

namespace Conjecture00000001290

/-! ### Counterexample 1: Single-Pile Nim (`nimGame`)
    Short, non-local under every locality definition, unbounded Grundy sequence `g(n) = n`,
    with rational value OGF `x / (1 - x)^2` and polynomial fiber GFs `x^v`. -/

def nimGame : ImpartialGame where
  move n m := m < n

theorem nimGame_isShort : nimGame.IsShort := by
  refine ⟨?_, noInfinitePlay_of_lt (fun _ _ h => h)⟩
  intro n
  exact ⟨rangeList n, fun m => mem_rangeList.symm⟩

theorem nimGame_grundy : nimGame.IsGrundySeq (fun n => n) :=
  ⟨fun _ _ hm => Nat.ne_of_lt hm, fun _ v hv => ⟨v, hv, rfl⟩⟩

theorem nimGame_rational_ogf : HasRationalGrundyOGF nimGame := by
  refine ⟨fun n => n, nimGame_grundy, [0, 1], [1, -2, 1], ⟨0, by simp [coeff]⟩, ?_⟩
  intro n
  cases n with
  | zero => rfl
  | succ n₁ =>
    cases n₁ with
    | zero => rfl
    | succ k =>
      have htrim := seriesMulPolyCoeff_eq_sumRange_len [1, -2, 1]
        (grundyIntSeq (fun n => n)) (n := k + 2) (by simp)
      rw [htrim]
      simp [sumRange, coeff, grundyIntSeq]
      omega

theorem nimGame_rational_fibers : HasAllRationalGrundyFibers nimGame := by
  refine ⟨fun n => n, nimGame_grundy, fun v => ?_⟩
  refine ⟨List.replicate v 0 ++ [1], [1], ⟨0, by simp [coeff]⟩, ?_⟩
  intro n
  have htrim := seriesMulPolyCoeff_eq_sumRange_len [1]
    (grundyFiberSeq (fun k => k) v) (n := n) (by simp)
  rw [htrim, coeff_replicate_zero_append 1 v n]
  simp [sumRange, coeff, grundyFiberSeq]

theorem nimGame_not_boundedStepLocal : ¬ nimGame.IsBoundedStepLocal := by
  rintro ⟨K, hK⟩
  have hm : nimGame.move (K + 1) 0 := Nat.zero_lt_succ K
  have hdist := hK (K + 1) 0 hm
  unfold ImpartialGame.natDist at hdist
  have hle : ¬ (K + 1 ≤ 0) := by omega
  simp [hle] at hdist
  omega

theorem nimGame_not_boundedOutDegree : ¬ nimGame.IsBoundedOutDegree := by
  rintro ⟨B, hB⟩
  have hle : B + 1 ≤ B := grundy_le_outdegree hB nimGame_grundy (B + 1)
  omega

/-- Even stronger: Nim is not Grundy-equivalent to ANY bounded-outdegree game. -/
theorem nimGame_not_grundyEquiv_boundedOutDegree :
    ¬ ∃ H : ImpartialGame, H.IsBoundedOutDegree ∧ H.IsGrundySeq (fun n => n) := by
  rintro ⟨_, ⟨B, hB⟩, hg⟩
  have hle : B + 1 ≤ B := grundy_le_outdegree hB hg (B + 1)
  omega

theorem nimGame_not_finiteSubtraction : ¬ nimGame.IsFiniteSubtractionGame :=
  fun hfin => nimGame_not_boundedStepLocal (finiteSubtraction_boundedStepLocal hfin)

/-! ### Counterexample 2: Odd-Subtraction Game (`oddSubGame`)
    Short, translation-invariant subtraction game with bounded, 2-periodic Grundy values
    `g(n) = n % 2` (rational OGF `x / (1 - x^2)` and rational fibers), yet non-local. -/

def oddSubGame : ImpartialGame where
  move n m := ∃ s : Nat, s % 2 = 1 ∧ s ≤ n ∧ m = n - s

theorem oddSubGame_isShort : oddSubGame.IsShort := by
  refine ⟨?_, ?_⟩
  · apply finitelyBranching_of_boolBound (fun n => n) (fun n m => (n - m) % 2 == 1)
    intro n m
    simp only [oddSubGame, beq_iff_eq]
    constructor
    · rintro ⟨s, hs, hsn, rfl⟩
      have hs0 : 0 < s := by omega
      have hsub : n - (n - s) = s := by omega
      exact ⟨by omega, by rw [hsub]; exact hs⟩
    · rintro ⟨hmn, hodd⟩
      exact ⟨n - m, hodd, by omega, by omega⟩
  · apply noInfinitePlay_of_lt
    rintro n m ⟨s, hs, hsn, rfl⟩
    omega

theorem oddSubGame_grundy : oddSubGame.IsGrundySeq (fun n => n % 2) := by
  refine ⟨?_, ?_⟩
  · rintro n m ⟨s, hs, hsn, rfl⟩
    dsimp
    omega
  · intro n v hv
    dsimp at hv
    have hn1 : n % 2 = 1 := by omega
    have hv0 : v = 0 := by omega
    subst hv0
    exact ⟨0, ⟨n, hn1, Nat.le_refl n, by omega⟩, rfl⟩

theorem oddSubGame_rational_ogf : HasRationalGrundyOGF oddSubGame := by
  refine ⟨fun n => n % 2, oddSubGame_grundy, eventuallyPeriodic_rational_ogf ?_⟩
  exact ⟨0, 2, by omega, fun n _ => by dsimp; omega⟩

theorem oddSubGame_rational_fibers : HasAllRationalGrundyFibers oddSubGame := by
  refine ⟨fun n => n % 2, oddSubGame_grundy, eventuallyPeriodic_rational_fibers ?_⟩
  exact ⟨0, 2, by omega, fun n _ => by dsimp; omega⟩

theorem oddSubGame_not_boundedStepLocal : ¬ oddSubGame.IsBoundedStepLocal := by
  rintro ⟨K, hK⟩
  have hm : oddSubGame.move (2 * K + 1) 0 := ⟨2 * K + 1, by omega, by omega, by omega⟩
  have hdist := hK (2 * K + 1) 0 hm
  unfold ImpartialGame.natDist at hdist
  have hle : ¬ (2 * K + 1 ≤ 0) := by omega
  simp [hle] at hdist
  omega

theorem oddSubGame_not_boundedOutDegree : ¬ oddSubGame.IsBoundedOutDegree := by
  rintro ⟨B, hB⟩
  rcases hB (2 * B + 1) with ⟨L, hlen, hL⟩
  have hall : ∀ v : Nat, v ≤ B → v ∈ L.map (fun m => m / 2) := by
    intro v hv
    have hmv : oddSubGame.move (2 * B + 1) (2 * v) :=
      ⟨2 * (B - v) + 1, by omega, by omega, by omega⟩
    have hmem : 2 * v ∈ L := (hL (2 * v)).mp hmv
    have hdiv : (2 * v) / 2 = v := by omega
    rw [← hdiv]
    exact List.mem_map_of_mem hmem
  have hbad := length_gt_of_all_le_mem B (L.map (fun m => m / 2)) hall
  simp at hbad
  omega

theorem oddSubGame_not_finiteSubtraction : ¬ oddSubGame.IsFiniteSubtractionGame :=
  fun hfin => oddSubGame_not_boundedStepLocal (finiteSubtraction_boundedStepLocal hfin)

/-! ### Counterexample 3: Non-Short Games with Rational Sprague–Grundy GFs
    3A (`loopyStep1Game`): Step-1 local, out-degree `≤ 2`, loopy (non-short), with unique
        stopper-sided Sprague–Grundy sequence `(0, 1, 0, 1, 0, 0, ...)` and polynomial GF `x + x^3`.
    3B (`infBranchGame`): Well-founded (no infinite play), infinitely branching at `0` (non-short),
        with unique Sprague–Grundy sequence `(1, 0, 0, ...)` and polynomial GF `1`. -/

def loopyStep1Game : ImpartialGame where
  move n m :=
    (n = 1 ∧ (m = 0 ∨ m = 2)) ∨
    (n = 2 ∧ (m = 1 ∨ m = 3)) ∨
    (n = 3 ∧ m = 4)

def loopyStep1Seq (n : Nat) : Nat :=
  if n = 1 ∨ n = 3 then 1 else 0

theorem loopyStep1Game_boundedStepLocal : loopyStep1Game.IsBoundedStepLocal := by
  refine ⟨1, fun n m hm => ?_⟩
  unfold loopyStep1Game at hm
  unfold ImpartialGame.natDist
  rcases hm with ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩ <;> simp

theorem loopyStep1Game_boundedOutDegree : loopyStep1Game.IsBoundedOutDegree := by
  refine ⟨2, fun n => ?_⟩
  by_cases hn1 : n = 1
  · subst hn1
    refine ⟨[0, 2], by simp, fun m => ?_⟩
    simp [loopyStep1Game]
  · by_cases hn2 : n = 2
    · subst hn2
      refine ⟨[1, 3], by simp, fun m => ?_⟩
      simp [loopyStep1Game]
    · by_cases hn3 : n = 3
      · subst hn3
        refine ⟨[4], by simp, fun m => ?_⟩
        simp [loopyStep1Game]
      · refine ⟨[], by simp, fun m => ?_⟩
        simp [loopyStep1Game, hn1, hn2, hn3]

theorem loopyStep1Game_not_noInfinitePlay : ¬ loopyStep1Game.NoInfinitePlay := by
  intro hwf
  apply no_infinite_seq_of_noInfinitePlay hwf
  refine ⟨fun k => if k % 2 = 0 then 1 else 2, fun k => ?_⟩
  unfold loopyStep1Game
  by_cases hk : k % 2 = 0
  · have hk1 : (k + 1) % 2 ≠ 0 := by omega
    simp [hk, hk1]
  · have hk1 : (k + 1) % 2 = 0 := by omega
    simp [hk, hk1]

theorem loopyStep1Game_not_isShort : ¬ loopyStep1Game.IsShort :=
  fun hshort => loopyStep1Game_not_noInfinitePlay hshort.2

theorem loopyStep1Game_grundy : loopyStep1Game.IsGrundySeq loopyStep1Seq := by
  refine ⟨?_, ?_⟩
  · intro n m hm
    unfold loopyStep1Game at hm
    rcases hm with ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp [loopyStep1Seq]
  · intro n v hv
    unfold loopyStep1Seq at hv
    split at hv
    · rename_i hn13
      have hv0 : v = 0 := by omega
      subst hv0
      rcases hn13 with rfl | rfl
      · exact ⟨0, by simp [loopyStep1Game], by simp [loopyStep1Seq]⟩
      · exact ⟨4, by simp [loopyStep1Game], by simp [loopyStep1Seq]⟩
    · omega

theorem loopyStep1Game_grundy_unique {g : Nat → Nat}
    (hg : loopyStep1Game.IsGrundySeq g) : ∀ n : Nat, g n = loopyStep1Seq n := by
  have hg_term : ∀ x : Nat, x ≠ 1 → x ≠ 2 → x ≠ 3 → g x = 0 := by
    intro x hx1 hx2 hx3
    by_cases hgx : g x = 0
    · exact hgx
    · rcases hg.2 x 0 (by omega) with ⟨m, hm, _⟩
      unfold loopyStep1Game at hm
      omega
  have hg0 : g 0 = 0 := hg_term 0 (by omega) (by omega) (by omega)
  have hg4 : g 4 = 0 := hg_term 4 (by omega) (by omega) (by omega)
  have hg3 : g 3 = 1 := by
    have hne0 : g 3 ≠ 0 := by
      intro h30
      exact hg.1 3 4 (by simp [loopyStep1Game]) (hg4.trans h30.symm)
    by_cases hgt1 : 1 < g 3
    · rcases hg.2 3 1 hgt1 with ⟨m, hm, hgm⟩
      unfold loopyStep1Game at hm
      rcases hm with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, rfl⟩ <;> omega
    · omega
  have hg1_ne0 : g 1 ≠ 0 := by
    intro h10
    exact hg.1 1 0 (by simp [loopyStep1Game]) (hg0.trans h10.symm)
  have hg2 : g 2 = 0 := by
    by_cases h20 : g 2 = 0
    · exact h20
    · rcases hg.2 2 0 (by omega) with ⟨m, hm, hgm⟩
      unfold loopyStep1Game at hm
      rcases hm with ⟨h, _⟩ | ⟨_, rfl | rfl⟩ | ⟨h, _⟩ <;> omega
  have hg1 : g 1 = 1 := by
    by_cases hgt1 : 1 < g 1
    · rcases hg.2 1 1 hgt1 with ⟨m, hm, hgm⟩
      unfold loopyStep1Game at hm
      rcases hm with ⟨_, rfl | rfl⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> omega
    · omega
  intro n
  by_cases hn1 : n = 1
  · subst hn1; simp [loopyStep1Seq, hg1]
  · by_cases hn2 : n = 2
    · subst hn2; simp [loopyStep1Seq, hg2]
    · by_cases hn3 : n = 3
      · subst hn3; simp [loopyStep1Seq, hg3]
      · simp [loopyStep1Seq, hn1, hn3, hg_term n hn1 hn2 hn3]

theorem loopyStep1Game_rational_ogf : HasRationalGrundyOGF loopyStep1Game := by
  refine ⟨loopyStep1Seq, loopyStep1Game_grundy, eventuallyPeriodic_rational_ogf ?_⟩
  refine ⟨4, 1, Nat.zero_lt_one, fun n hn => ?_⟩
  have h1 : ¬ (n = 1 ∨ n = 3) := by omega
  have h2 : ¬ (n + 1 = 1 ∨ n + 1 = 3) := by omega
  simp only [loopyStep1Seq, h1, h2, ↓reduceIte]

theorem loopyStep1Game_rational_fibers : HasAllRationalGrundyFibers loopyStep1Game := by
  refine ⟨loopyStep1Seq, loopyStep1Game_grundy, eventuallyPeriodic_rational_fibers ?_⟩
  refine ⟨4, 1, Nat.zero_lt_one, fun n hn => ?_⟩
  have h1 : ¬ (n = 1 ∨ n = 3) := by omega
  have h2 : ¬ (n + 1 = 1 ∨ n + 1 = 3) := by omega
  simp only [loopyStep1Seq, h1, h2, ↓reduceIte]

/-- Infinitely-branching well-founded game: `0` moves to all `m > 0`, all `n > 0` terminal. -/
def infBranchGame : ImpartialGame where
  move n m := n = 0 ∧ 0 < m

def infBranchSeq (n : Nat) : Nat :=
  if n = 0 then 1 else 0

theorem infBranchGame_noInfinitePlay : infBranchGame.NoInfinitePlay := by
  refine ⟨fun n => ?_⟩
  by_cases hn : n = 0
  · subst hn
    refine Acc.intro 0 (fun m ⟨_, hm⟩ => Acc.intro m (fun y ⟨hy, _⟩ => by omega))
  · exact Acc.intro n (fun _ ⟨h, _⟩ => absurd h hn)

theorem infBranchGame_not_finitelyBranching : ¬ infBranchGame.FinitelyBranching := by
  intro hfb
  rcases hfb 0 with ⟨L, hL⟩
  let m := listBound L + 1
  have hm : infBranchGame.move 0 m := ⟨rfl, by omega⟩
  have hmem : m ∈ L := (hL m).mp hm
  have hlt := lt_listBound hmem
  omega

theorem infBranchGame_not_isShort : ¬ infBranchGame.IsShort :=
  fun hshort => infBranchGame_not_finitelyBranching hshort.1

theorem infBranchGame_grundy : infBranchGame.IsGrundySeq infBranchSeq := by
  refine ⟨?_, ?_⟩
  · rintro n m ⟨rfl, hm⟩
    have hm0 : m ≠ 0 := by omega
    simp [infBranchSeq, hm0]
  · intro n v hv
    unfold infBranchSeq at hv
    split at hv
    · rename_i hn0
      subst hn0
      have hv0 : v = 0 := by omega
      subst hv0
      exact ⟨1, ⟨rfl, Nat.zero_lt_one⟩, rfl⟩
    · omega

theorem infBranchGame_rational_ogf : HasRationalGrundyOGF infBranchGame := by
  refine ⟨infBranchSeq, infBranchGame_grundy, eventuallyPeriodic_rational_ogf ?_⟩
  refine ⟨1, 1, Nat.zero_lt_one, fun n hn => ?_⟩
  have h1 : n ≠ 0 := by omega
  have h2 : n + 1 ≠ 0 := by omega
  simp [infBranchSeq, h1, h2]

theorem infBranchGame_rational_fibers : HasAllRationalGrundyFibers infBranchGame := by
  refine ⟨infBranchSeq, infBranchGame_grundy, eventuallyPeriodic_rational_fibers ?_⟩
  refine ⟨1, 1, Nat.zero_lt_one, fun n hn => ?_⟩
  have h1 : n ≠ 0 := by omega
  have h2 : n + 1 ≠ 0 := by omega
  simp [infBranchSeq, h1, h2]

/-! ### Counterexample 4: Lacunary Step-1 Game (`lacunaryLocalGame`)
    Short, bounded-step local (`K = 1`), bounded-outdegree (`B = 1`), yet its Sprague–Grundy
    generating function `∑_{k≥2} x^{2^k}` (and its nontrivial fiber) are IRRATIONAL. -/

def IsPow2Ge4 (n : Nat) : Prop :=
  ∃ k : Nat, 2 ≤ k ∧ n = 2 ^ k

def checkPow2Ge4 (n : Nat) : Nat → Bool
  | 0 => false
  | k + 1 => (decide (2 ≤ k) && (n == 2 ^ k)) || checkPow2Ge4 n k

private theorem nat_lt_two_pow : (k : Nat) → k < 2 ^ k
  | 0 => Nat.zero_lt_one
  | k + 1 => by
    have ih := nat_lt_two_pow k
    have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by
      rw [Nat.pow_succ]; omega
    omega

private theorem pow2_mono {a : Nat} : {b : Nat} → a ≤ b → 2 ^ a ≤ 2 ^ b
  | 0, h => by
    have ha : a = 0 := by omega
    subst ha; exact Nat.le_refl _
  | b + 1, h => by
    by_cases hab : a = b + 1
    · subst hab; exact Nat.le_refl _
    · have ih : 2 ^ a ≤ 2 ^ b := pow2_mono (a := a) (b := b) (by omega)
      rw [Nat.pow_succ]
      omega

private theorem checkPow2Ge4_iff (n : Nat) :
    ∀ fuel : Nat, (checkPow2Ge4 n fuel = true ↔ ∃ k : Nat, k < fuel ∧ 2 ≤ k ∧ n = 2 ^ k)
  | 0 => by simp [checkPow2Ge4]
  | fuel' + 1 => by
    simp only [checkPow2Ge4, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    rw [checkPow2Ge4_iff n fuel']
    constructor
    · rintro (⟨h2, hn⟩ | ⟨k, hk, h2, hn⟩)
      · exact ⟨fuel', by omega, h2, hn⟩
      · exact ⟨k, by omega, h2, hn⟩
    · rintro ⟨k, hk, h2, hn⟩
      by_cases hkf : k = fuel'
      · subst hkf; exact Or.inl ⟨h2, hn⟩
      · exact Or.inr ⟨k, by omega, h2, hn⟩

theorem checkPow2Ge4_spec (n : Nat) :
    checkPow2Ge4 n (n + 1) = true ↔ IsPow2Ge4 n := by
  rw [checkPow2Ge4_iff n (n + 1)]
  constructor
  · rintro ⟨k, _, h2, hn⟩
    exact ⟨k, h2, hn⟩
  · rintro ⟨k, h2, hn⟩
    have hklt : k < 2 ^ k := nat_lt_two_pow k
    exact ⟨k, by omega, h2, hn⟩

def lacunaryLocalGame : ImpartialGame where
  move n m := IsPow2Ge4 n ∧ m + 1 = n

def lacunarySeq (n : Nat) : Nat :=
  if checkPow2Ge4 n (n + 1) then 1 else 0

theorem lacunarySeq_eq_one_iff (n : Nat) :
    lacunarySeq n = 1 ↔ IsPow2Ge4 n := by
  unfold lacunarySeq
  rw [← checkPow2Ge4_spec n]
  cases checkPow2Ge4 n (n + 1) <;> simp

theorem lacunarySeq_eq_zero_iff (n : Nat) :
    lacunarySeq n = 0 ↔ ¬ IsPow2Ge4 n := by
  unfold lacunarySeq
  rw [← checkPow2Ge4_spec n]
  cases checkPow2Ge4 n (n + 1) <;> simp

private theorem pow2_even_of_ge2 {k : Nat} (hk : 2 ≤ k) : (2 ^ k) % 2 = 0 ∧ 4 ≤ 2 ^ k := by
  have hk2 : k = (k - 2) + 2 := by omega
  rw [hk2, Nat.pow_add]
  have h1 : 1 ≤ 2 ^ (k - 2) := pow2_mono (Nat.zero_le _)
  change (2 ^ (k - 2) * 4) % 2 = 0 ∧ 4 ≤ 2 ^ (k - 2) * 4
  omega

private theorem pred_not_isPow2Ge4 {n : Nat} (hn : IsPow2Ge4 n) : ¬ IsPow2Ge4 (n - 1) := by
  rcases hn with ⟨k, hk, rfl⟩
  rcases pow2_even_of_ge2 hk with ⟨heven, hge4⟩
  rintro ⟨r, hr, hreq⟩
  rcases pow2_even_of_ge2 hr with ⟨hreven, _⟩
  omega

theorem lacunaryLocalGame_boundedOutDegree : lacunaryLocalGame.IsBoundedOutDegree := by
  refine ⟨1, fun n => ?_⟩
  by_cases hpow : checkPow2Ge4 n (n + 1) = true
  · have hn : IsPow2Ge4 n := (checkPow2Ge4_spec n).mp hpow
    rcases hn with ⟨k, hk, hnk⟩
    rcases pow2_even_of_ge2 hk with ⟨_, hge4⟩
    refine ⟨[n - 1], by simp, fun m => ?_⟩
    simp only [lacunaryLocalGame, List.mem_singleton]
    constructor
    · rintro ⟨_, rfl⟩; omega
    · rintro rfl; exact ⟨⟨k, hk, hnk⟩, by omega⟩
  · have hnot : ¬ IsPow2Ge4 n := fun h => hpow ((checkPow2Ge4_spec n).mpr h)
    refine ⟨[], by simp, fun m => ?_⟩
    simp [lacunaryLocalGame, hnot]

theorem lacunaryLocalGame_boundedStepLocal : lacunaryLocalGame.IsBoundedStepLocal := by
  refine ⟨1, fun n m ⟨_, hmn⟩ => ?_⟩
  have hle : ¬ (n ≤ m) := by omega
  simp [ImpartialGame.natDist, hle]
  omega

theorem lacunaryLocalGame_isShort : lacunaryLocalGame.IsShort := by
  refine ⟨finitelyBranching_of_boundedOutDegree lacunaryLocalGame_boundedOutDegree, ?_⟩
  apply noInfinitePlay_of_lt
  intro n m ⟨_, hmn⟩
  omega

theorem lacunaryLocalGame_grundy : lacunaryLocalGame.IsGrundySeq lacunarySeq := by
  refine ⟨?_, ?_⟩
  · intro n m ⟨hn, hmn⟩
    have hm_not : ¬ IsPow2Ge4 m := by
      have hsub : m = n - 1 := by omega
      rw [hsub]
      exact pred_not_isPow2Ge4 hn
    have hgn : lacunarySeq n = 1 := (lacunarySeq_eq_one_iff n).mpr hn
    have hgm : lacunarySeq m = 0 := (lacunarySeq_eq_zero_iff m).mpr hm_not
    omega
  · intro n v hv
    by_cases hn : IsPow2Ge4 n
    · have hgn : lacunarySeq n = 1 := (lacunarySeq_eq_one_iff n).mpr hn
      have hv0 : v = 0 := by omega
      subst hv0
      rcases hn with ⟨k, hk, hnk⟩
      rcases pow2_even_of_ge2 hk with ⟨_, hge4⟩
      have hm_not : ¬ IsPow2Ge4 (n - 1) := pred_not_isPow2Ge4 ⟨k, hk, hnk⟩
      exact ⟨n - 1, ⟨⟨k, hk, hnk⟩, by omega⟩, (lacunarySeq_eq_zero_iff (n - 1)).mpr hm_not⟩
    · have hgn : lacunarySeq n = 0 := (lacunarySeq_eq_zero_iff n).mpr hn
      omega

private theorem not_isPow2Ge4_between {k δ : Nat}
    (hk : 2 ≤ k) (hδ1 : 1 ≤ δ) (hδ2 : δ < 2 ^ (k - 1)) :
    ¬ IsPow2Ge4 (2 ^ k - δ) := by
  rintro ⟨r, _, hreq⟩
  have hsplit : 2 ^ k = 2 ^ (k - 1) + 2 ^ (k - 1) := by
    have hk1 : k = (k - 1) + 1 := by omega
    conv => lhs; rw [hk1, Nat.pow_succ]
    omega
  by_cases hrk : r ≤ k - 1
  · have hle : 2 ^ r ≤ 2 ^ (k - 1) := pow2_mono hrk
    omega
  · have hge : 2 ^ k ≤ 2 ^ r := pow2_mono (by omega)
    omega

/-- Elementary lacunary gap proof: `∑_{k≥2} x^{2^k}` is NOT rational over `ℚ(x)`. -/
theorem lacunarySeq_not_rational_ogf : ¬ IsRationalOGF (grundyIntSeq lacunarySeq) := by
  rintro ⟨P, Q, hQ, hrel⟩
  rcases exists_first_nonzero hQ with ⟨i₀, hi₀_lt, hi₀_ne, hi₀_first⟩
  let k := P.length + Q.length + 2
  have hk2 : 2 ≤ k := by omega
  have hQ_lt_pow : Q.length < 2 ^ (k - 1) := by
    have hlt := nat_lt_two_pow (k - 1)
    omega
  have hP_lt_pow : P.length < 2 ^ k := by
    have hlt := nat_lt_two_pow k
    omega
  have hk_dbl : 2 ^ k = 2 ^ (k - 1) + 2 ^ (k - 1) := by
    have hk1 : k = (k - 1) + 1 := by omega
    conv => lhs; rw [hk1, Nat.pow_succ]
    omega
  let N := 2 ^ k + i₀
  have hPN : coeff P N = 0 := coeff_eq_zero_of_le (by omega)
  have hSN := hrel N
  rw [hPN] at hSN
  unfold seriesMulPolyCoeff at hSN
  have hsingle := sumRange_eq_single
    (f := fun j => coeff Q j * grundyIntSeq lacunarySeq (N - j))
    (i₀ := i₀) (m := N + 1) (by omega) ?_
  · rw [hsingle] at hSN
    dsimp only at hSN
    have hsub : N - i₀ = 2 ^ k := by omega
    have ha1 : lacunarySeq (2 ^ k) = 1 :=
      (lacunarySeq_eq_one_iff (2 ^ k)).mpr ⟨k, hk2, rfl⟩
    rw [hsub] at hSN
    simp [grundyIntSeq, ha1] at hSN
    exact hi₀_ne hSN
  · intro j _ hji₀
    dsimp only
    by_cases hjlt : j < i₀
    · rw [hi₀_first j hjlt, Int.zero_mul]
    · by_cases hjQ : j < Q.length
      · have hgt : i₀ < j := by omega
        have hsub : N - j = 2 ^ k - (j - i₀) := by omega
        have hnot : ¬ IsPow2Ge4 (2 ^ k - (j - i₀)) :=
          not_isPow2Ge4_between hk2 (by omega) (by omega)
        have ha0 : lacunarySeq (N - j) = 0 := by
          rw [hsub]
          exact (lacunarySeq_eq_zero_iff _).mpr hnot
        simp [grundyIntSeq, ha0]
      · have hcz : coeff Q j = 0 := coeff_eq_zero_of_le (by omega)
        rw [hcz, Int.zero_mul]

theorem lacunaryLocalGame_not_rational_ogf : ¬ HasRationalGrundyOGF lacunaryLocalGame := by
  rintro ⟨g, hg, hrat⟩
  have heq : ∀ n : Nat, g n = lacunarySeq n :=
    grundy_unique lacunaryLocalGame_isShort.2 hg lacunaryLocalGame_grundy
  have hfun : grundyIntSeq g = grundyIntSeq lacunarySeq := by
    funext n
    simp [grundyIntSeq, heq n]
  rw [hfun] at hrat
  exact lacunarySeq_not_rational_ogf hrat

theorem lacunaryLocalGame_not_rational_fibers : ¬ HasAllRationalGrundyFibers lacunaryLocalGame := by
  rintro ⟨g, hg, hfib⟩
  have heq : ∀ n : Nat, g n = lacunarySeq n :=
    grundy_unique lacunaryLocalGame_isShort.2 hg lacunaryLocalGame_grundy
  have h1 : grundyFiberSeq g 1 = grundyIntSeq lacunarySeq := by
    funext n
    rw [grundyFiberSeq, heq n, grundyIntSeq]
    unfold lacunarySeq
    cases checkPow2Ge4 n (n + 1) <;> rfl
  have hrat1 := hfib 1
  rw [h1] at hrat1
  exact lacunarySeq_not_rational_ogf hrat1

private theorem sumRange_add_seq (f₁ f₂ : Nat → Int) :
    (m : Nat) → sumRange (fun j => f₁ j + f₂ j) m = sumRange f₁ m + sumRange f₂ m
  | 0 => rfl
  | m + 1 => by
    simp only [sumRange, sumRange_add_seq f₁ f₂ m]
    omega

/-- Even the `P`-position indicator GF `∑_{g(n)=0} x^n` of `lacunaryLocalGame` is irrational. -/
theorem lacunarySeq_fiber0_not_rational_ogf :
    ¬ IsRationalOGF (grundyFiberSeq lacunarySeq 0) := by
  rintro ⟨P, Q, hQ, hrel⟩
  rcases exists_first_nonzero hQ with ⟨i₀, hi₀_lt, hi₀_ne, hi₀_first⟩
  let k := P.length + Q.length + 3
  have hk2 : 2 ≤ k := by omega
  have hQ_lt_pow : Q.length < 2 ^ (k - 1) := by
    have hlt := nat_lt_two_pow (k - 1)
    omega
  have hP_lt_pow : P.length < 2 ^ k := by
    have hlt := nat_lt_two_pow k
    omega
  have hk_dbl : 2 ^ k = 2 ^ (k - 1) + 2 ^ (k - 1) := by
    have hk1 : k = (k - 1) + 1 := by omega
    conv => lhs; rw [hk1, Nat.pow_succ]
    omega
  have hpart : ∀ m : Nat,
      grundyFiberSeq lacunarySeq 0 m + grundyIntSeq lacunarySeq m = 1 := by
    intro m
    unfold grundyFiberSeq grundyIntSeq lacunarySeq
    cases checkPow2Ge4 m (m + 1) <;> rfl
  have hsum_rel : ∀ n : Nat, Q.length ≤ n + 1 → P.length ≤ n →
      sumRange (fun j => coeff Q j * grundyIntSeq lacunarySeq (n - j)) Q.length =
      sumRange (fun j => coeff Q j) Q.length := by
    intro n hQn hPn
    have hSn : seriesMulPolyCoeff Q (grundyFiberSeq lacunarySeq 0) n = 0 := by
      rw [hrel n, coeff_eq_zero_of_le hPn]
    rw [seriesMulPolyCoeff_eq_sumRange_len Q _ hQn] at hSn
    have hcomb :
        sumRange (fun j => coeff Q j) Q.length =
        sumRange (fun j => coeff Q j * grundyFiberSeq lacunarySeq 0 (n - j) +
          coeff Q j * grundyIntSeq lacunarySeq (n - j)) Q.length := by
      apply sumRange_congr
      intro j _
      have hp := hpart (n - j)
      have hmul := congrArg (fun z => coeff Q j * z) hp
      simp [Int.mul_add] at hmul
      exact hmul.symm
    rw [hcomb, sumRange_add_seq, hSn, Int.zero_add]
  -- Evaluate at `N₁ = 2^k + Q.length` (strictly between `2^k` and `2^(k+1)` when `Q.length > 0`,
  -- so `N₁ = 2^k + Q.length`: for `j < Q.length`, `1 ≤ Q.length - j ≤ Q.length < 2^k = 2^((k+1)-1)`).
  let N₁ := 2 ^ k + Q.length
  have hN1_zero :
      sumRange (fun j => coeff Q j * grundyIntSeq lacunarySeq (N₁ - j)) Q.length = 0 := by
    apply sumRange_zero
    intro j hj
    dsimp only
    have hpow1 : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
    have hsub : N₁ - j = 2 ^ (k + 1) - (2 ^ k - (Q.length - j)) := by
      dsimp [N₁]
      omega
    have hnot : ¬ IsPow2Ge4 (N₁ - j) := by
      rw [hsub]
      apply not_isPow2Ge4_between (k := k + 1) (by omega) (by omega)
      change 2 ^ k - (Q.length - j) < 2 ^ k
      omega
    have ha0 : lacunarySeq (N₁ - j) = 0 := (lacunarySeq_eq_zero_iff _).mpr hnot
    simp [grundyIntSeq, ha0]
  have hQsum0 : sumRange (fun j => coeff Q j) Q.length = 0 := by
    rw [← hsum_rel N₁ (by omega) (by omega)]
    exact hN1_zero
  -- Evaluate at `N₀ = 2^k + i₀`.
  let N₀ := 2 ^ k + i₀
  have hN0_eq := hsum_rel N₀ (by omega) (by omega)
  rw [hQsum0] at hN0_eq
  have hsingle := sumRange_eq_single
    (f := fun j => coeff Q j * grundyIntSeq lacunarySeq (N₀ - j))
    (i₀ := i₀) (m := Q.length) hi₀_lt ?_
  · rw [hsingle] at hN0_eq
    dsimp only at hN0_eq
    have hsub : N₀ - i₀ = 2 ^ k := by omega
    have ha1 : lacunarySeq (2 ^ k) = 1 :=
      (lacunarySeq_eq_one_iff (2 ^ k)).mpr ⟨k, hk2, rfl⟩
    rw [hsub] at hN0_eq
    simp [grundyIntSeq, ha1] at hN0_eq
    exact hi₀_ne hN0_eq
  · intro j hjQ hji₀
    dsimp only
    by_cases hjlt : j < i₀
    · rw [hi₀_first j hjlt, Int.zero_mul]
    · have hsub : N₀ - j = 2 ^ k - (j - i₀) := by omega
      have hnot : ¬ IsPow2Ge4 (2 ^ k - (j - i₀)) :=
        not_isPow2Ge4_between hk2 (by omega) (by omega)
      have ha0 : lacunarySeq (N₀ - j) = 0 := by
        rw [hsub]
        exact (lacunarySeq_eq_zero_iff _).mpr hnot
      simp [grundyIntSeq, ha0]

theorem lacunaryLocalGame_not_rational_pPositions :
    ¬ HasRationalPPositionOGF lacunaryLocalGame := by
  rintro ⟨g, hg, hrat⟩
  have heq : ∀ n : Nat, g n = lacunarySeq n :=
    grundy_unique lacunaryLocalGame_isShort.2 hg lacunaryLocalGame_grundy
  have h0 : grundyFiberSeq g 0 = grundyFiberSeq lacunarySeq 0 := by
    funext n
    simp [grundyFiberSeq, heq n]
  rw [h0] at hrat
  exact lacunarySeq_fiber0_not_rational_ogf hrat

end Conjecture00000001290
