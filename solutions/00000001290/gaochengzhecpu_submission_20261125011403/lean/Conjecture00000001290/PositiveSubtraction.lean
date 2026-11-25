/-
  Conjecture 00000001290 — Positive Theorem for Finite Subtraction Games
  Core Lean 4.19.0 (zero external dependencies)
-/
import Conjecture00000001290.GeneratingFunction

namespace Conjecture00000001290

/-! ### General Infinite-to-Finite Pigeonhole Principle -/

/-- For any finite list `U` and sequence `w : Nat → α` taking values in `U`,
    there exist `i < j` with `w i = w j`. -/
theorem pigeonhole_seq {α : Type} :
    ∀ (U : List α) (w : Nat → α), (∀ n : Nat, w n ∈ U) →
    ∃ i j : Nat, i < j ∧ w i = w j
  | [], w, hw => nomatch (hw 0)
  | u :: us, w, hw => by
    by_cases htwo : ∃ i j : Nat, i < j ∧ w i = u ∧ w j = u
    · rcases htwo with ⟨i, j, hij, hwi, hwj⟩
      exact ⟨i, j, hij, hwi.trans hwj.symm⟩
    · by_cases hone : ∃ i₀ : Nat, w i₀ = u
      · rcases hone with ⟨i₀, hi₀⟩
        let w' : Nat → α := fun k => w (i₀ + 1 + k)
        have hw' : ∀ k : Nat, w' k ∈ us := by
          intro k
          cases hw (i₀ + 1 + k) with
          | head _ =>
            exfalso
            exact htwo ⟨i₀, i₀ + 1 + k, by omega, hi₀, rfl⟩
          | tail _ hmem => exact hmem
        rcases pigeonhole_seq us w' hw' with ⟨k₁, k₂, hk, heq⟩
        exact ⟨i₀ + 1 + k₁, i₀ + 1 + k₂, by omega, heq⟩
      · have hw_us : ∀ n : Nat, w n ∈ us := by
          intro n
          cases hw n with
          | head _ =>
            exfalso
            exact hone ⟨n, rfl⟩
          | tail _ hmem => exact hmem
        exact pigeonhole_seq us w hw_us

/-! ### Enumeration of all bounded tuples in `{0, ..., M - 1}^K` -/

def prependAll : Nat → List (List Nat) → List (List Nat)
  | 0, _ => []
  | v + 1, rest => rest.map (fun L => v :: L) ++ prependAll v rest

def allBoundedLists (M : Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | k + 1 => prependAll M (allBoundedLists M k)

private theorem mem_prependAll {x : Nat} {xs : List Nat} {rest : List (List Nat)}
    (hxs : xs ∈ rest) :
    ∀ {M : Nat}, x < M → (x :: xs) ∈ prependAll M rest
  | 0, hx => by omega
  | v + 1, hx => by
    unfold prependAll
    rw [List.mem_append]
    by_cases hxv : x = v
    · subst hxv
      exact Or.inl (List.mem_map_of_mem hxs)
    · exact Or.inr (mem_prependAll hxs (by omega))

private theorem mem_allBoundedLists {M : Nat} :
    {L : List Nat} → {K : Nat} → L.length = K → (∀ x : Nat, x ∈ L → x < M) →
    L ∈ allBoundedLists M K
  | [], 0, _, _ => List.Mem.head []
  | _ :: _, 0, hlen, _ => by simp at hlen
  | [], _ + 1, hlen, _ => by simp at hlen
  | x :: xs, k + 1, hlen, hbd => by
    unfold allBoundedLists
    apply mem_prependAll
    · apply mem_allBoundedLists (by simp at hlen; exact hlen)
      intro y hy
      exact hbd y (List.Mem.tail x hy)
    · exact hbd x (List.Mem.head xs)

/-! ### Sliding state window `[g (n + K - 1), ..., g n]` -/

def stateWindow (g : Nat → Nat) (n : Nat) : Nat → List Nat
  | 0 => []
  | k + 1 => g (n + k) :: stateWindow g n k

private theorem length_stateWindow (g : Nat → Nat) (n : Nat) :
    (k : Nat) → (stateWindow g n k).length = k
  | 0 => rfl
  | k + 1 => by simp [stateWindow, length_stateWindow g n k]

private theorem mem_stateWindow {g : Nat → Nat} {n x : Nat} :
    {k : Nat} → x ∈ stateWindow g n k → ∃ j : Nat, j < k ∧ g (n + j) = x
  | 0, h => nomatch h
  | k + 1, h => by
    simp only [stateWindow, List.mem_cons] at h
    cases h with
    | inl hxk => exact ⟨k, by omega, hxk.symm⟩
    | inr hmem =>
      rcases mem_stateWindow hmem with ⟨j, hj, hgj⟩
      exact ⟨j, by omega, hgj⟩

private theorem stateWindow_eq_iff (g : Nat → Nat) (n₁ n₂ : Nat) :
    (k : Nat) →
    (stateWindow g n₁ k = stateWindow g n₂ k ↔ ∀ j : Nat, j < k → g (n₁ + j) = g (n₂ + j))
  | 0 => by simp [stateWindow]
  | k + 1 => by
    simp only [stateWindow, List.cons.injEq]
    rw [stateWindow_eq_iff g n₁ n₂ k]
    constructor
    · rintro ⟨hk, hall⟩ j hj
      by_cases hjk : j = k
      · subst hjk; exact hk
      · exact hall j (by omega)
    · intro hall
      exact ⟨hall k (by omega), fun j hj => hall j (by omega)⟩

/-! ### Locality, Shortness, Eventual Periodicity, and Rationality of Finite Subtraction Games -/

/-- Option list of a finite subtraction game at position `n`. -/
def subOpts (S : List Nat) (n : Nat) : List Nat :=
  (S.filter (fun s => decide (s ≤ n))).map (fun s => n - s)

private theorem subOpts_length_le (S : List Nat) (n : Nat) :
    (subOpts S n).length ≤ S.length := by
  unfold subOpts
  rw [List.length_map]
  exact List.length_filter_le _ S

private theorem mem_subOpts_iff (S : List Nat) (n m : Nat) :
    m ∈ subOpts S n ↔ ∃ s : Nat, s ∈ S ∧ s ≤ n ∧ m = n - s := by
  unfold subOpts
  rw [List.mem_map]
  constructor
  · rintro ⟨s, hs, hm⟩
    rw [List.mem_filter, decide_eq_true_eq] at hs
    exact ⟨s, hs.1, hs.2, hm.symm⟩
  · rintro ⟨s, hsS, hsn, hm⟩
    refine ⟨s, ?_, hm.symm⟩
    rw [List.mem_filter, decide_eq_true_eq]
    exact ⟨hsS, hsn⟩

theorem finiteSubtraction_boundedOutDegree {G : ImpartialGame}
    (hfin : G.IsFiniteSubtractionGame) : G.IsBoundedOutDegree := by
  rcases hfin with ⟨S, _, hmove⟩
  refine ⟨S.length, fun n => ⟨subOpts S n, subOpts_length_le S n, ?_⟩⟩
  intro m
  rw [hmove n m, mem_subOpts_iff]

theorem finiteSubtraction_boundedStepLocal {G : ImpartialGame}
    (hfin : G.IsFiniteSubtractionGame) : G.IsBoundedStepLocal := by
  rcases hfin with ⟨S, _, hmove⟩
  refine ⟨listBound S, fun n m hm => ?_⟩
  rcases (hmove n m).mp hm with ⟨s, hsS, hsn, rfl⟩
  have hslt : s < listBound S := lt_listBound hsS
  unfold ImpartialGame.natDist
  by_cases hn : n ≤ n - s
  · simp [hn]; omega
  · simp [hn]; omega

theorem finiteSubtraction_isShort {G : ImpartialGame}
    (hfin : G.IsFiniteSubtractionGame) : G.IsShort := by
  refine ⟨finitelyBranching_of_boundedOutDegree (finiteSubtraction_boundedOutDegree hfin), ?_⟩
  rcases hfin with ⟨S, hpos, hmove⟩
  apply noInfinitePlay_of_lt
  intro n m hm
  rcases (hmove n m).mp hm with ⟨s, hsS, hsn, rfl⟩
  have hs0 : 0 < s := hpos s hsS
  omega

/-- Every Sprague–Grundy sequence of a finite subtraction game is eventually periodic. -/
theorem finiteSubtraction_eventuallyPeriodic {G : ImpartialGame}
    (hfin : G.IsFiniteSubtractionGame) {g : Nat → Nat} (hg : G.IsGrundySeq g) :
    EventuallyPeriodic g := by
  rcases hfin with ⟨S, hpos, hmove⟩
  have hdeg : ∀ n : Nat, ∃ L : List Nat, L.length ≤ S.length ∧ ∀ m : Nat, G.move n m ↔ m ∈ L := by
    intro n
    refine ⟨subOpts S n, subOpts_length_le S n, fun m => ?_⟩
    rw [hmove n m, mem_subOpts_iff]
  have hg_le : ∀ n : Nat, g n ≤ S.length := grundy_le_outdegree hdeg hg
  let K := listBound S
  let M := S.length + 1
  by_cases hK : K = 0
  · refine ⟨0, 1, Nat.zero_lt_one, fun n _ => ?_⟩
    have hS_empty : ∀ s : Nat, s ∉ S := by
      intro s hs
      have hlt := lt_listBound hs
      omega
    have hg0 : ∀ x : Nat, g x = 0 := by
      intro x
      by_cases hgx : g x = 0
      · exact hgx
      · rcases hg.2 x 0 (by omega) with ⟨m, hm, _⟩
        rcases (hmove x m).mp hm with ⟨s, hsS, _, _⟩
        exact absurd hsS (hS_empty s)
    rw [hg0 (n + 1), hg0 n]
  · let w : Nat → List Nat := fun n => stateWindow g n K
    have hw_mem : ∀ n : Nat, w n ∈ allBoundedLists M K := by
      intro n
      apply mem_allBoundedLists (length_stateWindow g n K)
      intro x hx
      rcases mem_stateWindow hx with ⟨j, _, rfl⟩
      have hle := hg_le (n + j)
      omega
    rcases pigeonhole_seq (allBoundedLists M K) w hw_mem with ⟨n₁, n₂, hn12, hweq⟩
    have hstep : ∀ a b : Nat, stateWindow g a K = stateWindow g b K → g (a + K) = g (b + K) := by
      intro a b hab
      have hwin := (stateWindow_eq_iff g a b K).mp hab
      have hopt_eq : ∀ s : Nat, s ∈ S → g (a + K - s) = g (b + K - s) := by
        intro s hsS
        have hs0 : 0 < s := hpos s hsS
        have hsK : s < K := lt_listBound hsS
        have ha_sub : a + K - s = a + (K - s) := by omega
        have hb_sub : b + K - s = b + (K - s) := by omega
        rw [ha_sub, hb_sub]
        exact hwin (K - s) (by omega)
      by_cases hlt : g (a + K) < g (b + K)
      · rcases hg.2 (b + K) (g (a + K)) hlt with ⟨m, hm, hgm⟩
        rcases (hmove (b + K) m).mp hm with ⟨s, hsS, _, rfl⟩
        have hsK : s < K := lt_listBound hsS
        have hma : G.move (a + K) (a + K - s) :=
          (hmove (a + K) (a + K - s)).mpr ⟨s, hsS, by omega, rfl⟩
        have hga : g (a + K - s) = g (a + K) := (hopt_eq s hsS).trans hgm
        exact absurd hga (hg.1 (a + K) (a + K - s) hma)
      · by_cases hgt : g (b + K) < g (a + K)
        · rcases hg.2 (a + K) (g (b + K)) hgt with ⟨m, hm, hgm⟩
          rcases (hmove (a + K) m).mp hm with ⟨s, hsS, _, rfl⟩
          have hsK : s < K := lt_listBound hsS
          have hmb : G.move (b + K) (b + K - s) :=
            (hmove (b + K) (b + K - s)).mpr ⟨s, hsS, by omega, rfl⟩
          have hgb : g (b + K - s) = g (b + K) := (hopt_eq s hsS).symm.trans hgm
          exact absurd hgb (hg.1 (b + K) (b + K - s) hmb)
        · omega
    have hshift : ∀ t : Nat, stateWindow g (n₁ + t) K = stateWindow g (n₂ + t) K := by
      intro t
      induction t with
      | zero => simpa using hweq
      | succ t' ih =>
        rw [stateWindow_eq_iff] at ih ⊢
        intro j hj
        by_cases hj1 : j + 1 < K
        · have h := ih (j + 1) hj1
          have ha : n₁ + t' + (j + 1) = n₁ + (t' + 1) + j := by omega
          have hb : n₂ + t' + (j + 1) = n₂ + (t' + 1) + j := by omega
          rw [← ha, ← hb]
          exact h
        · have hjK : j + 1 = K := by omega
          have htop := hstep (n₁ + t') (n₂ + t') ((stateWindow_eq_iff g _ _ K).mpr ih)
          have ha : n₁ + t' + K = n₁ + (t' + 1) + j := by omega
          have hb : n₂ + t' + K = n₂ + (t' + 1) + j := by omega
          rw [← ha, ← hb]
          exact htop
    refine ⟨n₁, n₂ - n₁, by omega, fun n hn => ?_⟩
    have hwin_t := (stateWindow_eq_iff g (n₁ + (n - n₁)) (n₂ + (n - n₁)) K).mp
      (hshift (n - n₁)) 0 (by omega)
    have ha : n₁ + (n - n₁) + 0 = n := by omega
    have hb : n₂ + (n - n₁) + 0 = n + (n₂ - n₁) := by omega
    rw [ha, hb] at hwin_t
    exact hwin_t.symm

/-- Sufficiency holds for 1D finite subtraction games: every finite subtraction game has
    a rational Sprague–Grundy value OGF and rational Grundy-fiber indicator OGFs. -/
theorem finiteSubtraction_rational_ogf {G : ImpartialGame}
    (hfin : G.IsFiniteSubtractionGame) :
    HasRationalGrundyOGF G ∧ HasAllRationalGrundyFibers G := by
  rcases short_has_grundy (finiteSubtraction_isShort hfin) with ⟨g, hg⟩
  have hep : EventuallyPeriodic g := finiteSubtraction_eventuallyPeriodic hfin hg
  exact ⟨⟨g, hg, eventuallyPeriodic_rational_ogf hep⟩,
         ⟨g, hg, eventuallyPeriodic_rational_fibers hep⟩⟩

end Conjecture00000001290
