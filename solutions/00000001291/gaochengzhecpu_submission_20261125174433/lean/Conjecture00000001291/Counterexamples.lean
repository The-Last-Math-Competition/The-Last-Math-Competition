import Conjecture00000001291.Basic
import Conjecture00000001291.Poset

namespace Conjecture00000001291
open IGame

/-- Canonical misère building blocks up to layer height 4:
    `g0 = 0`, `g1 = *`, `g2 = *2`, `g2b = {*2}`, `g3 = *3`, `g4 = *4`, `g5 = {0, *, *2, {*2}, *3}`. -/
def g2 : IGame := .mk [g0, g1]
def g2b : IGame := .mk [g2]
def g3 : IGame := .mk [g0, g1, g2]
def g4 : IGame := .mk [g0, g1, g2, g3]
def g5 : IGame := .mk [g0, g1, g2, g2b, g3]

/-- The 10 canonical misère Grundy values in `U₄ = {u ∈ M₄ : 0 ∈ u}` (all of layer height ≤ 4). -/
def u1 : IGame := g1
def u2 : IGame := g2
def u3 : IGame := g3
def u4 : IGame := .mk [g0, g2b]
def u5 : IGame := .mk [g0, g2, g2b]
def u6 : IGame := .mk [g0, g2b, g3]
def u7 : IGame := .mk [g0, g1, g2, g2b]
def u8 : IGame := g4
def u9 : IGame := .mk [g0, g2, g2b, g3]
def u10 : IGame := g5

/-- 8-element distinguishing context pool (maximum tree size: 23 nodes). -/
def w0 : IGame := g0
def w1 : IGame := g1
def w2 : IGame := g2
def w3 : IGame := .mk [g2b]
def w4 : IGame := g3
def w5 : IGame := .mk [g1, g2, .mk [g2b]]
def w6 : IGame := .mk [g0, g1, .mk [g0, g1, .mk [g1, g2b]]]
def w7 : IGame := .mk [g1, g2, g3, .mk [g1, g2b]]

def witnessPool : List IGame := [w0, w1, w2, w3, w4, w5, w6, w7]

/-- Decidable separation check via `witnessPool` and `misereWinAdd`. -/
def separatedByPool (a b : IGame) : Bool :=
  witnessPool.any (fun w => misereWinAdd a w != misereWinAdd b w)

theorem not_misereEquiv_of_separatedByPool {a b : IGame}
    (h : separatedByPool a b = true) : ¬ MisereEquiv a b := by
  obtain ⟨w, _, hne⟩ := List.any_eq_true.mp h
  intro heq
  have hw := heq w
  rw [misereWin_add_eq, misereWin_add_eq] at hw
  rw [hw] at hne
  simp at hne

/-- Boolean check that all pairs in a list are separated by `witnessPool`. -/
def pairwiseSeparated : List IGame → Bool
  | [] => true
  | g :: gs => gs.all (separatedByPool g) && pairwiseSeparated gs

theorem pairwiseInequiv_of_pairwiseSeparated :
    ∀ {gs : List IGame}, pairwiseSeparated gs = true → PairwiseInequiv gs
  | [], _ => .nil
  | g :: gs, h => by
    simp only [pairwiseSeparated, Bool.and_eq_true, List.all_eq_true] at h
    exact .cons (fun x hx => not_misereEquiv_of_separatedByPool (h.1 x hx))
      (pairwiseInequiv_of_pairwiseSeparated h.2)

/-- Enumeration of all sublists and all proper sublists of a list. -/
def allSublists : List IGame → List (List IGame)
  | [] => [[]]
  | x :: xs => allSublists xs ++ (allSublists xs).map (x :: ·)

def properSublists : List IGame → List (List IGame)
  | [] => []
  | x :: xs => allSublists xs ++ (properSublists xs).map (x :: ·)

theorem filter_mem_allSublists (p : IGame → Bool) :
    ∀ (xs : List IGame), xs.filter p ∈ allSublists xs
  | [] => .head _
  | x :: xs => by
    unfold List.filter allSublists
    cases p x with
    | false => exact List.mem_append_left _ (filter_mem_allSublists p xs)
    | true =>
      apply List.mem_append_right
      exact List.mem_map.mpr ⟨xs.filter p, filter_mem_allSublists p xs, rfl⟩

theorem filter_mem_properSublists (p : IGame → Bool) :
    ∀ {xs : List IGame}, (∃ y ∈ xs, p y = false) → xs.filter p ∈ properSublists xs
  | [], ⟨_, hy, _⟩ => nomatch hy
  | x :: xs, ⟨y, hy, hpy⟩ => by
    unfold List.filter properSublists
    cases hpx : p x with
    | false => exact List.mem_append_left _ (filter_mem_allSublists p xs)
    | true =>
      cases List.mem_cons.mp hy with
      | inl heq =>
        subst heq
        rw [hpx] at hpy
        nomatch hpy
      | inr hmem =>
        apply List.mem_append_right
        exact List.mem_map.mpr ⟨xs.filter p, filter_mem_properSublists p ⟨y, hmem, hpy⟩, rfl⟩

theorem mem_of_any_beq_true {z : IGame} {s : List IGame}
    (h : (s.any (fun w => beq z w)) = true) : z ∈ s := by
  obtain ⟨w, hw, hb⟩ := List.any_eq_true.mp h
  rw [eq_of_beq hb]
  exact hw

theorem any_beq_true_of_mem {z : IGame} {s : List IGame} (h : z ∈ s) :
    (s.any (fun w => beq z w)) = true :=
  List.any_eq_true.mpr ⟨z, h, beq_refl z⟩

theorem exists_false_of_not_subset :
    ∀ {gs s : List IGame}, (¬ ∀ z ∈ gs, z ∈ s) →
      ∃ y ∈ gs, (s.any (fun w => beq y w)) = false
  | [], _, hnot => False.elim (hnot (fun _ hz => nomatch hz))
  | x :: xs, s, hnot => by
    cases hx : s.any (fun w => beq x w) with
    | false => exact ⟨x, .head _, hx⟩
    | true =>
      have hxs : ¬ ∀ z ∈ xs, z ∈ s := by
        intro hall
        apply hnot
        intro z hz
        cases List.mem_cons.mp hz with
        | inl heq => exact heq ▸ mem_of_any_beq_true hx
        | inr hm => exact hall z hm
      obtain ⟨y, hy, hfy⟩ := exists_false_of_not_subset hxs
      exact ⟨y, .tail _ hy, hfy⟩

/-- Soundness of finite proper-sublist separation for semantic `SubsetIrreducible`. -/
theorem subsetIrreducible_of_properSublists_sep {gs : List IGame}
    (hsep : ((properSublists gs).all (fun s' => separatedByPool (.mk gs) (.mk s'))) = true) :
    SubsetIrreducible (.mk gs) := by
  intro s ⟨hsub, hnot⟩ heq
  let p : IGame → Bool := fun z => s.any (fun w => beq z w)
  have hex : ∃ y ∈ gs, p y = false := exists_false_of_not_subset hnot
  have hmemProp : gs.filter p ∈ properSublists gs := filter_mem_properSublists p hex
  have hsepOne : separatedByPool (.mk gs) (.mk (gs.filter p)) = true :=
    (List.all_eq_true.mp hsep) (gs.filter p) hmemProp
  have hneq : ¬ MisereEquiv (.mk gs) (.mk (gs.filter p)) :=
    not_misereEquiv_of_separatedByPool hsepOne
  have hiff : ∀ z, z ∈ gs.filter p ↔ z ∈ s := by
    intro z
    constructor
    · intro hzf
      obtain ⟨_, hpz⟩ := List.mem_filter.mp hzf
      exact mem_of_any_beq_true hpz
    · intro hzs
      exact List.mem_filter.mpr ⟨hsub z hzs, any_beq_true_of_mem hzs⟩
  have heqFilter : MisereEquiv (.mk (gs.filter p)) (.mk s) := misereEquiv_of_mem_iff hiff
  exact hneq (MisereEquiv.symm (MisereEquiv.trans heqFilter heq))

/-! ### Canonical Verification of `g0..g5` and `u1..u10` -/

theorem canon_g0 : IsCanonicalMisere g0 :=
  .mk (fun _ h => nomatch h) .nil (subsetIrreducible_of_properSublists_sep rfl)

theorem canon_g1 : IsCanonicalMisere g1 :=
  .mk
    (fun c hc => by cases hc with | head => exact canon_g0 | tail _ h => nomatch h)
    (pairwiseInequiv_of_pairwiseSeparated rfl)
    (subsetIrreducible_of_properSublists_sep rfl)

theorem canon_g2 : IsCanonicalMisere g2 :=
  .mk
    (fun c hc => by
      cases hc with
      | head => exact canon_g0
      | tail _ h1 => cases h1 with | head => exact canon_g1 | tail _ h2 => nomatch h2)
    (pairwiseInequiv_of_pairwiseSeparated rfl)
    (subsetIrreducible_of_properSublists_sep rfl)

theorem canon_g2b : IsCanonicalMisere g2b :=
  .mk
    (fun c hc => by cases hc with | head => exact canon_g2 | tail _ h => nomatch h)
    (pairwiseInequiv_of_pairwiseSeparated rfl)
    (subsetIrreducible_of_properSublists_sep rfl)

theorem canon_g3 : IsCanonicalMisere g3 :=
  .mk
    (fun c hc => by
      cases hc with
      | head => exact canon_g0
      | tail _ h1 =>
        cases h1 with
        | head => exact canon_g1
        | tail _ h2 => cases h2 with | head => exact canon_g2 | tail _ h3 => nomatch h3)
    (pairwiseInequiv_of_pairwiseSeparated rfl)
    (subsetIrreducible_of_properSublists_sep rfl)

theorem canon_g4 : IsCanonicalMisere g4 :=
  .mk
    (fun c hc => by
      cases hc with
      | head => exact canon_g0
      | tail _ h1 =>
        cases h1 with
        | head => exact canon_g1
        | tail _ h2 =>
          cases h2 with
          | head => exact canon_g2
          | tail _ h3 => cases h3 with | head => exact canon_g3 | tail _ h4 => nomatch h4)
    (pairwiseInequiv_of_pairwiseSeparated rfl)
    (subsetIrreducible_of_properSublists_sep rfl)

theorem canon_g5 : IsCanonicalMisere g5 :=
  .mk
    (fun c hc => by
      cases hc with
      | head => exact canon_g0
      | tail _ h1 =>
        cases h1 with
        | head => exact canon_g1
        | tail _ h2 =>
          cases h2 with
          | head => exact canon_g2
          | tail _ h3 =>
            cases h3 with
            | head => exact canon_g2b
            | tail _ h4 => cases h4 with | head => exact canon_g3 | tail _ h5 => nomatch h5)
    (pairwiseInequiv_of_pairwiseSeparated rfl)
    (subsetIrreducible_of_properSublists_sep rfl)

theorem canon_u4 : IsCanonicalMisere u4 :=
  .mk
    (fun c hc => by
      cases hc with
      | head => exact canon_g0
      | tail _ h1 => cases h1 with | head => exact canon_g2b | tail _ h2 => nomatch h2)
    (pairwiseInequiv_of_pairwiseSeparated rfl)
    (subsetIrreducible_of_properSublists_sep rfl)

theorem canon_u5 : IsCanonicalMisere u5 :=
  .mk
    (fun c hc => by
      cases hc with
      | head => exact canon_g0
      | tail _ h1 =>
        cases h1 with
        | head => exact canon_g2
        | tail _ h2 => cases h2 with | head => exact canon_g2b | tail _ h3 => nomatch h3)
    (pairwiseInequiv_of_pairwiseSeparated rfl)
    (subsetIrreducible_of_properSublists_sep rfl)

theorem canon_u6 : IsCanonicalMisere u6 :=
  .mk
    (fun c hc => by
      cases hc with
      | head => exact canon_g0
      | tail _ h1 =>
        cases h1 with
        | head => exact canon_g2b
        | tail _ h2 => cases h2 with | head => exact canon_g3 | tail _ h3 => nomatch h3)
    (pairwiseInequiv_of_pairwiseSeparated rfl)
    (subsetIrreducible_of_properSublists_sep rfl)

theorem canon_u7 : IsCanonicalMisere u7 :=
  .mk
    (fun c hc => by
      cases hc with
      | head => exact canon_g0
      | tail _ h1 =>
        cases h1 with
        | head => exact canon_g1
        | tail _ h2 =>
          cases h2 with
          | head => exact canon_g2
          | tail _ h3 => cases h3 with | head => exact canon_g2b | tail _ h4 => nomatch h4)
    (pairwiseInequiv_of_pairwiseSeparated rfl)
    (subsetIrreducible_of_properSublists_sep rfl)

theorem canon_u9 : IsCanonicalMisere u9 :=
  .mk
    (fun c hc => by
      cases hc with
      | head => exact canon_g0
      | tail _ h1 =>
        cases h1 with
        | head => exact canon_g2
        | tail _ h2 =>
          cases h2 with
          | head => exact canon_g2b
          | tail _ h3 => cases h3 with | head => exact canon_g3 | tail _ h4 => nomatch h4)
    (pairwiseInequiv_of_pairwiseSeparated rfl)
    (subsetIrreducible_of_properSublists_sep rfl)

/-!
### Convention A Refutation (Layer `n = 4`, Canonical Option-Inclusion Order on `Mₙ`):
At misère layer height `n = 4`, `g0 ⊂ g1 ⊂ g2 ⊂ g3 ⊂ g4 ⊂ g5` is a strict chain of 6 canonical
misère Grundy values (poset height `5 > 4`, vertex cardinality `6 > 4`).
-/

/-- Domain of canonical misère Grundy values of layer height at most `n`. -/
def CanonicalMisereLayer (n : Nat) (g : IGame) : Prop :=
  IsCanonicalMisere g ∧ g.layerHeight ≤ n

def decideOptionSubset (a b : IGame) : Bool :=
  a.options.all (fun x => b.options.any (fun y => beq x y))

theorem optionSubset_of_decide {a b : IGame} (h : decideOptionSubset a b = true) :
    OptionSubset a b := by
  intro x hx
  have hy := (List.all_eq_true.mp h) x hx
  exact mem_of_any_beq_true hy

theorem not_optionSubset_of_decide_false {a b : IGame} (h : decideOptionSubset a b = false) :
    ¬ OptionSubset a b := by
  intro hsub
  have hall : decideOptionSubset a b = true :=
    List.all_eq_true.mpr (fun x hx => any_beq_true_of_mem (hsub x hx))
  rw [h] at hall
  nomatch hall

theorem strictOptionSubset_of_bools {a b : IGame}
    (h1 : decideOptionSubset a b = true) (h2 : decideOptionSubset b a = false) :
    StrictOptionSubset a b :=
  ⟨optionSubset_of_decide h1, not_optionSubset_of_decide_false h2⟩

theorem chainA_witness_height_5 :
    HasChainOfHeight (CanonicalMisereLayer 4) StrictOptionSubset 5 := by
  refine ⟨[g0, g1, g2, g3, g4, g5], rfl, ?_⟩
  exact .cons ⟨canon_g0, by decide⟩ (strictOptionSubset_of_bools rfl rfl)
    (.cons ⟨canon_g1, by decide⟩ (strictOptionSubset_of_bools rfl rfl)
      (.cons ⟨canon_g2, by decide⟩ (strictOptionSubset_of_bools rfl rfl)
        (.cons ⟨canon_g3, by decide⟩ (strictOptionSubset_of_bools rfl rfl)
          (.cons ⟨canon_g4, by decide⟩ (strictOptionSubset_of_bools rfl rfl)
            (.singleton ⟨canon_g5, by decide⟩)))))

/-- Disproof of Conjecture 00000001291 under Convention A (at `n = 4`, height is at least `5 > 4`). -/
theorem refutation_conventionA_at_4 :
    ¬ PosetHeightAtMost (CanonicalMisereLayer 4) StrictOptionSubset 4 :=
  not_posetHeightAtMost_of_chain chainA_witness_height_5 (by omega)

theorem refutation_conventionA_universal :
    ¬ (∀ n : Nat, PosetHeightAtMost (CanonicalMisereLayer n) StrictOptionSubset n) :=
  fun hall => refutation_conventionA_at_4 (hall 4)

theorem refutation_conventionA_card_universal :
    ¬ (∀ n : Nat, PosetCardHeightAtMost (CanonicalMisereLayer n) StrictOptionSubset n) :=
  fun hall => not_posetCardHeightAtMost_of_chain chainA_witness_height_5 (by omega) (hall 4)

/-- Small-layer non-vacuity witness (`n = 3` attains chain height `3 ≤ 3`). -/
theorem small_layer_3_attains_height_3 :
    HasChainOfHeight (CanonicalMisereLayer 3) StrictOptionSubset 3 := by
  refine ⟨[g0, g1, g2, g3], rfl, ?_⟩
  exact .cons ⟨canon_g0, by decide⟩ (strictOptionSubset_of_bools rfl rfl)
    (.cons ⟨canon_g1, by decide⟩ (strictOptionSubset_of_bools rfl rfl)
      (.cons ⟨canon_g2, by decide⟩ (strictOptionSubset_of_bools rfl rfl)
        (.singleton ⟨canon_g3, by decide⟩)))

/-!
### Convention B Refutation (Layer `n = 5`, Conway Normalization Partial Order `NormReducesLt`):
At misère layer height `n = 5`, we consider games `g` of layer height `≤ 5` whose options are
already normalized, pairwise misère-inequivalent canonical Grundy values in `M₄`.
The 11 games `H₀ ≺_norm H₁ ≺_norm ⋯ ≺_norm H₁₀` (all semantically misère-equivalent to `0`)
form a strict normalization chain of height `10 > 5` (11 elements).
-/

/-- Domain of layer-`n` games built over distinct canonical misère Grundy values. -/
def PreCanonicalMisereLayer (n : Nat) (g : IGame) : Prop :=
  g.layerHeight ≤ n ∧ PairwiseInequiv g.options ∧ (∀ c ∈ g.options, IsCanonicalMisere c)

def uList10 : List IGame := [u1, u2, u3, u4, u5, u6, u7, u8, u9, u10]

theorem uList10_pairwiseInequiv : PairwiseInequiv uList10 :=
  pairwiseInequiv_of_pairwiseSeparated rfl

theorem uList10_all_canon : ∀ c ∈ uList10, IsCanonicalMisere c := by
  intro c hc
  rcases List.mem_cons.mp hc with rfl | hc
  · exact canon_g1
  rcases List.mem_cons.mp hc with rfl | hc
  · exact canon_g2
  rcases List.mem_cons.mp hc with rfl | hc
  · exact canon_g3
  rcases List.mem_cons.mp hc with rfl | hc
  · exact canon_u4
  rcases List.mem_cons.mp hc with rfl | hc
  · exact canon_u5
  rcases List.mem_cons.mp hc with rfl | hc
  · exact canon_u6
  rcases List.mem_cons.mp hc with rfl | hc
  · exact canon_u7
  rcases List.mem_cons.mp hc with rfl | hc
  · exact canon_g4
  rcases List.mem_cons.mp hc with rfl | hc
  · exact canon_u9
  rcases List.mem_cons.mp hc with rfl | hc
  · exact canon_g5
  nomatch hc

theorem uList10_zero_mem : ∀ c ∈ uList10, g0 ∈ c.options := by
  intro c hc
  rcases List.mem_cons.mp hc with rfl | hc <;> first | exact .head _ | skip
  rcases List.mem_cons.mp hc with rfl | hc <;> first | exact .head _ | skip
  rcases List.mem_cons.mp hc with rfl | hc <;> first | exact .head _ | skip
  rcases List.mem_cons.mp hc with rfl | hc <;> first | exact .head _ | skip
  rcases List.mem_cons.mp hc with rfl | hc <;> first | exact .head _ | skip
  rcases List.mem_cons.mp hc with rfl | hc <;> first | exact .head _ | skip
  rcases List.mem_cons.mp hc with rfl | hc <;> first | exact .head _ | skip
  rcases List.mem_cons.mp hc with rfl | hc <;> first | exact .head _ | skip
  rcases List.mem_cons.mp hc with rfl | hc <;> first | exact .head _ | skip
  rcases List.mem_cons.mp hc with rfl | hc
  · exact .head _
  · nomatch hc

theorem pairwiseInequiv_take :
    ∀ (k : Nat) {xs : List IGame}, PairwiseInequiv xs → PairwiseInequiv (xs.take k)
  | 0, _, _ => .nil
  | _ + 1, [], _ => .nil
  | k + 1, _ :: _, .cons hhd htl =>
    .cons (fun y hy => hhd y (List.mem_of_mem_take hy)) (pairwiseInequiv_take k htl)

/-- Prefix games `H_k = mk (uList10.take k)` for `0 ≤ k ≤ 10`. -/
def HGame (k : Nat) : IGame := .mk (uList10.take k)

theorem HGame_mem_layer5 (k : Nat) : PreCanonicalMisereLayer 5 (HGame k) := by
  refine ⟨?_, pairwiseInequiv_take k uList10_pairwiseInequiv,
    fun c hc => uList10_all_canon c (List.mem_of_mem_take hc)⟩
  apply layerHeight_mk_le
  intro c hc
  have hmem : c ∈ uList10 := List.mem_of_mem_take hc
  rcases List.mem_cons.mp hmem with rfl | hmem; · decide
  rcases List.mem_cons.mp hmem with rfl | hmem; · decide
  rcases List.mem_cons.mp hmem with rfl | hmem; · decide
  rcases List.mem_cons.mp hmem with rfl | hmem; · decide
  rcases List.mem_cons.mp hmem with rfl | hmem; · decide
  rcases List.mem_cons.mp hmem with rfl | hmem; · decide
  rcases List.mem_cons.mp hmem with rfl | hmem; · decide
  rcases List.mem_cons.mp hmem with rfl | hmem; · decide
  rcases List.mem_cons.mp hmem with rfl | hmem; · decide
  rcases List.mem_cons.mp hmem with rfl | hmem; · decide
  nomatch hmem

theorem HGame_equiv_g0 : ∀ (k : Nat), MisereEquiv (HGame k) g0
  | 0 => MisereEquiv.refl g0
  | _ + 1 =>
    misereEquiv_zero_of_star_and_zero_mem
      (.head _)
      (fun u hu => uList10_zero_mem u (List.mem_of_mem_take hu))

theorem HGame_step_norm (k : Nat)
    (h1 : decideOptionSubset (HGame k) (HGame (k + 1)) = true)
    (h2 : decideOptionSubset (HGame (k + 1)) (HGame k) = false) :
    NormReducesLt (HGame k) (HGame (k + 1)) :=
  ⟨strictOptionSubset_of_bools h1 h2,
   MisereEquiv.trans (HGame_equiv_g0 k) (MisereEquiv.symm (HGame_equiv_g0 (k + 1)))⟩

theorem chainB_witness_height_10 :
    HasChainOfHeight (PreCanonicalMisereLayer 5) NormReducesLt 10 := by
  refine ⟨[HGame 0, HGame 1, HGame 2, HGame 3, HGame 4, HGame 5,
           HGame 6, HGame 7, HGame 8, HGame 9, HGame 10], rfl, ?_⟩
  exact .cons (HGame_mem_layer5 0) (HGame_step_norm 0 rfl rfl)
    (.cons (HGame_mem_layer5 1) (HGame_step_norm 1 rfl rfl)
      (.cons (HGame_mem_layer5 2) (HGame_step_norm 2 rfl rfl)
        (.cons (HGame_mem_layer5 3) (HGame_step_norm 3 rfl rfl)
          (.cons (HGame_mem_layer5 4) (HGame_step_norm 4 rfl rfl)
            (.cons (HGame_mem_layer5 5) (HGame_step_norm 5 rfl rfl)
              (.cons (HGame_mem_layer5 6) (HGame_step_norm 6 rfl rfl)
                (.cons (HGame_mem_layer5 7) (HGame_step_norm 7 rfl rfl)
                  (.cons (HGame_mem_layer5 8) (HGame_step_norm 8 rfl rfl)
                    (.cons (HGame_mem_layer5 9) (HGame_step_norm 9 rfl rfl)
                      (.singleton (HGame_mem_layer5 10)))))))))))

/-- Disproof of Conjecture 00000001291 under Convention B (at `n = 5`, normalization height is `≥ 10 > 5`). -/
theorem refutation_conventionB_at_5 :
    ¬ PosetHeightAtMost (PreCanonicalMisereLayer 5) NormReducesLt 5 :=
  not_posetHeightAtMost_of_chain chainB_witness_height_10 (by omega)

theorem refutation_conventionB_universal :
    ¬ (∀ n : Nat, PosetHeightAtMost (PreCanonicalMisereLayer n) NormReducesLt n) :=
  fun hall => refutation_conventionB_at_5 (hall 5)

theorem refutation_conventionB_card_universal :
    ¬ (∀ n : Nat, PosetCardHeightAtMost (PreCanonicalMisereLayer n) NormReducesLt n) :=
  fun hall => not_posetCardHeightAtMost_of_chain chainB_witness_height_10 (by omega) (hall 5)

end Conjecture00000001291
