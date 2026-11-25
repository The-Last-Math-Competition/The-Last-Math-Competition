import Conjecture00000001291.Basic
import Conjecture00000001291.Poset

namespace Conjecture00000001291
open IGame

/-!
### Positive Contrast Regimes:
1. **Normal-play Sprague–Grundy values**: bounded by `layerHeight g ≤ n`, so poset height is `≤ n`.
2. **Conway's scalar misère Grundy function** `𝒢⁻(G)` (`𝒢⁻(0) = 1`, `mex` on non-empty games):
   satisfies `𝒢⁻(G) = 0 ↔ o⁻(G) = 𝒫`, and its attained integer poset at layer height `≤ n`
   has height `≤ n` for every `n : Nat` (`{1}` of height `0` at `n = 0`, and `⊆ {0..n}` for `n ≥ 1`).
3. **Global syntactic outcome preorder** (`∀ X, o⁻(H+X) = 𝒫 → o⁻(G+X) = 𝒫` over *all* games `X`):
   collapses to `MisereEquiv` (an antichain on equivalence classes, height `0 ≤ n`).
-/

/-- Minimum excluded natural number (`mex`) of a finite list of `Nat`s. -/
def mexAux (vals : List Nat) (cur fuel : Nat) : Nat :=
  match fuel with
  | 0 => cur
  | fuel' + 1 =>
    if vals.contains cur then mexAux vals (cur + 1) fuel' else cur

def mex (vals : List Nat) : Nat :=
  mexAux vals 0 vals.length

theorem mem_of_lt_mexAux {vals : List Nat} {cur fuel j : Nat}
    (hlo : cur ≤ j) (hhi : j < mexAux vals cur fuel) : j ∈ vals := by
  induction fuel generalizing cur with
  | zero =>
    unfold mexAux at hhi
    omega
  | succ _ ih =>
    unfold mexAux at hhi
    split at hhi
    · next hcont =>
      by_cases heq : j = cur
      · subst heq
        exact List.contains_iff_mem.mp hcont
      · exact ih (by omega) hhi
    · omega

/-- Normal-play Grundy value `𝒢⁺(G) = mex {𝒢⁺(G') : G' ∈ G}`. -/
def grundyNormal : IGame → Nat
  | .mk gs => mex (grundyNormalList gs)
where
  grundyNormalList : List IGame → List Nat
    | [] => []
    | g :: gs => grundyNormal g :: grundyNormalList gs

theorem mem_grundyNormalList_iff {v : Nat} {gs : List IGame} :
    v ∈ grundyNormal.grundyNormalList gs ↔ ∃ g ∈ gs, grundyNormal g = v := by
  induction gs with
  | nil =>
    simp [grundyNormal.grundyNormalList]
  | cons g gs ih =>
    unfold grundyNormal.grundyNormalList
    rw [List.mem_cons, ih]
    constructor
    · rintro (rfl | ⟨x, hx, rfl⟩)
      · exact ⟨g, .head _, rfl⟩
      · exact ⟨x, .tail _ hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      cases List.mem_cons.mp hx with
      | inl heq => subst heq; exact .inl rfl
      | inr hm => exact .inr ⟨x, hm, rfl⟩

/-- Normal-play Grundy value never exceeds game layer height: `𝒢⁺(G) ≤ layerHeight(G)`. -/
theorem grundyNormal_le_layerHeight (g : IGame) : grundyNormal g ≤ g.layerHeight := by
  refine @ind (fun y => grundyNormal y ≤ y.layerHeight) (fun gs ih => ?_) g
  cases gs with
  | nil => decide
  | cons a as =>
    exact Classical.byContradiction fun hgt => by
      have hge : (IGame.mk (a :: as)).layerHeight <
                 mex (grundyNormal.grundyNormalList (a :: as)) := by
        show (IGame.mk (a :: as)).layerHeight < grundyNormal (.mk (a :: as))
        omega
      have hmem : (IGame.mk (a :: as)).layerHeight ∈ grundyNormal.grundyNormalList (a :: as) :=
        mem_of_lt_mexAux (Nat.zero_le _) hge
      obtain ⟨c, hc, hval⟩ := mem_grundyNormalList_iff.mp hmem
      have hlt : c.layerHeight < (IGame.mk (a :: as)).layerHeight := layerHeight_lt_of_mem hc
      have hle : grundyNormal c ≤ c.layerHeight := ih c hc
      omega

/-- Attained normal-play Grundy values at layer height `≤ n`. -/
def AttainedNormalGrundy (n : Nat) (v : Nat) : Prop :=
  ∃ g : IGame, g.layerHeight ≤ n ∧ grundyNormal g = v

theorem normal_grundy_posetHeight_le (n : Nat) :
    PosetHeightAtMost (AttainedNormalGrundy n) (· < ·) n := by
  apply nat_posetHeightAtMost
  rintro v ⟨g, hg, rfl⟩
  exact Nat.le_trans (grundyNormal_le_layerHeight g) hg

/-! ### Conway's Scalar Misère Grundy Function `𝒢⁻(G)` -/

/-- Conway's scalar misère Grundy number (`𝒢⁻(0) = 1`, and `mex` on non-empty option lists). -/
def grundyMisere : IGame → Nat
  | .mk [] => 1
  | .mk (g :: gs) => mex (grundyMisere g :: grundyMisereList gs)
where
  grundyMisereList : List IGame → List Nat
    | [] => []
    | g :: gs => grundyMisere g :: grundyMisereList gs

theorem mem_grundyMisereList_iff {v : Nat} {gs : List IGame} :
    v ∈ grundyMisere.grundyMisereList gs ↔ ∃ g ∈ gs, grundyMisere g = v := by
  induction gs with
  | nil => simp [grundyMisere.grundyMisereList]
  | cons g gs ih =>
    unfold grundyMisere.grundyMisereList
    rw [List.mem_cons, ih]
    constructor
    · rintro (rfl | ⟨x, hx, rfl⟩)
      · exact ⟨g, .head _, rfl⟩
      · exact ⟨x, .tail _ hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      cases List.mem_cons.mp hx with
      | inl heq => subst heq; exact .inl rfl
      | inr hm => exact .inr ⟨x, hm, rfl⟩

theorem mexAux_ge_cur (vals : List Nat) : ∀ (c f : Nat), c ≤ mexAux vals c f
  | c, 0 => by simp [mexAux]
  | c, f + 1 => by
    unfold mexAux
    split
    · have := mexAux_ge_cur vals (c + 1) f; omega
    · omega

theorem mex_eq_zero_iff {vals : List Nat} : mex vals = 0 ↔ 0 ∉ vals := by
  cases vals with
  | nil => simp [mex, mexAux]
  | cons v vs =>
    unfold mex mexAux
    cases h0 : (v :: vs).contains 0 with
    | false =>
      constructor
      · intro _ hm
        have hc : (v :: vs).contains 0 = true := List.contains_iff_mem.mpr hm
        rw [h0] at hc
        nomatch hc
      · intro _
        rfl
    | true =>
      change (if true = true then mexAux (v :: vs) 1 vs.length else 0) = 0 ↔ 0 ∉ v :: vs
      simp only [↓reduceIte]
      have hge1 : 1 ≤ mexAux (v :: vs) 1 vs.length := mexAux_ge_cur (v :: vs) 1 vs.length
      have hmem0 : 0 ∈ v :: vs := List.contains_iff_mem.mp h0
      exact ⟨fun hz => by omega, fun hnm => False.elim (hnm hmem0)⟩

/-- Fundamental characterization of Conway's scalar misère Grundy number:
    `o⁻(G) = 𝒫` (`misereWin G = false`) if and only if `𝒢⁻(G) = 0`. -/
theorem misereWin_false_iff_grundyMisere_zero (g : IGame) :
    misereWin g = false ↔ grundyMisere g = 0 := by
  refine @ind (fun y => misereWin y = false ↔ grundyMisere y = 0) (fun gs ih => ?_) g
  cases gs with
  | nil => simp [misereWin, grundyMisere]
  | cons a as =>
    rw [misereWin_mk_ne_nil (by simp)]
    show ((a :: as).any (fun c => !misereWin c) = false) ↔
         mex (grundyMisere.grundyMisereList (a :: as)) = 0
    rw [mex_eq_zero_iff, mem_grundyMisereList_iff]
    constructor
    · intro hany ⟨c, hc, hz⟩
      have hfalse : misereWin c = false := (ih c hc).mpr hz
      have htrue : (a :: as).any (fun x => !misereWin x) = true :=
        List.any_eq_true.mpr ⟨c, hc, by simp [hfalse]⟩
      rw [hany] at htrue
      nomatch htrue
    · intro hno
      cases hany : (a :: as).any (fun x => !misereWin x) with
      | false => rfl
      | true =>
        obtain ⟨c, hc, hnc⟩ := List.any_eq_true.mp hany
        have hfc : misereWin c = false := by
          cases hm : misereWin c <;> simp [hm] at hnc ⊢
        exact False.elim (hno ⟨c, hc, (ih c hc).mp hfc⟩)

/-- For every `G`, `𝒢⁻(G) ≤ max 1 (layerHeight G)` (with `𝒢⁻(0) = 1`). -/
theorem grundyMisere_le_max_one_layerHeight (g : IGame) :
    grundyMisere g ≤ max 1 g.layerHeight := by
  refine @ind (fun y => grundyMisere y ≤ max 1 y.layerHeight) (fun gs ih => ?_) g
  cases gs with
  | nil => decide
  | cons a as =>
    have hpos : 1 ≤ (IGame.mk (a :: as)).layerHeight := by
      rw [layerHeight_mk_cons]; omega
    by_cases h1 : (IGame.mk (a :: as)).layerHeight = 1
    · have hz : grundyMisere (.mk (a :: as)) = 0 := by
        show mex (grundyMisere.grundyMisereList (a :: as)) = 0
        rw [mex_eq_zero_iff, mem_grundyMisereList_iff]
        rintro ⟨c, hc, hc0⟩
        have hclt : c.layerHeight < (IGame.mk (a :: as)).layerHeight := layerHeight_lt_of_mem hc
        cases c with
        | mk copts =>
          cases copts with
          | nil => simp [grundyMisere] at hc0
          | cons c0 cs =>
            rw [layerHeight_mk_cons] at hclt
            omega
      omega
    · exact Classical.byContradiction fun hgt => by
        have hlt : (IGame.mk (a :: as)).layerHeight <
                   mex (grundyMisere.grundyMisereList (a :: as)) := by
          show (IGame.mk (a :: as)).layerHeight < grundyMisere (.mk (a :: as))
          omega
        have hmem := mem_of_lt_mexAux (Nat.zero_le _) hlt
        obtain ⟨c, hc, hval⟩ := mem_grundyMisereList_iff.mp hmem
        have hclt : c.layerHeight < (IGame.mk (a :: as)).layerHeight := layerHeight_lt_of_mem hc
        have hcle : grundyMisere c ≤ max 1 c.layerHeight := ih c hc
        omega

/-- Attained scalar misère Grundy numbers at layer height `≤ n`. -/
def AttainedScalarMisereGrundy (n : Nat) (v : Nat) : Prop :=
  ∃ g : IGame, g.layerHeight ≤ n ∧ grundyMisere g = v

/-- Contrast Theorem: The poset of attained scalar misère Grundy values `(𝒢⁻, <)` DOES have
    height `≤ n` for ALL `n : Nat` (including `n = 0`, where `{1}` is a singleton of height `0`). -/
theorem scalar_misere_grundy_posetHeight_le :
    ∀ (n : Nat), PosetHeightAtMost (AttainedScalarMisereGrundy n) (· < ·) n
  | 0 => by
    intro k ⟨xs, hlen, hsc⟩
    have h1 : ∀ v, AttainedScalarMisereGrundy 0 v → v = 1 := by
      rintro v ⟨g, hg, rfl⟩
      cases g with
      | mk gs =>
        cases gs with
        | nil => rfl
        | cons a as =>
          rw [layerHeight_mk_cons] at hg
          omega
    cases xs with
    | nil => simp at hlen
    | cons x rest =>
      cases rest with
      | nil => simp at hlen; omega
      | cons y _ =>
        cases hsc with
        | cons hx hxy htail =>
          have hy : AttainedScalarMisereGrundy 0 y := by
            cases htail with
            | singleton hy0 => exact hy0
            | cons hy0 _ _ => exact hy0
          rw [h1 x hx, h1 y hy] at hxy
          omega
  | n + 1 => by
    apply nat_posetHeightAtMost
    rintro v ⟨g, hg, rfl⟩
    have hb := grundyMisere_le_max_one_layerHeight g
    omega

/-!
### Global Syntactic Outcome Order Antichain Theorem:
Over the full universe of impartial games, `MisereOutcomeLe g h` collapses to `MisereEquiv g h`.
-/

/-- Global misère syntactic preorder: every P-context for `h` is also a P-context for `g`. -/
def MisereOutcomeLe (g h : IGame) : Prop :=
  ∀ x : IGame, misereWin (add h x) = false → misereWin (add g x) = false

def MisereOutcomeLt (g h : IGame) : Prop :=
  MisereOutcomeLe g h ∧ ¬ MisereOutcomeLe h g

/-- Constructive P-partner `S` for any game `a`, satisfying `o⁻(a + S) = 𝒫`. -/
def makePPartner : IGame → IGame
  | .mk [] => g1
  | .mk (a :: as) =>
    if misereWin (.mk (a :: as)) then .mk (makePPartner a :: makePPartnerList as) else g0
where
  makePPartnerList : List IGame → List IGame
    | [] => []
    | a :: as => makePPartner a :: makePPartnerList as

theorem makePPartnerList_eq_map (gs : List IGame) :
    makePPartner.makePPartnerList gs = gs.map makePPartner := by
  induction gs with
  | nil => rfl
  | cons g gs ih => simp [makePPartner.makePPartnerList, ih]

theorem misereWin_add_makePPartner (a : IGame) :
    misereWin (add a (makePPartner a)) = false := by
  refine @ind (fun y => misereWin (add y (makePPartner y)) = false) (fun gs ih => ?_) a
  cases gs with
  | nil => rfl
  | cons a0 as =>
    unfold makePPartner
    cases hw : misereWin (.mk (a0 :: as)) with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      show misereWin (add (.mk (a0 :: as)) (.mk [])) = false
      rw [add_mk_nil_right]
      exact hw
    | true =>
      simp only [↓reduceIte, makePPartnerList_eq_map]
      let partnerOpts : List IGame := makePPartner a0 :: as.map makePPartner
      have hp_eq : partnerOpts = (a0 :: as).map makePPartner := rfl
      rw [misereWin_add_eq, misereWinAdd_unfold (.inl (by simp))]
      apply Bool.or_eq_false_iff.mpr
      constructor
      · cases hl : (a0 :: as).any (fun c => !misereWinAdd c (.mk partnerOpts)) with
        | false => rfl
        | true =>
          obtain ⟨c, hc, hnc⟩ := List.any_eq_true.mp hl
          have hmemP : makePPartner c ∈ partnerOpts := by
            rw [hp_eq]
            exact List.mem_map.mpr ⟨c, hc, rfl⟩
          have hcWin : misereWinAdd c (.mk partnerOpts) = true := by
            cases c with
            | mk copts =>
              rw [misereWinAdd_unfold (.inr (by simp [partnerOpts]))]
              have hrTrue : (partnerOpts.any (fun p => !misereWinAdd (.mk copts) p)) = true := by
                apply List.any_eq_true.mpr
                refine ⟨makePPartner (.mk copts), hmemP, ?_⟩
                have hih : misereWin (add (.mk copts) (makePPartner (.mk copts))) = false :=
                  ih (.mk copts) hc
                rw [misereWin_add_eq] at hih
                simp [hih]
              rw [hrTrue, Bool.or_true]
          rw [hcWin] at hnc
          nomatch hnc
      · cases hr : partnerOpts.any (fun p => !misereWinAdd (.mk (a0 :: as)) p) with
        | false => rfl
        | true =>
          obtain ⟨p, hp, hnp⟩ := List.any_eq_true.mp hr
          rw [hp_eq] at hp
          obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hp
          have hpWin : misereWinAdd (.mk (a0 :: as)) (makePPartner c) = true := by
            cases hmP : makePPartner c with
            | mk popts =>
              rw [misereWinAdd_unfold (.inl (by simp))]
              have hlTrue : ((a0 :: as).any (fun d => !misereWinAdd d (.mk popts))) = true := by
                apply List.any_eq_true.mpr
                refine ⟨c, hc, ?_⟩
                have hih : misereWin (add c (makePPartner c)) = false := ih c hc
                rw [hmP, misereWin_add_eq] at hih
                simp [hih]
              rw [hlTrue]
              rfl
          rw [hpWin] at hnp
          nomatch hnp

/-- Global Syntactic Antichain Theorem:
    `MisereOutcomeLe g h` holds if and only if `MisereEquiv g h` (`G ≡⁻ H`). -/
theorem misereOutcomeLe_iff_misereEquiv (g h : IGame) :
    MisereOutcomeLe g h ↔ MisereEquiv g h := by
  constructor
  · intro hle x
    cases hhx : misereWin (add h x) with
    | false => exact hle x hhx
    | true =>
      cases hgx : misereWin (add g x) with
      | true => rfl
      | false =>
        cases h with
        | mk hs =>
          let sOpts : List IGame := x :: hs.map makePPartner
          let S : IGame := .mk sOpts
          have hhS : misereWin (add (.mk hs) S) = false := by
            rw [misereWin_add_eq, misereWinAdd_unfold (.inr (by simp [S, sOpts]))]
            apply Bool.or_eq_false_iff.mpr
            constructor
            · cases hl : hs.any (fun c => !misereWinAdd c S) with
              | false => rfl
              | true =>
                obtain ⟨c, hc, hnc⟩ := List.any_eq_true.mp hl
                have hmP : makePPartner c ∈ sOpts := .tail _ (List.mem_map.mpr ⟨c, hc, rfl⟩)
                have hcWin : misereWinAdd c S = true := by
                  cases c with
                  | mk copts =>
                    rw [misereWinAdd_unfold (.inr (by simp [S, sOpts]))]
                    have hrT : (sOpts.any (fun p => !misereWinAdd (.mk copts) p)) = true := by
                      apply List.any_eq_true.mpr
                      refine ⟨makePPartner (.mk copts), hmP, ?_⟩
                      have hp := misereWin_add_makePPartner (.mk copts)
                      rw [misereWin_add_eq] at hp
                      simp [hp]
                    rw [hrT, Bool.or_true]
                rw [hcWin] at hnc
                nomatch hnc
            · cases hr : sOpts.any (fun p => !misereWinAdd (.mk hs) p) with
              | false => rfl
              | true =>
                obtain ⟨p, hp, hnp⟩ := List.any_eq_true.mp hr
                cases List.mem_cons.mp hp with
                | inl heq =>
                  subst heq
                  rw [misereWin_add_eq] at hhx
                  rw [hhx] at hnp
                  nomatch hnp
                | inr hm =>
                  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hm
                  cases hs with
                  | nil => nomatch hc
                  | cons h0 hs' =>
                    have hpWin : misereWinAdd (.mk (h0 :: hs')) (makePPartner c) = true := by
                      cases hmP : makePPartner c with
                      | mk popts =>
                        rw [misereWinAdd_unfold (.inl (by simp))]
                        have hlT : ((h0 :: hs').any (fun d => !misereWinAdd d (.mk popts))) = true := by
                          apply List.any_eq_true.mpr
                          refine ⟨c, hc, ?_⟩
                          have hp0 := misereWin_add_makePPartner c
                          rw [hmP, misereWin_add_eq] at hp0
                          simp [hp0]
                        rw [hlT]
                        rfl
                    rw [hpWin] at hnp
                    nomatch hnp
          have hgS_false : misereWin (add g S) = false := hle S hhS
          have hgS_true : misereWin (add g S) = true := by
            cases g with
            | mk gs =>
              rw [misereWin_add_eq, misereWinAdd_unfold (.inr (by simp [S, sOpts]))]
              have hrT : (sOpts.any (fun p => !misereWinAdd (.mk gs) p)) = true := by
                apply List.any_eq_true.mpr
                refine ⟨x, .head _, ?_⟩
                rw [misereWin_add_eq] at hgx
                simp [hgx]
              rw [hrT, Bool.or_true]
          rw [hgS_true] at hgS_false
          nomatch hgS_false
  · intro heq x hhx
    rw [heq x]
    exact hhx

theorem not_misereOutcomeLt (g h : IGame) : ¬ MisereOutcomeLt g h := by
  rintro ⟨hle, hnot⟩
  have heq := (misereOutcomeLe_iff_misereEquiv g h).mp hle
  exact hnot ((misereOutcomeLe_iff_misereEquiv h g).mpr (MisereEquiv.symm heq))

/-- Corollary: Under the global syntactic outcome partial order, every subset of games is an
    antichain of height `0 ≤ n` for all `n`. -/
theorem global_misereOutcome_posetHeight_le (P : IGame → Prop) (n : Nat) :
    PosetHeightAtMost P MisereOutcomeLt n := by
  intro k ⟨xs, hlen, hsc⟩
  cases xs with
  | nil => simp at hlen
  | cons _ rest =>
    cases rest with
    | nil => simp at hlen; omega
    | cons y _ =>
      cases hsc with
      | cons _ hxy _ => exact False.elim (not_misereOutcomeLt _ y hxy)

end Conjecture00000001291
