namespace Conjecture00000001291

/-- Finite impartial combinatorial game trees (hereditarily finite option lists). -/
inductive IGame where
  | mk : List IGame → IGame

namespace IGame

/-- Direct option list of an impartial game. -/
def options : IGame → List IGame
  | .mk gs => gs

/-- Strong structural induction principle on `IGame` via option membership. -/
theorem ind {P : IGame → Prop}
    (step : ∀ gs : List IGame, (∀ g ∈ gs, P g) → P (.mk gs)) : ∀ g : IGame, P g
  | .mk gs => step gs (indList gs)
where
  indList : ∀ (gs : List IGame) (g : IGame), g ∈ gs → P g
    | [], _, h => nomatch h
    | a :: as, g, h => by
      cases List.mem_cons.mp h with
      | inl heq => exact heq ▸ ind step a
      | inr hmem => exact indList as g hmem

/-- Structural Boolean equality on game trees. -/
def beq : IGame → IGame → Bool
  | .mk gs, .mk hs => beqList gs hs
where
  beqList : List IGame → List IGame → Bool
    | [], [] => true
    | g :: gs, h :: hs => beq g h && beqList gs hs
    | _, _ => false

theorem beq_refl : ∀ (g : IGame), beq g g = true
  | .mk gs => beqList_refl gs
where
  beqList_refl : ∀ (gs : List IGame), beq.beqList gs gs = true
    | [] => rfl
    | g :: gs => by simp [beq.beqList, beq_refl g, beqList_refl gs]

theorem eq_of_beq : ∀ {g h : IGame}, beq g h = true → g = h
  | .mk gs, .mk hs, h => congrArg IGame.mk (eq_of_beqList h)
where
  eq_of_beqList : ∀ {gs hs : List IGame}, beq.beqList gs hs = true → gs = hs
    | [], [], _ => rfl
    | _ :: _, [], h => nomatch h
    | [], _ :: _, h => nomatch h
    | _ :: _, _ :: _, h => by
      simp [beq.beqList] at h
      rw [eq_of_beq h.1, eq_of_beqList h.2]

theorem beq_iff_eq (g h : IGame) : beq g h = true ↔ g = h :=
  ⟨eq_of_beq, fun e => e ▸ beq_refl g⟩

/-- Layer height (birthday / tree height) of an impartial game:
    `layerHeight (mk []) = 0`, and `1 + max_{g ∈ gs} layerHeight g` for `gs ≠ []`. -/
def layerHeight : IGame → Nat
  | .mk [] => 0
  | .mk (g :: gs) => 1 + Nat.max (layerHeight g) (layerHeightList gs)
where
  layerHeightList : List IGame → Nat
    | [] => 0
    | g :: gs => Nat.max (layerHeight g) (layerHeightList gs)

theorem layerHeight_mk_cons (g : IGame) (gs : List IGame) :
    (IGame.mk (g :: gs)).layerHeight = 1 + layerHeight.layerHeightList (g :: gs) := rfl

theorem le_layerHeightList_of_mem {g : IGame} {gs : List IGame} (h : g ∈ gs) :
    g.layerHeight ≤ layerHeight.layerHeightList gs := by
  induction gs with
  | nil => nomatch h
  | cons a as ih =>
    unfold layerHeight.layerHeightList
    cases List.mem_cons.mp h with
    | inl heq =>
      subst heq
      exact Nat.le_max_left _ _
    | inr hmem =>
      exact Nat.le_trans (ih hmem) (Nat.le_max_right _ _)

theorem layerHeight_lt_of_mem {g : IGame} {gs : List IGame} (h : g ∈ gs) :
    g.layerHeight < (IGame.mk gs).layerHeight := by
  cases gs with
  | nil => nomatch h
  | cons a as =>
    rw [layerHeight_mk_cons]
    have := le_layerHeightList_of_mem h
    omega

theorem layerHeightList_le {gs : List IGame} {n : Nat}
    (h : ∀ g ∈ gs, g.layerHeight ≤ n) : layerHeight.layerHeightList gs ≤ n := by
  induction gs with
  | nil => exact Nat.zero_le n
  | cons a as ih =>
    unfold layerHeight.layerHeightList
    exact Nat.max_le.mpr ⟨h a (.head _), ih (fun x hx => h x (.tail _ hx))⟩

theorem layerHeight_mk_le {gs : List IGame} {n : Nat}
    (h : ∀ g ∈ gs, g.layerHeight < n) : (IGame.mk gs).layerHeight ≤ n := by
  cases gs with
  | nil => exact Nat.zero_le n
  | cons a as =>
    cases n with
    | zero => exact False.elim (Nat.not_lt_zero _ (h a (.head _)))
    | succ m =>
      rw [layerHeight_mk_cons]
      have hm : layerHeight.layerHeightList (a :: as) ≤ m :=
        layerHeightList_le (fun g hg => Nat.le_of_lt_succ (h g hg))
      omega

/-- Right-recursion helper for structurally recursive disjunctive sum `add`. -/
def stepAddRight (leftMap : IGame → List IGame) : IGame → IGame
  | .mk hs => .mk (leftMap (.mk hs) ++ stepAddRightList leftMap hs)
where
  stepAddRightList (leftMap : IGame → List IGame) : List IGame → List IGame
    | [] => []
    | h' :: hs => stepAddRight leftMap h' :: stepAddRightList leftMap hs

/-- Purely structurally recursive disjunctive sum `G + H = {G' + H} ∪ {G + H'}`. -/
def add : IGame → IGame → IGame
  | .mk gs => stepAddRight (addLeft gs)
where
  addLeft : List IGame → IGame → List IGame
    | [], _ => []
    | g' :: gs, h => add g' h :: addLeft gs h

theorem addLeft_eq_map (gs : List IGame) (h : IGame) :
    add.addLeft gs h = gs.map (fun g' => add g' h) := by
  induction gs with
  | nil => rfl
  | cons g' gs ih => simp [add.addLeft, ih]

theorem stepAddRightList_eq_map (leftMap : IGame → List IGame) (hs : List IGame) :
    stepAddRight.stepAddRightList leftMap hs = hs.map (stepAddRight leftMap) := by
  induction hs with
  | nil => rfl
  | cons h' hs ih => simp [stepAddRight.stepAddRightList, ih]

theorem add_def (gs hs : List IGame) :
    add (.mk gs) (.mk hs) =
      .mk ((gs.map (fun g' => add g' (.mk hs))) ++ (hs.map (fun h' => add (.mk gs) h'))) := by
  show stepAddRight (add.addLeft gs) (.mk hs) = _
  unfold stepAddRight
  rw [addLeft_eq_map, stepAddRightList_eq_map]
  rfl

theorem add_mk_nil_left (h : IGame) : add (.mk []) h = h := by
  refine @ind (fun y => add (.mk []) y = y) (fun hs ih => ?_) h
  dsimp only
  rw [add_def]
  simp only [List.map_nil, List.nil_append]
  congr 1
  induction hs with
  | nil => rfl
  | cons x xs ihs =>
    simp only [List.map_cons]
    rw [ih x (.head _), ihs (fun y hy => ih y (.tail _ hy))]

theorem add_mk_nil_right (g : IGame) : add g (.mk []) = g := by
  refine @ind (fun y => add y (.mk []) = y) (fun gs ih => ?_) g
  dsimp only
  rw [add_def]
  simp only [List.map_nil, List.append_nil]
  congr 1
  induction gs with
  | nil => rfl
  | cons x xs ihs =>
    simp only [List.map_cons]
    rw [ih x (.head _), ihs (fun y hy => ih y (.tail _ hy))]

/-- Misère-play outcome (`true` = N-position / Next player wins;
    `false` = P-position / Previous player wins). -/
def misereWin : IGame → Bool
  | .mk [] => true
  | .mk (g :: gs) => (!misereWin g) || misereWinAux gs
where
  misereWinAux : List IGame → Bool
    | [] => false
    | g :: gs => (!misereWin g) || misereWinAux gs

theorem misereWinAux_eq_any (gs : List IGame) :
    misereWin.misereWinAux gs = gs.any (fun g => !misereWin g) := by
  induction gs with
  | nil => rfl
  | cons g gs ih => simp [misereWin.misereWinAux, ih]

theorem misereWin_mk_nil : misereWin (.mk []) = true := rfl

theorem misereWin_mk_ne_nil {gs : List IGame} (hne : gs ≠ []) :
    misereWin (.mk gs) = gs.any (fun g => !misereWin g) := by
  cases gs with
  | nil => exact False.elim (hne rfl)
  | cons g gs => simp [misereWin, misereWinAux_eq_any]

/-- Right-recursion helper for structurally recursive `misereWinAdd`. -/
def stepWinRight (isNilG : Bool) (leftAny : IGame → Bool) : IGame → Bool
  | .mk [] => if isNilG then true else leftAny (.mk [])
  | .mk (h0 :: hs) =>
    leftAny (.mk (h0 :: hs)) ||
    ((!stepWinRight isNilG leftAny h0) || stepWinRightList isNilG leftAny hs)
where
  stepWinRightList (isNilG : Bool) (leftAny : IGame → Bool) : List IGame → Bool
    | [] => false
    | h' :: hs => (!stepWinRight isNilG leftAny h') || stepWinRightList isNilG leftAny hs

/-- Purely structurally recursive fast evaluator for `misereWin (add g h)`. -/
def misereWinAdd : IGame → IGame → Bool
  | .mk [] => stepWinRight true (fun _ => false)
  | .mk (g0 :: gs) => stepWinRight false (misereWinAddLeft (g0 :: gs))
where
  misereWinAddLeft : List IGame → IGame → Bool
    | [], _ => false
    | g' :: gs, h => (!misereWinAdd g' h) || misereWinAddLeft gs h

theorem misereWinAddLeft_eq_any (gs : List IGame) (h : IGame) :
    misereWinAdd.misereWinAddLeft gs h = gs.any (fun g' => !misereWinAdd g' h) := by
  induction gs with
  | nil => rfl
  | cons g' gs ih => simp [misereWinAdd.misereWinAddLeft, ih]

theorem stepWinRightList_eq_any (isNilG : Bool) (leftAny : IGame → Bool) (hs : List IGame) :
    stepWinRight.stepWinRightList isNilG leftAny hs =
      hs.any (fun h' => !stepWinRight isNilG leftAny h') := by
  induction hs with
  | nil => rfl
  | cons h' hs ih => simp [stepWinRight.stepWinRightList, ih]

theorem misereWinAdd_nil_nil : misereWinAdd (.mk []) (.mk []) = true := rfl

theorem misereWinAdd_unfold {gs hs : List IGame} (hne : gs ≠ [] ∨ hs ≠ []) :
    misereWinAdd (.mk gs) (.mk hs) =
      ((gs.any (fun g' => !misereWinAdd g' (.mk hs))) ||
       (hs.any (fun h' => !misereWinAdd (.mk gs) h'))) := by
  cases gs with
  | nil =>
    cases hs with
    | nil =>
      cases hne with
      | inl h => exact False.elim (h rfl)
      | inr h => exact False.elim (h rfl)
    | cons h0 hs' =>
      show stepWinRight true (fun _ => false) (.mk (h0 :: hs')) = _
      unfold stepWinRight
      rw [stepWinRightList_eq_any]
      simp [misereWinAdd]
  | cons g0 gs' =>
    cases hs with
    | nil =>
      show stepWinRight false (misereWinAdd.misereWinAddLeft (g0 :: gs')) (.mk []) = _
      unfold stepWinRight
      simp [misereWinAddLeft_eq_any]
    | cons h0 hs' =>
      show stepWinRight false (misereWinAdd.misereWinAddLeft (g0 :: gs')) (.mk (h0 :: hs')) = _
      unfold stepWinRight
      rw [misereWinAddLeft_eq_any, stepWinRightList_eq_any]
      simp [misereWinAdd]

theorem any_congr_mem {α : Type} {xs : List α} {p q : α → Bool}
    (h : ∀ x ∈ xs, p x = q x) : xs.any p = xs.any q := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.any_cons]
    rw [h x (.head _), ih (fun y hy => h y (.tail _ hy))]

/-- Exact agreement between `misereWin (add g h)` and `misereWinAdd g h`. -/
theorem misereWin_add_eq (g h : IGame) : misereWin (add g h) = misereWinAdd g h := by
  revert h
  refine @ind (fun x => ∀ y : IGame, misereWin (add x y) = misereWinAdd x y) (fun gs ihg => ?_) g
  intro h
  refine @ind (fun y => misereWin (add (.mk gs) y) = misereWinAdd (.mk gs) y) (fun hs ihh => ?_) h
  cases gs with
  | nil =>
    cases hs with
    | nil => rfl
    | cons h0 hs' =>
      rw [add_def, misereWin_mk_ne_nil (by simp), misereWinAdd_unfold (.inr (by simp))]
      simp only [List.map_nil, List.nil_append, List.any_nil, Bool.false_or, List.any_map]
      exact any_congr_mem (fun h' hh' => congrArg Bool.not (ihh h' hh'))
  | cons g0 gs' =>
    rw [add_def, misereWin_mk_ne_nil (by simp), misereWinAdd_unfold (.inl (by simp))]
    simp only [List.any_append, List.any_map, Function.comp_def]
    have hl : ((g0 :: gs').any (fun x => !misereWin (add x (.mk hs)))) =
              ((g0 :: gs').any (fun x => !misereWinAdd x (.mk hs))) :=
      any_congr_mem (fun x hx => congrArg Bool.not (ihg x hx (.mk hs)))
    have hr : (hs.any (fun y => !misereWin (add (.mk (g0 :: gs')) y))) =
              (hs.any (fun y => !misereWinAdd (.mk (g0 :: gs')) y)) :=
      any_congr_mem (fun y hy => congrArg Bool.not (ihh y hy))
    rw [hl, hr]

/-- Terminal game `0 = ∅` and Nim-heap `* = {0}`. -/
def g0 : IGame := .mk []
def g1 : IGame := .mk [g0]

/-- Semantic misère indistinguishability (`G ≡⁻ H`): identical misère outcome in every game context `X`. -/
def MisereEquiv (g h : IGame) : Prop :=
  ∀ x : IGame, misereWin (add g x) = misereWin (add h x)

theorem MisereEquiv.refl (g : IGame) : MisereEquiv g g :=
  fun _ => rfl

theorem MisereEquiv.symm {g h : IGame} (hgh : MisereEquiv g h) : MisereEquiv h g :=
  fun x => (hgh x).symm

theorem MisereEquiv.trans {a b c : IGame} (hab : MisereEquiv a b) (hbc : MisereEquiv b c) :
    MisereEquiv a c :=
  fun x => (hab x).trans (hbc x)

/-- Option-set inclusion `G ⊆ H` and strict option-set inclusion `G ⊂ H`. -/
def OptionSubset (g h : IGame) : Prop :=
  ∀ c ∈ g.options, c ∈ h.options

def StrictOptionSubset (g h : IGame) : Prop :=
  OptionSubset g h ∧ ¬ OptionSubset h g

theorem strictOptionSubset_irrefl (g : IGame) : ¬ StrictOptionSubset g g :=
  fun ⟨h1, h2⟩ => h2 h1

theorem strictOptionSubset_trans {a b c : IGame}
    (hab : StrictOptionSubset a b) (hbc : StrictOptionSubset b c) :
    StrictOptionSubset a c := by
  refine ⟨fun x hx => hbc.1 x (hab.1 x hx), ?_⟩
  intro hca
  exact hbc.2 (fun x hx => hab.1 x (hca x hx))

theorem any_eq_of_mem_iff {α : Type} {l1 l2 : List α} (p : α → Bool)
    (hm : ∀ z, z ∈ l1 ↔ z ∈ l2) : l1.any p = l2.any p := by
  cases h2 : l2.any p with
  | false =>
    cases h1 : l1.any p with
    | false => rfl
    | true =>
      obtain ⟨z, hz, hpz⟩ := List.any_eq_true.mp h1
      have hfalse : l2.any p = true := List.any_eq_true.mpr ⟨z, (hm z).mp hz, hpz⟩
      rw [h2] at hfalse
      nomatch hfalse
  | true =>
    obtain ⟨z, hz, hpz⟩ := List.any_eq_true.mp h2
    exact List.any_eq_true.mpr ⟨z, (hm z).mpr hz, hpz⟩

/-- Two option lists with identical membership sets yield semantically misère-equivalent games. -/
theorem misereEquiv_of_mem_iff {s1 s2 : List IGame}
    (hm : ∀ z, z ∈ s1 ↔ z ∈ s2) : MisereEquiv (.mk s1) (.mk s2) := by
  intro x
  rw [misereWin_add_eq, misereWin_add_eq]
  refine @ind (fun y => misereWinAdd (.mk s1) y = misereWinAdd (.mk s2) y) (fun xs ih => ?_) x
  cases s1 with
  | nil =>
    cases s2 with
    | nil => rfl
    | cons b _ => nomatch (hm b).mpr (.head _)
  | cons a as =>
    cases s2 with
    | nil => nomatch (hm a).mp (.head _)
    | cons b bs =>
      rw [misereWinAdd_unfold (.inl (by simp)), misereWinAdd_unfold (.inl (by simp))]
      have hl : ((a :: as).any (fun g' => !misereWinAdd g' (.mk xs))) =
                ((b :: bs).any (fun g' => !misereWinAdd g' (.mk xs))) :=
        any_eq_of_mem_iff (fun g' => !misereWinAdd g' (.mk xs)) hm
      have hr : (xs.any (fun x' => !misereWinAdd (.mk (a :: as)) x')) =
                (xs.any (fun x' => !misereWinAdd (.mk (b :: bs)) x')) :=
        any_congr_mem (fun x' hx' => congrArg Bool.not (ih x' hx'))
      rw [hl, hr]

/-- Pairwise semantic misère inequivalence of an option list (no duplicate Grundy-value options). -/
inductive PairwiseInequiv : List IGame → Prop where
  | nil : PairwiseInequiv []
  | cons {g : IGame} {gs : List IGame} :
      (∀ h ∈ gs, ¬ MisereEquiv g h) → PairwiseInequiv gs → PairwiseInequiv (g :: gs)

/-- Semantic subset-irreducibility: no proper subset of `g`'s options is misère-equivalent to `g`. -/
def SubsetIrreducible (g : IGame) : Prop :=
  ∀ s : List IGame, StrictOptionSubset (.mk s) g → ¬ MisereEquiv (.mk s) g

/-- Hereditary misère canonical form predicate:
    every option is in canonical form, options are pairwise misère-inequivalent,
    and no proper subset of options is misère-equivalent to the game. -/
inductive IsCanonicalMisere : IGame → Prop where
  | mk {gs : List IGame} :
      (∀ c ∈ gs, IsCanonicalMisere c) →
      PairwiseInequiv gs →
      SubsetIrreducible (.mk gs) →
      IsCanonicalMisere (.mk gs)

/-- Conway normalization strict partial order (`h ≺_norm g`):
    `h` is a strict option-subset of `g` that is semantically misère-equivalent to `g`
    (i.e. obtained by deleting redundant/reversible options). -/
def NormReducesLt (h g : IGame) : Prop :=
  StrictOptionSubset h g ∧ MisereEquiv h g

theorem normReducesLt_irrefl (g : IGame) : ¬ NormReducesLt g g :=
  fun ⟨hs, _⟩ => strictOptionSubset_irrefl g hs

theorem normReducesLt_trans {a b c : IGame}
    (hab : NormReducesLt a b) (hbc : NormReducesLt b c) : NormReducesLt a c :=
  ⟨strictOptionSubset_trans hab.1 hbc.1, MisereEquiv.trans hab.2 hbc.2⟩

/-- Universal Zero-Normalization Theorem:
    Any game `H` that has `* = {0}` as an option and whose options `u ∈ H` all contain `0 = ∅`
    as an option is semantically misère-equivalent to `0` (`∀ X, o⁻(H + X) = o⁻(0 + X)`). -/
theorem misereEquiv_zero_of_star_and_zero_mem {hs : List IGame}
    (hstar : g1 ∈ hs) (hzero : ∀ u ∈ hs, g0 ∈ u.options) :
    MisereEquiv (.mk hs) g0 := by
  intro x
  have h0x : add g0 x = x := add_mk_nil_left x
  rw [h0x, misereWin_add_eq]
  refine @ind (fun y => misereWinAdd (.mk hs) y = misereWin y) (fun xs ih => ?_) x
  cases hs with
  | nil => nomatch hstar
  | cons h0 hs' =>
    rw [misereWinAdd_unfold (.inl (by simp))]
    cases xs with
    | nil =>
      simp only [List.any_nil, Bool.or_false, misereWin_mk_nil]
      apply List.any_eq_true.mpr
      exact ⟨g1, hstar, rfl⟩
    | cons x0 xs' =>
      have hright : ((x0 :: xs').any (fun x' => !misereWinAdd (.mk (h0 :: hs')) x')) =
                    ((x0 :: xs').any (fun x' => !misereWin x')) :=
        any_congr_mem (fun x' hx' => congrArg Bool.not (ih x' hx'))
      rw [hright, ← misereWin_mk_ne_nil (by simp)]
      cases hx : misereWin (.mk (x0 :: xs')) with
      | true => simp only [Bool.or_true]
      | false =>
        simp only [Bool.or_false]
        cases hl : (h0 :: hs').any (fun u => !misereWinAdd u (.mk (x0 :: xs'))) with
        | false => rfl
        | true =>
          obtain ⟨u, hu, hnot⟩ := List.any_eq_true.mp hl
          have hz : g0 ∈ u.options := hzero u hu
          cases u with
          | mk uopts =>
            simp only [options] at hz
            cases uopts with
            | nil => nomatch hz
            | cons u0 us =>
              have huwin : misereWinAdd (.mk (u0 :: us)) (.mk (x0 :: xs')) = true := by
                rw [misereWinAdd_unfold (.inl (by simp))]
                have hleftTrue : ((u0 :: us).any (fun c => !misereWinAdd c (.mk (x0 :: xs')))) = true := by
                  apply List.any_eq_true.mpr
                  refine ⟨g0, hz, ?_⟩
                  rw [← misereWin_add_eq, show g0 = .mk [] from rfl, add_mk_nil_left, hx]
                  rfl
                rw [hleftTrue]
                rfl
              rw [huwin] at hnot
              nomatch hnot

end IGame
end Conjecture00000001291
