/-
  Conjecture 00000008545 — Complete Disproof in Self-Contained Core Lean 4 (v4.19.0)

  Official problem statement:
    English: "Definition: Uniformity of a lattice is the evenness of element covering numbers.
      Conjecture: The spectra of upper and lower uniform lattices are symmetric; and the
      minimal example of failure of uniformity is the 5-element nonmodular lattice.
      (minimal counterexample to uniformity)"
    Chinese: "定义：格的一致性（均匀性）指元素覆盖数的均匀。猜想：上/下均匀的格的谱对称；
      均匀性的失败的最小例为 5 元素非模格。（均匀性最小反例）"

  Summary of formalized results (zero sorry, zero native_decide, zero custom axioms):
    1. General finite bounded lattice theory (`FinLattice α`), covering relation (`Covers`),
       upper/lower/total covering numbers (`upperCovNum`, `lowerCovNum`, `totalCovNum`),
       modularity, distributivity (`distributive_implies_modular`), and canonical gradings
       (`Grading`, `grading_unique`).
    2. Regime I (Global non-extremal covering uniformity: constant `c⁺` on `L \ {1̂}` and
       constant `c⁻` on `L \ {0̂}`):
       - Universal minimality theorem (`all_card_le_3_globally_uniform`): EVERY finite lattice
         of cardinality `≤ 3` is globally uniform.
       - Refutation of Clause 2 (`disproof_global_minimal_counterexample`): the 4-element
         Boolean lattice `B₂` (`card = 4 < 5`) is distributive and modular, yet fails both
         global upper uniformity and global lower uniformity. (Also refutes unrestricted
         constancy on `C₂`, Hasse degree regularity on `C₃`, and arithmetic parity on `C₂`.)
    3. Regime II (Strict interior covering uniformity on `L \ {0̂, 1̂}`):
       - Refutation of both clauses (`disproof_interior_uniformity`): the 5-element nonmodular
         pentagon `N₅` SATISFIES interior upper and lower uniformity (so `N₅` is not a
         counterexample at all), whereas the 5-element distributive (hence modular) lattices
         `B₂ ⊕ 1` and `1 ⊕ B₂` FAIL interior uniformity; moreover `N₅` has non-zero-symmetric
         Hasse adjacency spectrum (`tr(A⁵) = 10 ≠ 0`).
    4. Regime III (Graded rank-wise covering uniformity — Terwilliger uniform lattices, under
       which `N₅` IS the minimal counterexample to uniformity):
       - Refutation of Clause 1 for Whitney / rank-size spectra and rank-covering profiles
         (`disproof_rank_uniform_whitney_and_profile`): `B₂ ⊕ 1` (`card = 5`, distributive
         and modular) is both rank-upper-uniform and rank-lower-uniform, yet its Whitney
         spectrum `[1, 2, 1, 1]` is not palindromic and its rank-covering profile is not
         top-bottom symmetric.
       - Refutation of Clause 1 for covering-degree multiset spectra and upper/lower symmetry
         (`disproof_rank_upper_uniform_multiset`): the 7-element graded lattice `Lat7` is
         rank-upper-uniform (and interior-upper-uniform), yet fails rank-lower-uniformity, has
         non-palindromic Whitney spectrum `[1, 3, 2, 1]`, and has unequal upper vs. lower
         covering-degree multisets (`|{x : c⁺(x) = 3}| = 1 ≠ 0 = |{x : c⁻(x) = 3}|`).
       - Refutation of shortest-chain height layer uniformity + Hasse graph eigenvalue symmetry
         (`disproof_min_height_hasse_spectrum`): the 6-element lattice `N₅ ⊕ 1` satisfies
         minimum-height upper uniformity yet has `tr(A⁵) = 10 ≠ 0`.
    5. Master synthesis theorem (`conjecture_00000008545_false`) combining all regimes alongside
       non-vacuity witnesses (`Chain3Lat`, `B2Lat`, `M3Lat`).
-/

namespace Conjecture00000008545

/-! ## Section 1: List Duplicate-Freedom and Finite Bounded Lattices -/

/-- Duplicate-free list predicate in Core Lean 4. -/
def Nodup {α : Type} : List α → Prop
  | [] => True
  | x :: xs => x ∉ xs ∧ Nodup xs

instance instDecidableNodup {α : Type} [DecidableEq α] : (l : List α) → Decidable (Nodup l)
  | [] => isTrue trivial
  | x :: xs =>
    match inferInstanceAs (Decidable (x ∉ xs)), instDecidableNodup xs with
    | isTrue h₁, isTrue h₂ => isTrue ⟨h₁, h₂⟩
    | isFalse h₁, _ => isFalse (fun h => h₁ h.1)
    | _, isFalse h₂ => isFalse (fun h => h₂ h.2)

theorem nodup_filter {α : Type} (p : α → Bool) :
    ∀ {l : List α}, Nodup l → Nodup (l.filter p)
  | [], _ => trivial
  | x :: xs, ⟨hx, hxs⟩ => by
    unfold List.filter
    cases p x with
    | false => exact nodup_filter p hxs
    | true =>
      exact ⟨fun hmem => hx (List.mem_filter.mp hmem).1, nodup_filter p hxs⟩

/-- Removing one occurrence of `a` from a list. -/
def eraseOne {α : Type} [DecidableEq α] (a : α) : List α → List α
  | [] => []
  | x :: xs => if x = a then xs else x :: eraseOne a xs

theorem length_eraseOne_of_mem {α : Type} [DecidableEq α] {a : α} :
    ∀ {l : List α}, a ∈ l → l.length = (eraseOne a l).length + 1
  | [], h => nomatch h
  | x :: xs, h => by
    unfold eraseOne
    by_cases hxa : x = a
    · simp [hxa]
    · simp only [hxa, ↓reduceIte, List.length_cons]
      cases h with
      | head => exact absurd rfl hxa
      | tail _ htail =>
        have ih := length_eraseOne_of_mem htail
        omega

theorem mem_eraseOne_of_ne {α : Type} [DecidableEq α] {a b : α} (hab : b ≠ a) :
    ∀ {l : List α}, b ∈ l → b ∈ eraseOne a l
  | [], h => nomatch h
  | x :: xs, h => by
    unfold eraseOne
    by_cases hxa : x = a
    · simp only [hxa, ↓reduceIte]
      cases h with
      | head => exact absurd hxa hab
      | tail _ htail => exact htail
    · simp only [hxa, ↓reduceIte]
      cases h with
      | head => exact List.Mem.head _
      | tail _ htail => exact List.Mem.tail _ (mem_eraseOne_of_ne hab htail)

theorem nodup_length_le_of_subset {α : Type} [DecidableEq α] :
    ∀ {l₁ l₂ : List α}, Nodup l₁ → (∀ x, x ∈ l₁ → x ∈ l₂) → l₁.length ≤ l₂.length
  | [], _, _, _ => Nat.zero_le _
  | x :: xs, l₂, ⟨hx, hxs⟩, hsub => by
    have hx₂ : x ∈ l₂ := hsub x (List.Mem.head _)
    have hlen : l₂.length = (eraseOne x l₂).length + 1 := length_eraseOne_of_mem hx₂
    have hsub' : ∀ y, y ∈ xs → y ∈ eraseOne x l₂ := by
      intro y hy
      have hyne : y ≠ x := fun hyeq => hx (hyeq ▸ hy)
      exact mem_eraseOne_of_ne hyne (hsub y (List.Mem.tail _ hy))
    have ih := nodup_length_le_of_subset hxs hsub'
    simp only [List.length_cons]
    omega

/-- Any two duplicate-free complete enumerations of `α` have identical length. -/
theorem enum_length_unique {α : Type} [DecidableEq α] {l₁ l₂ : List α}
    (hn₁ : Nodup l₁) (hc₁ : ∀ x : α, x ∈ l₁)
    (hn₂ : Nodup l₂) (hc₂ : ∀ x : α, x ∈ l₂) :
    l₁.length = l₂.length := by
  have h₁ := nodup_length_le_of_subset hn₁ (fun x _ => hc₂ x)
  have h₂ := nodup_length_le_of_subset hn₂ (fun x _ => hc₁ x)
  omega

/-- A finite bounded lattice on a decidable-equality carrier `α`, equipped with a
    duplicate-free complete enumeration `elems` and all partial-order, boundedness,
    least-upper-bound (`join`), and greatest-lower-bound (`meet`) axioms. -/
structure FinLattice (α : Type) [DecidableEq α] where
  elems : List α
  elems_nodup : Nodup elems
  elems_complete : ∀ x : α, x ∈ elems
  le : α → α → Bool
  join : α → α → α
  meet : α → α → α
  bot : α
  top : α
  le_refl : ∀ x, le x x = true
  le_trans : ∀ x y z, le x y = true → le y z = true → le x z = true
  le_antisymm : ∀ x y, le x y = true → le y x = true → x = y
  bot_le : ∀ x, le bot x = true
  le_top : ∀ x, le x top = true
  le_join_left : ∀ x y, le x (join x y) = true
  le_join_right : ∀ x y, le y (join x y) = true
  join_le : ∀ x y z, le x z = true → le y z = true → le (join x y) z = true
  meet_le_left : ∀ x y, le (meet x y) x = true
  meet_le_right : ∀ x y, le (meet x y) y = true
  le_meet : ∀ x y z, le z x = true → le z y = true → le z (meet x y) = true

namespace FinLattice

variable {α : Type} [DecidableEq α]

/-- Cardinality of the finite lattice `L`. -/
def card (L : FinLattice α) : Nat := L.elems.length

theorem card_pos (L : FinLattice α) : 1 ≤ L.card := by
  unfold card
  have h : L.bot ∈ L.elems := L.elems_complete L.bot
  cases hl : L.elems with
  | nil => rw [hl] at h; nomatch h
  | cons _ _ => simp

theorem join_eq_right_of_le (L : FinLattice α) {x z : α} (hxz : L.le x z = true) :
    L.join x z = z :=
  L.le_antisymm _ _ (L.join_le x z z hxz (L.le_refl z)) (L.le_join_right x z)

theorem meet_eq_left_of_le (L : FinLattice α) {x z : α} (hxz : L.le x z = true) :
    L.meet x z = x :=
  L.le_antisymm _ _ (L.meet_le_left x z) (L.le_meet x z x (L.le_refl x) hxz)

theorem meet_comm (L : FinLattice α) (x y : α) : L.meet x y = L.meet y x :=
  L.le_antisymm _ _
    (L.le_meet y x (L.meet x y) (L.meet_le_right x y) (L.meet_le_left x y))
    (L.le_meet x y (L.meet y x) (L.meet_le_right y x) (L.meet_le_left y x))

theorem join_comm (L : FinLattice α) (x y : α) : L.join x y = L.join y x :=
  L.le_antisymm _ _
    (L.join_le x y (L.join y x) (L.le_join_right y x) (L.le_join_left y x))
    (L.join_le y x (L.join x y) (L.le_join_right x y) (L.le_join_left x y))

/-! ## Section 2: Modularity, Distributivity, Covering Relation, and Covering Numbers -/

/-- Modular law: `x ≤ z → x ∨ (y ∧ z) = (x ∨ y) ∧ z`. -/
def IsModular (L : FinLattice α) : Prop :=
  ∀ x y z : α, L.le x z = true → L.join x (L.meet y z) = L.meet (L.join x y) z

/-- Distributive law: `x ∧ (y ∨ z) = (x ∧ y) ∨ (x ∧ z)`. -/
def IsDistributive (L : FinLattice α) : Prop :=
  ∀ x y z : α, L.meet x (L.join y z) = L.join (L.meet x y) (L.meet x z)

/-- Every distributive lattice is modular. -/
theorem distributive_implies_modular (L : FinLattice α) (hdist : L.IsDistributive) :
    L.IsModular := by
  intro x y z hxz
  calc
    L.join x (L.meet y z)
      = L.join (L.meet z x) (L.meet z y) := by
          rw [L.meet_comm z x, L.meet_eq_left_of_le hxz, L.meet_comm y z]
    _ = L.meet z (L.join x y) := (hdist z x y).symm
    _ = L.meet (L.join x y) z := L.meet_comm z (L.join x y)

/-- Strict order `x < y` in `L`. -/
def Lt (L : FinLattice α) (x y : α) : Prop :=
  L.le x y = true ∧ x ≠ y

/-- Executable strict order check. -/
def ltB (L : FinLattice α) (x y : α) : Bool :=
  L.le x y && decide (x ≠ y)

theorem ltB_iff (L : FinLattice α) (x y : α) : L.ltB x y = true ↔ L.Lt x y := by
  unfold ltB Lt
  simp

/-- Covering relation `x ⋖ y`: `x < y` and there is no `z` with `x < z < y`. -/
def Covers (L : FinLattice α) (x y : α) : Prop :=
  L.Lt x y ∧ ∀ z : α, ¬(L.Lt x z ∧ L.Lt z y)

/-- Executable covering check over `L.elems`. -/
def coversB (L : FinLattice α) (x y : α) : Bool :=
  L.ltB x y && L.elems.all (fun z => !(L.ltB x z && L.ltB z y))

theorem coversB_iff (L : FinLattice α) (x y : α) :
    L.coversB x y = true ↔ L.Covers x y := by
  unfold coversB Covers
  rw [Bool.and_eq_true, ltB_iff, List.all_eq_true]
  constructor
  · rintro ⟨hxy, hall⟩
    refine ⟨hxy, fun z ⟨hxz, hzy⟩ => ?_⟩
    have hz := hall z (L.elems_complete z)
    rw [Bool.not_eq_true', Bool.and_eq_false_iff] at hz
    cases hz with
    | inl h =>
      have ht : L.ltB x z = true := (L.ltB_iff x z).mpr hxz
      rw [ht] at h; contradiction
    | inr h =>
      have ht : L.ltB z y = true := (L.ltB_iff z y).mpr hzy
      rw [ht] at h; contradiction
  · rintro ⟨hxy, hno⟩
    refine ⟨hxy, fun z _ => ?_⟩
    rw [Bool.not_eq_true', Bool.and_eq_false_iff]
    by_cases hxz : L.ltB x z = true
    · right
      by_cases hzy : L.ltB z y = true
      · exact False.elim (hno z ⟨(L.ltB_iff x z).mp hxz, (L.ltB_iff z y).mp hzy⟩)
      · exact Bool.eq_false_iff.mpr hzy
    · left; exact Bool.eq_false_iff.mpr hxz

instance instDecidableCovers (L : FinLattice α) (x y : α) : Decidable (L.Covers x y) :=
  decidable_of_iff (L.coversB x y = true) (L.coversB_iff x y)

/-- Duplicate-free list of upper covers `{y ∈ L : x ⋖ y}`. -/
def upperCovList (L : FinLattice α) (x : α) : List α :=
  L.elems.filter (fun y => L.coversB x y)

/-- Duplicate-free list of lower covers `{y ∈ L : y ⋖ x}`. -/
def lowerCovList (L : FinLattice α) (x : α) : List α :=
  L.elems.filter (fun y => L.coversB y x)

theorem nodup_upperCovList (L : FinLattice α) (x : α) : Nodup (L.upperCovList x) :=
  nodup_filter _ L.elems_nodup

theorem nodup_lowerCovList (L : FinLattice α) (x : α) : Nodup (L.lowerCovList x) :=
  nodup_filter _ L.elems_nodup

theorem mem_upperCovList_iff (L : FinLattice α) (x y : α) :
    y ∈ L.upperCovList x ↔ L.Covers x y := by
  unfold upperCovList
  rw [List.mem_filter, L.coversB_iff]
  exact ⟨fun h => h.2, fun h => ⟨L.elems_complete y, h⟩⟩

theorem mem_lowerCovList_iff (L : FinLattice α) (x y : α) :
    y ∈ L.lowerCovList x ↔ L.Covers y x := by
  unfold lowerCovList
  rw [List.mem_filter, L.coversB_iff]
  exact ⟨fun h => h.2, fun h => ⟨L.elems_complete y, h⟩⟩

/-- Upper covering number `c⁺(x) = |{y ∈ L : x ⋖ y}|`. -/
def upperCovNum (L : FinLattice α) (x : α) : Nat :=
  (L.upperCovList x).length

/-- Lower covering number `c⁻(x) = |{y ∈ L : y ⋖ x}|`. -/
def lowerCovNum (L : FinLattice α) (x : α) : Nat :=
  (L.lowerCovList x).length

/-- Total covering degree `c(x) = c⁺(x) + c⁻(x)` in the Hasse diagram. -/
def totalCovNum (L : FinLattice α) (x : α) : Nat :=
  L.upperCovNum x + L.lowerCovNum x

theorem not_covers_top_left (L : FinLattice α) (y : α) : ¬L.Covers L.top y := by
  rintro ⟨⟨htopy, hne⟩, _⟩
  exact hne (L.le_antisymm L.top y htopy (L.le_top y))

theorem not_covers_bot_right (L : FinLattice α) (y : α) : ¬L.Covers y L.bot := by
  rintro ⟨⟨hybot, hne⟩, _⟩
  exact hne (L.le_antisymm y L.bot hybot (L.bot_le y))

theorem upperCovNum_top (L : FinLattice α) : L.upperCovNum L.top = 0 := by
  unfold upperCovNum
  cases h : L.upperCovList L.top with
  | nil => rfl
  | cons y ys =>
    have hy : y ∈ L.upperCovList L.top := by rw [h]; exact List.Mem.head _
    exact False.elim (L.not_covers_top_left y ((L.mem_upperCovList_iff L.top y).mp hy))

theorem lowerCovNum_bot (L : FinLattice α) : L.lowerCovNum L.bot = 0 := by
  unfold lowerCovNum
  cases h : L.lowerCovList L.bot with
  | nil => rfl
  | cons y ys =>
    have hy : y ∈ L.lowerCovList L.bot := by rw [h]; exact List.Mem.head _
    exact False.elim (L.not_covers_bot_right y ((L.mem_lowerCovList_iff L.bot y).mp hy))

/-! ## Section 3: All Standard Definitions of Lattice Uniformity and Spectra -/

/-- Regime I-A: Global non-extremal upper uniformity (`c⁺` constant on `L \ {1̂}`). -/
def GloballyUpperUniform (L : FinLattice α) : Prop :=
  ∀ x y : α, x ≠ L.top → y ≠ L.top → L.upperCovNum x = L.upperCovNum y

/-- Regime I-A: Global non-extremal lower uniformity (`c⁻` constant on `L \ {0̂}`). -/
def GloballyLowerUniform (L : FinLattice α) : Prop :=
  ∀ x y : α, x ≠ L.bot → y ≠ L.bot → L.lowerCovNum x = L.lowerCovNum y

/-- Regime I-A: Global covering uniformity (both upper and lower non-extremal constancy). -/
def GloballyUniform (L : FinLattice α) : Prop :=
  L.GloballyUpperUniform ∧ L.GloballyLowerUniform

/-- Regime I-B: Unrestricted global constancy of `c⁺` on all of `L`. -/
def UnrestrictedUpperUniform (L : FinLattice α) : Prop :=
  ∀ x y : α, L.upperCovNum x = L.upperCovNum y

/-- Regime I-C: Undirected Hasse diagram regularity (`c⁺(x) + c⁻(x)` constant on `L`). -/
def HasseRegular (L : FinLattice α) : Prop :=
  ∀ x y : α, L.totalCovNum x = L.totalCovNum y

/-- Regime I-D: Literal arithmetic parity reading ("evenness" = `2 ∣ c⁺(x)` on `L \ {1̂}`). -/
def ParityEvenUpper (L : FinLattice α) : Prop :=
  ∀ x : α, x ≠ L.top → L.upperCovNum x % 2 = 0

/-- Strict interior membership `x ∈ L \ {0̂, 1̂}`. -/
def IsInterior (L : FinLattice α) (x : α) : Prop :=
  x ≠ L.bot ∧ x ≠ L.top

/-- Regime II: Strict interior upper uniformity (`c⁺` constant on `L \ {0̂, 1̂}`). -/
def InteriorUpperUniform (L : FinLattice α) : Prop :=
  ∀ x y : α, L.IsInterior x → L.IsInterior y → L.upperCovNum x = L.upperCovNum y

/-- Regime II: Strict interior lower uniformity (`c⁻` constant on `L \ {0̂, 1̂}`). -/
def InteriorLowerUniform (L : FinLattice α) : Prop :=
  ∀ x y : α, L.IsInterior x → L.IsInterior y → L.lowerCovNum x = L.lowerCovNum y

/-- Regime II: Strict interior uniformity (both `c⁺` and `c⁻` constant on `L \ {0̂, 1̂}`). -/
def InteriorUniform (L : FinLattice α) : Prop :=
  L.InteriorUpperUniform ∧ L.InteriorLowerUniform

/-- A grading (rank function) on `L`: `rk(0̂) = 0` and `x ⋖ y → rk(y) = rk(x) + 1`. -/
structure Grading (L : FinLattice α) where
  rk : α → Nat
  rk_bot : rk L.bot = 0
  rk_covers : ∀ x y : α, L.Covers x y → rk y = rk x + 1

/-- Regime III: Graded rank-upper-uniformity (Terwilliger upper uniformity). -/
def RankUpperUniform (L : FinLattice α) (g : L.Grading) : Prop :=
  ∀ x y : α, g.rk x = g.rk y → L.upperCovNum x = L.upperCovNum y

/-- Regime III: Graded rank-lower-uniformity (Terwilliger lower uniformity). -/
def RankLowerUniform (L : FinLattice α) (g : L.Grading) : Prop :=
  ∀ x y : α, g.rk x = g.rk y → L.lowerCovNum x = L.lowerCovNum y

/-- Regime III: Graded rank-uniformity (Terwilliger uniform lattice). -/
def RankUniform (L : FinLattice α) (g : L.Grading) : Prop :=
  L.RankUpperUniform g ∧ L.RankLowerUniform g

/-- Existential graded rank-uniformity (without pre-fixing `g`; canonical by `grading_unique`). -/
def IsRankUniform (L : FinLattice α) : Prop :=
  ∃ g : L.Grading, L.RankUniform g

/-- Height `h = rk(1̂)` of a graded lattice. -/
def height (L : FinLattice α) (g : L.Grading) : Nat :=
  g.rk L.top

/-- `k`-th Whitney number of the second kind `W_k = |{x ∈ L : rk(x) = k}|`. -/
def whitneyNum (L : FinLattice α) (g : L.Grading) (k : Nat) : Nat :=
  (L.elems.filter (fun x => decide (g.rk x = k))).length

/-- Whitney / rank-size spectrum `[W_0, W_1, ..., W_h]`. -/
def whitneySpectrum (L : FinLattice α) (g : L.Grading) : List Nat :=
  (List.range (L.height g + 1)).map (L.whitneyNum g)

/-- Palindromic symmetry of the Whitney / rank-size spectrum. -/
def WhitneySymmetric (L : FinLattice α) (g : L.Grading) : Prop :=
  L.whitneySpectrum g = (L.whitneySpectrum g).reverse

instance instDecidableWhitneySymmetric (L : FinLattice α) (g : L.Grading) :
    Decidable (L.WhitneySymmetric g) :=
  inferInstanceAs (Decidable (L.whitneySpectrum g = (L.whitneySpectrum g).reverse))

/-- Top-bottom symmetry of rank covering numbers `c⁺` vs. `c⁻` across complementary ranks. -/
def RankCoveringSymmetric (L : FinLattice α) (g : L.Grading) : Prop :=
  ∀ x y : α, g.rk x + g.rk y = L.height g → L.upperCovNum x = L.lowerCovNum y

/-- Multiplicity of covering degree `d` in `{c⁺(x) : x ∈ L}`. -/
def upperDegCount (L : FinLattice α) (d : Nat) : Nat :=
  (L.elems.filter (fun x => decide (L.upperCovNum x = d))).length

/-- Multiplicity of covering degree `d` in `{c⁻(x) : x ∈ L}`. -/
def lowerDegCount (L : FinLattice α) (d : Nat) : Nat :=
  (L.elems.filter (fun x => decide (L.lowerCovNum x = d))).length

/-- Equality (symmetry) between the upper covering-number multiset `{c⁺(x) : x ∈ L}`
    and the lower covering-number multiset `{c⁻(x) : x ∈ L}`. -/
def CoveringMultisetSymmetric (L : FinLattice α) : Prop :=
  ∀ d : Nat, L.upperDegCount d = L.lowerDegCount d

/-! ## Section 4: Universal Structural Theorems (Covering Chains, Grading Uniqueness,
    and Global Uniformity of All Lattices of Cardinality `≤ 3`) -/

/-- Strict interval `{z ∈ L : x < z ∧ z < y}` used as termination measure. -/
def openInterval (L : FinLattice α) (x y : α) : List α :=
  L.elems.filter (fun z => L.ltB x z && L.ltB z y)

theorem mem_openInterval_iff (L : FinLattice α) (x y z : α) :
    z ∈ L.openInterval x y ↔ L.Lt x z ∧ L.Lt z y := by
  unfold openInterval
  rw [List.mem_filter, Bool.and_eq_true, L.ltB_iff, L.ltB_iff]
  exact ⟨fun h => h.2, fun h => ⟨L.elems_complete z, h⟩⟩

/-- In any finite lattice, if `x < y`, there is an upper cover `w` of `x` with `w ≤ y`. -/
theorem exists_cover_le_of_lt (L : FinLattice α) :
    ∀ (n : Nat) {x y : α}, (L.openInterval x y).length ≤ n → L.Lt x y →
      ∃ w : α, L.Covers x w ∧ L.le w y = true
  | 0, x, y, hlen, hxy => by
    refine ⟨y, ⟨hxy, fun z hz => ?_⟩, L.le_refl y⟩
    have hmem : z ∈ L.openInterval x y := (L.mem_openInterval_iff x y z).mpr hz
    cases h : L.openInterval x y with
    | nil => rw [h] at hmem; nomatch hmem
    | cons _ _ => rw [h] at hlen; simp at hlen
  | n + 1, x, y, hlen, hxy => by
    by_cases hcov : L.Covers x y
    · exact ⟨y, hcov, L.le_refl y⟩
    · -- Since `L.coversB x y` is decidable, find an intermediate element in `openInterval x y`
      cases hlist : L.openInterval x y with
      | nil =>
        refine ⟨y, ⟨hxy, fun z hz => ?_⟩, L.le_refl y⟩
        have hmem := (L.mem_openInterval_iff x y z).mpr hz
        rw [hlist] at hmem; nomatch hmem
      | cons z zs =>
        have hzmem : z ∈ L.openInterval x y := by rw [hlist]; exact List.Mem.head _
        have ⟨hxz, hzy⟩ := (L.mem_openInterval_iff x y z).mp hzmem
        -- `openInterval x z` is a duplicate-free subset of `openInterval x y` missing `z`
        have hsub : ∀ u, u ∈ L.openInterval x z → u ∈ eraseOne z (L.openInterval x y) := by
          intro u hu
          have ⟨hxu, huz⟩ := (L.mem_openInterval_iff x z u).mp hu
          have huy : L.Lt u y :=
            ⟨L.le_trans u z y huz.1 hzy.1, fun hueq =>
              huz.2 (L.le_antisymm u z huz.1 (hueq ▸ hzy.1))⟩
          have hune : u ≠ z := huz.2
          exact mem_eraseOne_of_ne hune ((L.mem_openInterval_iff x y u).mpr ⟨hxu, huy⟩)
        have hnodup : Nodup (L.openInterval x z) := nodup_filter _ L.elems_nodup
        have hle1 := nodup_length_le_of_subset hnodup hsub
        have hle2 := length_eraseOne_of_mem hzmem
        have hsmall : (L.openInterval x z).length ≤ n := by omega
        obtain ⟨w, hwcov, hwz⟩ := exists_cover_le_of_lt L n hsmall hxz
        exact ⟨w, hwcov, L.le_trans w z y hwz hzy.1⟩

/-- Every element in a finite bounded lattice is connected from `0̂` by a covering chain,
    which forces any two `Grading`s on `L` to agree everywhere. -/
theorem grading_eq_aux (L : FinLattice α) (g₁ g₂ : L.Grading) :
    ∀ (n : Nat) (x : α), (L.elems.filter (fun z => L.ltB z x)).length ≤ n →
      g₁.rk x = g₂.rk x
  | 0, x, hlen => by
    by_cases hx : x = L.bot
    · rw [hx, g₁.rk_bot, g₂.rk_bot]
    · have hlt : L.Lt L.bot x := ⟨L.bot_le x, Ne.symm hx⟩
      have hmem : L.bot ∈ L.elems.filter (fun z => L.ltB z x) := by
        rw [List.mem_filter, L.ltB_iff]
        exact ⟨L.elems_complete L.bot, hlt⟩
      cases h : L.elems.filter (fun z => L.ltB z x) with
      | nil => rw [h] at hmem; nomatch hmem
      | cons _ _ => rw [h] at hlen; simp at hlen
  | n + 1, x, hlen => by
    by_cases hx : x = L.bot
    · rw [hx, g₁.rk_bot, g₂.rk_bot]
    · -- Dually pick a maximal element strictly below `x`, i.e., a lower cover of `x`
      -- Equivalently, apply covering step from `bot`? Wait: if we step UP from `bot`, the upper
      -- interval shrinks; here let's find `w ⋖ x` directly!
      have hbotx : L.Lt L.bot x := ⟨L.bot_le x, Ne.symm hx⟩
      -- Check if any `w` covers-below `x` via dual interval `(w, x)`:
      -- Even simpler: by induction on `(openInterval y x).length` we find `w` with `y ≤ w` and `w ⋖ x`!
      let rec find_lower_cover :
          ∀ (m : Nat) {y : α}, (L.openInterval y x).length ≤ m → L.Lt y x →
            ∃ w : α, L.le y w = true ∧ L.Covers w x
        | 0, y, hm, hyx => by
          refine ⟨y, L.le_refl y, ⟨hyx, fun z hz => ?_⟩⟩
          have hmem := (L.mem_openInterval_iff y x z).mpr hz
          cases h : L.openInterval y x with
          | nil => rw [h] at hmem; nomatch hmem
          | cons _ _ => rw [h] at hm; simp at hm
        | m + 1, y, hm, hyx => by
          cases hlist : L.openInterval y x with
          | nil =>
            refine ⟨y, L.le_refl y, ⟨hyx, fun z hz => ?_⟩⟩
            have hmem := (L.mem_openInterval_iff y x z).mpr hz
            rw [hlist] at hmem; nomatch hmem
          | cons z zs =>
            have hzmem : z ∈ L.openInterval y x := by rw [hlist]; exact List.Mem.head _
            have ⟨hyz, hzx⟩ := (L.mem_openInterval_iff y x z).mp hzmem
            have hsub : ∀ u, u ∈ L.openInterval z x → u ∈ eraseOne z (L.openInterval y x) := by
              intro u hu
              have ⟨hzu, hux⟩ := (L.mem_openInterval_iff z x u).mp hu
              have hyu : L.Lt y u :=
                ⟨L.le_trans y z u hyz.1 hzu.1, fun hyeq =>
                  hyz.2 (L.le_antisymm y z hyz.1 (hyeq ▸ hzu.1))⟩
              exact mem_eraseOne_of_ne hzu.2.symm ((L.mem_openInterval_iff y x u).mpr ⟨hyu, hux⟩)
            have hnd_zx : Nodup (L.openInterval z x) := nodup_filter _ L.elems_nodup
            have hle1 := nodup_length_le_of_subset hnd_zx hsub
            have hle2 := length_eraseOne_of_mem hzmem
            obtain ⟨w, hzw, hwcov⟩ := find_lower_cover m (by omega) hzx
            exact ⟨w, L.le_trans y z w hyz.1 hzw, hwcov⟩
      obtain ⟨w, _, hwcov⟩ := find_lower_cover (L.openInterval L.bot x).length (Nat.le_refl _) hbotx
      have hwmem : w ∈ L.elems.filter (fun z => L.ltB z x) := by
        rw [List.mem_filter, L.ltB_iff]
        exact ⟨L.elems_complete w, hwcov.1⟩
      have hsub : ∀ u, u ∈ L.elems.filter (fun z => L.ltB z w) →
          u ∈ eraseOne w (L.elems.filter (fun z => L.ltB z x)) := by
        intro u hu
        rw [List.mem_filter, L.ltB_iff] at hu
        have hux : L.Lt u x :=
          ⟨L.le_trans u w x hu.2.1 hwcov.1.1, fun hueq =>
            hu.2.2 (L.le_antisymm u w hu.2.1 (hueq ▸ hwcov.1.1))⟩
        apply mem_eraseOne_of_ne hu.2.2
        rw [List.mem_filter, L.ltB_iff]
        exact ⟨L.elems_complete u, hux⟩
      have hle1 := nodup_length_le_of_subset (nodup_filter _ L.elems_nodup) hsub
      have hle2 := length_eraseOne_of_mem hwmem
      have ih := grading_eq_aux L g₁ g₂ n w (by omega)
      rw [g₁.rk_covers w x hwcov, g₂.rk_covers w x hwcov, ih]

/-- Uniqueness of the rank function on any graded finite lattice. -/
theorem grading_unique (L : FinLattice α) (g₁ g₂ : L.Grading) (x : α) :
    g₁.rk x = g₂.rk x :=
  L.grading_eq_aux g₁ g₂ _ x (Nat.le_refl _)

/-- Helper lemma for 3-element lattices `{bot, m, top}`. -/
private theorem three_elem_uniform_aux (L : FinLattice α) (m : α)
    (hmb : m ≠ L.bot) (hmt : m ≠ L.top)
    (htri : ∀ z : α, z = L.bot ∨ z = m ∨ z = L.top) :
    L.GloballyUniform := by
  have hcov_bm : L.Covers L.bot m := by
    refine ⟨⟨L.bot_le m, hmb.symm⟩, fun z ⟨hbz, hzm⟩ => ?_⟩
    rcases htri z with rfl | rfl | rfl
    · exact hbz.2 rfl
    · exact hzm.2 rfl
    · exact hmt (L.le_antisymm m L.top (L.le_top m) hzm.1)
  have hcov_mt : L.Covers m L.top := by
    refine ⟨⟨L.le_top m, hmt⟩, fun z ⟨hmz, hzt⟩ => ?_⟩
    rcases htri z with rfl | rfl | rfl
    · exact hmb (L.le_antisymm m L.bot hmz.1 (L.bot_le m))
    · exact hmz.2 rfl
    · exact hzt.2 rfl
  have hncov_bt : ¬L.Covers L.bot L.top := fun ⟨_, hno⟩ =>
    hno m ⟨⟨L.bot_le m, hmb.symm⟩, ⟨L.le_top m, hmt⟩⟩
  have hncov_bb : ¬L.Covers L.bot L.bot := fun ⟨⟨_, hne⟩, _⟩ => hne rfl
  have hncov_mm : ¬L.Covers m m := fun ⟨⟨_, hne⟩, _⟩ => hne rfl
  have hncov_mb : ¬L.Covers m L.bot := L.not_covers_bot_right m
  have hncov_tb : ¬L.Covers L.top m := L.not_covers_top_left m
  -- Exact length = 1 for any duplicate-free list whose unique inhabitant is `a`
  have uniq_len_eq_one : ∀ {l : List α} (a : α), Nodup l → a ∈ l →
      (∀ z, z ∈ l → z = a) → l.length = 1 := by
    intro l a hnd hmem huniq
    cases l with
    | nil => nomatch hmem
    | cons u us =>
      have hua : u = a := huniq u (List.Mem.head _)
      cases us with
      | nil => rfl
      | cons v vs =>
        have hva : v = a := huniq v (List.Mem.tail _ (List.Mem.head _))
        have huv : u = v := hua.trans hva.symm
        exact False.elim (hnd.1 (huv ▸ List.Mem.head _))
  have hubot : L.upperCovNum L.bot = 1 := by
    apply uniq_len_eq_one m (L.nodup_upperCovList L.bot)
      ((L.mem_upperCovList_iff L.bot m).mpr hcov_bm)
    intro z hz
    have hcz := (L.mem_upperCovList_iff L.bot z).mp hz
    rcases htri z with rfl | rfl | rfl
    · exact False.elim (hncov_bb hcz)
    · rfl
    · exact False.elim (hncov_bt hcz)
  have hum : L.upperCovNum m = 1 := by
    apply uniq_len_eq_one L.top (L.nodup_upperCovList m)
      ((L.mem_upperCovList_iff m L.top).mpr hcov_mt)
    intro z hz
    have hcz := (L.mem_upperCovList_iff m z).mp hz
    rcases htri z with rfl | rfl | rfl
    · exact False.elim (hncov_mb hcz)
    · exact False.elim (hncov_mm hcz)
    · rfl
  have hlm : L.lowerCovNum m = 1 := by
    apply uniq_len_eq_one L.bot (L.nodup_lowerCovList m)
      ((L.mem_lowerCovList_iff m L.bot).mpr hcov_bm)
    intro z hz
    have hcz := (L.mem_lowerCovList_iff m z).mp hz
    rcases htri z with rfl | rfl | rfl
    · rfl
    · exact False.elim (hncov_mm hcz)
    · exact False.elim (hncov_tb hcz)
  have hltop : L.lowerCovNum L.top = 1 := by
    apply uniq_len_eq_one m (L.nodup_lowerCovList L.top)
      ((L.mem_lowerCovList_iff L.top m).mpr hcov_mt)
    intro z hz
    have hcz := (L.mem_lowerCovList_iff L.top z).mp hz
    rcases htri z with rfl | rfl | rfl
    · exact False.elim (hncov_bt hcz)
    · rfl
    · exact False.elim (L.not_covers_top_left L.top hcz)
  constructor
  · intro x y hx hy
    have hxv : L.upperCovNum x = 1 := by
      rcases htri x with rfl | rfl | rfl
      · exact hubot
      · exact hum
      · exact False.elim (hx rfl)
    have hyv : L.upperCovNum y = 1 := by
      rcases htri y with rfl | rfl | rfl
      · exact hubot
      · exact hum
      · exact False.elim (hy rfl)
    rw [hxv, hyv]
  · intro x y hx hy
    have hxv : L.lowerCovNum x = 1 := by
      rcases htri x with rfl | rfl | rfl
      · exact False.elim (hx rfl)
      · exact hlm
      · exact hltop
    have hyv : L.lowerCovNum y = 1 := by
      rcases htri y with rfl | rfl | rfl
      · exact False.elim (hy rfl)
      · exact hlm
      · exact hltop
    rw [hxv, hyv]

/-- Universal Minimality Theorem: EVERY finite lattice of cardinality at most `3`
    is globally uniform (both globally upper-uniform and globally lower-uniform). -/
theorem all_card_le_3_globally_uniform (L : FinLattice α) (hcard : L.card ≤ 3) :
    L.GloballyUniform := by
  unfold card at hcard
  have hnd := L.elems_nodup
  have hcomp := L.elems_complete
  cases he : L.elems with
  | nil =>
    have hb := hcomp L.bot; rw [he] at hb; nomatch hb
  | cons a rest =>
    cases rest with
    | nil =>
      have all_eq : ∀ x : α, x = a := by
        intro x; have hx := hcomp x; rw [he] at hx
        cases hx with
        | head => rfl
        | tail _ ht => nomatch ht
      exact ⟨fun x y _ _ => by rw [all_eq x, all_eq y],
             fun x y _ _ => by rw [all_eq x, all_eq y]⟩
    | cons b rest₂ =>
      cases rest₂ with
      | nil =>
        have two_cases : ∀ x : α, x = a ∨ x = b := by
          intro x; have hx := hcomp x; rw [he] at hx
          cases hx with
          | head => exact Or.inl rfl
          | tail _ ht =>
            cases ht with
            | head => exact Or.inr rfl
            | tail _ ht₂ => nomatch ht₂
        constructor
        · intro x y hx hy
          rcases two_cases L.top with htop | htop
          · rcases two_cases x with rfl | rfl
            · exact False.elim (hx htop.symm)
            · rcases two_cases y with rfl | rfl
              · exact False.elim (hy htop.symm)
              · rfl
          · rcases two_cases x with rfl | rfl
            · rcases two_cases y with rfl | rfl
              · rfl
              · exact False.elim (hy htop.symm)
            · exact False.elim (hx htop.symm)
        · intro x y hx hy
          rcases two_cases L.bot with hbot | hbot
          · rcases two_cases x with rfl | rfl
            · exact False.elim (hx hbot.symm)
            · rcases two_cases y with rfl | rfl
              · exact False.elim (hy hbot.symm)
              · rfl
          · rcases two_cases x with rfl | rfl
            · rcases two_cases y with rfl | rfl
              · rfl
              · exact False.elim (hy hbot.symm)
            · exact False.elim (hx hbot.symm)
      | cons c rest₃ =>
        cases rest₃ with
        | cons _ _ => rw [he] at hcard; simp at hcard
        | nil =>
          rw [he] at hnd
          obtain ⟨habc, hbnc, _⟩ := hnd
          have hab : a ≠ b := fun h => habc (h ▸ List.Mem.head _)
          have hac : a ≠ c := fun h => habc (h ▸ List.Mem.tail _ (List.Mem.head _))
          have hbc : b ≠ c := fun h => hbnc (h ▸ List.Mem.head _)
          have three_cases : ∀ z : α, z = a ∨ z = b ∨ z = c := by
            intro z; have hz := hcomp z; rw [he] at hz
            cases hz with
            | head => exact Or.inl rfl
            | tail _ ht =>
              cases ht with
              | head => exact Or.inr (Or.inl rfl)
              | tail _ ht₂ =>
                cases ht₂ with
                | head => exact Or.inr (Or.inr rfl)
                | tail _ ht₃ => nomatch ht₃
          have hbt : L.bot ≠ L.top := by
            intro hbt_eq
            have all_eq_bot : ∀ z : α, z = L.bot := fun z =>
              L.le_antisymm z L.bot (hbt_eq ▸ L.le_top z) (L.bot_le z)
            exact hab ((all_eq_bot a).trans (all_eq_bot b).symm)
          -- Find the unique element of `{a, b, c}` distinct from `L.bot` and `L.top`
          rcases three_cases L.bot with hb | hb | hb <;>
          rcases three_cases L.top with ht | ht | ht
          · exact False.elim (hbt (hb.trans ht.symm))
          · refine L.three_elem_uniform_aux c
              (by intro h; subst hb h; exact hac rfl)
              (by intro h; subst ht h; exact hbc rfl) ?_
            intro z; rcases three_cases z with rfl | rfl | rfl
            · exact Or.inl hb.symm
            · exact Or.inr (Or.inr ht.symm)
            · exact Or.inr (Or.inl rfl)
          · refine L.three_elem_uniform_aux b
              (by intro h; subst hb h; exact hab rfl)
              (by intro h; subst ht h; exact hbc rfl) ?_
            intro z; rcases three_cases z with rfl | rfl | rfl
            · exact Or.inl hb.symm
            · exact Or.inr (Or.inl rfl)
            · exact Or.inr (Or.inr ht.symm)
          · refine L.three_elem_uniform_aux c
              (by intro h; subst hb h; exact hbc rfl)
              (by intro h; subst ht h; exact hac rfl) ?_
            intro z; rcases three_cases z with rfl | rfl | rfl
            · exact Or.inr (Or.inr ht.symm)
            · exact Or.inl hb.symm
            · exact Or.inr (Or.inl rfl)
          · exact False.elim (hbt (hb.trans ht.symm))
          · refine L.three_elem_uniform_aux a
              (by intro h; subst hb h; exact hab rfl)
              (by intro h; subst ht h; exact hac rfl) ?_
            intro z; rcases three_cases z with rfl | rfl | rfl
            · exact Or.inr (Or.inl rfl)
            · exact Or.inl hb.symm
            · exact Or.inr (Or.inr ht.symm)
          · refine L.three_elem_uniform_aux b
              (by intro h; subst hb h; exact hbc rfl)
              (by intro h; subst ht h; exact hab rfl) ?_
            intro z; rcases three_cases z with rfl | rfl | rfl
            · exact Or.inr (Or.inr ht.symm)
            · exact Or.inr (Or.inl rfl)
            · exact Or.inl hb.symm
          · refine L.three_elem_uniform_aux a
              (by intro h; subst hb h; exact hac rfl)
              (by intro h; subst ht h; exact hab rfl) ?_
            intro z; rcases three_cases z with rfl | rfl | rfl
            · exact Or.inr (Or.inl rfl)
            · exact Or.inr (Or.inr ht.symm)
            · exact Or.inl hb.symm
          · exact False.elim (hbt (hb.trans ht.symm))

end FinLattice

/-! ## Section 5: Matrix Power and Trace Utilities (for Hasse Adjacency Graph Spectra) -/

/-- `n × n` integer matrix represented as `Fin n → Fin n → Int`. -/
abbrev IntMat (n : Nat) := Fin n → Fin n → Int

def sumFin : (n : Nat) → (Fin n → Int) → Int
  | 0, _ => 0
  | n + 1, f => f ⟨0, Nat.zero_lt_succ n⟩ + sumFin n (fun i => f ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)

def matMul {n : Nat} (A B : IntMat n) : IntMat n :=
  fun i j => sumFin n (fun k => A i k * B k j)

def matId (n : Nat) : IntMat n :=
  fun i j => if i = j then 1 else 0

def matPow {n : Nat} (A : IntMat n) : Nat → IntMat n
  | 0 => matId n
  | k + 1 => matMul (matPow A k) A

def matTrace {n : Nat} (A : IntMat n) : Int :=
  sumFin n (fun i => A i i)

/-- Undirected Hasse diagram adjacency matrix of `L` indexed by `Fin n`. -/
def hasseAdj {α : Type} [DecidableEq α] (L : FinLattice α) {n : Nat} (idx : Fin n → α) : IntMat n :=
  fun i j => if L.coversB (idx i) (idx j) || L.coversB (idx j) (idx i) then 1 else 0

/-! ## Section 6: Concrete Verified Finite Lattices (`C₂`, `C₃`, `B₂`, `M₃`, `N₅`,
    `B₂ ⊕ 1`, `1 ⊕ B₂`, `N₅ ⊕ 1`, and `L₇`) -/

/-! ### 6.1 Two-Element Chain `C₂` and Three-Element Chain `C₃` -/

inductive C2 | bot | top deriving DecidableEq, Repr

def C2Lat : FinLattice C2 where
  elems := [.bot, .top]
  elems_nodup := by decide
  elems_complete := fun x => by cases x <;> decide
  le x y := match x, y with | .top, .bot => false | _, _ => true
  join x y := match x, y with | .bot, .bot => .bot | _, _ => .top
  meet x y := match x, y with | .top, .top => .top | _, _ => .bot
  bot := .bot
  top := .top
  le_refl := fun x => by cases x <;> rfl
  le_trans := fun x y z => by cases x <;> cases y <;> cases z <;> decide
  le_antisymm := fun x y => by cases x <;> cases y <;> decide
  bot_le := fun x => by cases x <;> rfl
  le_top := fun x => by cases x <;> rfl
  le_join_left := fun x y => by cases x <;> cases y <;> rfl
  le_join_right := fun x y => by cases x <;> cases y <;> rfl
  join_le := fun x y z => by cases x <;> cases y <;> cases z <;> decide
  meet_le_left := fun x y => by cases x <;> cases y <;> rfl
  meet_le_right := fun x y => by cases x <;> cases y <;> rfl
  le_meet := fun x y z => by cases x <;> cases y <;> cases z <;> decide

inductive C3 | bot | mid | top deriving DecidableEq, Repr

def C3Lat : FinLattice C3 where
  elems := [.bot, .mid, .top]
  elems_nodup := by decide
  elems_complete := fun x => by cases x <;> decide
  le x y := match x, y with
    | .bot, _ => true
    | .mid, .mid | .mid, .top => true
    | .top, .top => true
    | _, _ => false
  join x y := match x, y with
    | .top, _ | _, .top => .top
    | .mid, _ | _, .mid => .mid
    | .bot, .bot => .bot
  meet x y := match x, y with
    | .bot, _ | _, .bot => .bot
    | .mid, _ | _, .mid => .mid
    | .top, .top => .top
  bot := .bot
  top := .top
  le_refl := fun x => by cases x <;> rfl
  le_trans := fun x y z => by cases x <;> cases y <;> cases z <;> decide
  le_antisymm := fun x y => by cases x <;> cases y <;> decide
  bot_le := fun x => by cases x <;> rfl
  le_top := fun x => by cases x <;> rfl
  le_join_left := fun x y => by cases x <;> cases y <;> rfl
  le_join_right := fun x y => by cases x <;> cases y <;> rfl
  join_le := fun x y z => by cases x <;> cases y <;> cases z <;> decide
  meet_le_left := fun x y => by cases x <;> cases y <;> rfl
  meet_le_right := fun x y => by cases x <;> cases y <;> rfl
  le_meet := fun x y z => by cases x <;> cases y <;> cases z <;> decide

def C3Grading : C3Lat.Grading where
  rk | .bot => 0 | .mid => 1 | .top => 2
  rk_bot := rfl
  rk_covers := fun x y h => by
    have hb : C3Lat.coversB x y = true := (C3Lat.coversB_iff x y).mpr h
    cases x <;> cases y <;> revert hb <;> decide

/-! ### 6.2 Four-Element Boolean Lattice `B₂ = C₂ × C₂` -/

inductive B2 | bot | a | b | top deriving DecidableEq, Repr

def B2Lat : FinLattice B2 where
  elems := [.bot, .a, .b, .top]
  elems_nodup := by decide
  elems_complete := fun x => by cases x <;> decide
  le x y := match x, y with
    | .bot, _ => true
    | _, .top => true
    | .a, .a => true
    | .b, .b => true
    | _, _ => false
  join x y := match x, y with
    | .bot, z | z, .bot => z
    | .top, _ | _, .top => .top
    | .a, .a => .a
    | .b, .b => .b
    | _, _ => .top
  meet x y := match x, y with
    | .top, z | z, .top => z
    | .bot, _ | _, .bot => .bot
    | .a, .a => .a
    | .b, .b => .b
    | _, _ => .bot
  bot := .bot
  top := .top
  le_refl := fun x => by cases x <;> rfl
  le_trans := fun x y z => by cases x <;> cases y <;> cases z <;> decide
  le_antisymm := fun x y => by cases x <;> cases y <;> decide
  bot_le := fun x => by cases x <;> rfl
  le_top := fun x => by cases x <;> decide
  le_join_left := fun x y => by cases x <;> cases y <;> decide
  le_join_right := fun x y => by cases x <;> cases y <;> decide
  join_le := fun x y z => by cases x <;> cases y <;> cases z <;> decide
  meet_le_left := fun x y => by cases x <;> cases y <;> decide
  meet_le_right := fun x y => by cases x <;> cases y <;> decide
  le_meet := fun x y z => by cases x <;> cases y <;> cases z <;> decide

def B2Grading : B2Lat.Grading where
  rk | .bot => 0 | .a => 1 | .b => 1 | .top => 2
  rk_bot := rfl
  rk_covers := fun x y h => by
    have hb : B2Lat.coversB x y = true := (B2Lat.coversB_iff x y).mpr h
    cases x <;> cases y <;> revert hb <;> decide

/-! ### 6.3 Five-Element Modular Non-Distributive Diamond `M₃` -/

inductive M3 | bot | a | b | c | top deriving DecidableEq, Repr

def M3Lat : FinLattice M3 where
  elems := [.bot, .a, .b, .c, .top]
  elems_nodup := by decide
  elems_complete := fun x => by cases x <;> decide
  le x y := match x, y with
    | .bot, _ => true
    | _, .top => true
    | .a, .a | .b, .b | .c, .c => true
    | _, _ => false
  join x y := match x, y with
    | .bot, z | z, .bot => z
    | .top, _ | _, .top => .top
    | .a, .a => .a | .b, .b => .b | .c, .c => .c
    | _, _ => .top
  meet x y := match x, y with
    | .top, z | z, .top => z
    | .bot, _ | _, .bot => .bot
    | .a, .a => .a | .b, .b => .b | .c, .c => .c
    | _, _ => .bot
  bot := .bot
  top := .top
  le_refl := fun x => by cases x <;> rfl
  le_trans := fun x y z => by cases x <;> cases y <;> cases z <;> decide
  le_antisymm := fun x y => by cases x <;> cases y <;> decide
  bot_le := fun x => by cases x <;> rfl
  le_top := fun x => by cases x <;> decide
  le_join_left := fun x y => by cases x <;> cases y <;> decide
  le_join_right := fun x y => by cases x <;> cases y <;> decide
  join_le := fun x y z => by cases x <;> cases y <;> cases z <;> decide
  meet_le_left := fun x y => by cases x <;> cases y <;> decide
  meet_le_right := fun x y => by cases x <;> cases y <;> decide
  le_meet := fun x y z => by cases x <;> cases y <;> cases z <;> decide

def M3Grading : M3Lat.Grading where
  rk | .bot => 0 | .a => 1 | .b => 1 | .c => 1 | .top => 2
  rk_bot := rfl
  rk_covers := fun x y h => by
    have hb : M3Lat.coversB x y = true := (M3Lat.coversB_iff x y).mpr h
    cases x <;> cases y <;> revert hb <;> decide

/-! ### 6.4 Five-Element Nonmodular Pentagon `N₅` (`bot ⋖ a ⋖ top`, `bot ⋖ b ⋖ c ⋖ top`) -/

inductive N5 | bot | a | b | c | top deriving DecidableEq, Repr

def N5Lat : FinLattice N5 where
  elems := [.bot, .a, .b, .c, .top]
  elems_nodup := by decide
  elems_complete := fun x => by cases x <;> decide
  le x y := match x, y with
    | .bot, _ => true
    | _, .top => true
    | .a, .a => true
    | .b, .b | .b, .c => true
    | .c, .c => true
    | _, _ => false
  join x y := match x, y with
    | .bot, z | z, .bot => z
    | .top, _ | _, .top => .top
    | .a, .a => .a
    | .b, .b => .b
    | .b, .c | .c, .b | .c, .c => .c
    | _, _ => .top
  meet x y := match x, y with
    | .top, z | z, .top => z
    | .bot, _ | _, .bot => .bot
    | .a, .a => .a
    | .c, .c => .c
    | .b, .b | .b, .c | .c, .b => .b
    | _, _ => .bot
  bot := .bot
  top := .top
  le_refl := fun x => by cases x <;> rfl
  le_trans := fun x y z => by cases x <;> cases y <;> cases z <;> decide
  le_antisymm := fun x y => by cases x <;> cases y <;> decide
  bot_le := fun x => by cases x <;> rfl
  le_top := fun x => by cases x <;> decide
  le_join_left := fun x y => by cases x <;> cases y <;> decide
  le_join_right := fun x y => by cases x <;> cases y <;> decide
  join_le := fun x y z => by cases x <;> cases y <;> cases z <;> decide
  meet_le_left := fun x y => by cases x <;> cases y <;> decide
  meet_le_right := fun x y => by cases x <;> cases y <;> decide
  le_meet := fun x y z => by cases x <;> cases y <;> cases z <;> decide

def N5Idx : Fin 5 → N5
  | ⟨0, _⟩ => .bot | ⟨1, _⟩ => .a | ⟨2, _⟩ => .b | ⟨3, _⟩ => .c | ⟨4, _⟩ => .top

/-! ### 6.5 Five-Element Distributive Lattice `B₂ ⊕ 1` (`bot ⋖ a, b ⋖ u ⋖ top`)
    and Its Dual `1 ⊕ B₂` (`bot ⋖ u ⋖ a, b ⋖ top`) -/

inductive B2Plus1 | bot | a | b | u | top deriving DecidableEq, Repr

def B2Plus1Lat : FinLattice B2Plus1 where
  elems := [.bot, .a, .b, .u, .top]
  elems_nodup := by decide
  elems_complete := fun x => by cases x <;> decide
  le x y := match x, y with
    | .bot, _ => true
    | _, .top => true
    | .a, .a | .a, .u => true
    | .b, .b | .b, .u => true
    | .u, .u => true
    | _, _ => false
  join x y := match x, y with
    | .bot, z | z, .bot => z
    | .top, _ | _, .top => .top
    | .a, .a => .a
    | .b, .b => .b
    | _, _ => .u
  meet x y := match x, y with
    | .top, z | z, .top => z
    | .u, z | z, .u => z
    | .bot, _ | _, .bot => .bot
    | .a, .a => .a
    | .b, .b => .b
    | _, _ => .bot
  bot := .bot
  top := .top
  le_refl := fun x => by cases x <;> rfl
  le_trans := fun x y z => by cases x <;> cases y <;> cases z <;> decide
  le_antisymm := fun x y => by cases x <;> cases y <;> decide
  bot_le := fun x => by cases x <;> rfl
  le_top := fun x => by cases x <;> decide
  le_join_left := fun x y => by cases x <;> cases y <;> decide
  le_join_right := fun x y => by cases x <;> cases y <;> decide
  join_le := fun x y z => by cases x <;> cases y <;> cases z <;> decide
  meet_le_left := fun x y => by cases x <;> cases y <;> decide
  meet_le_right := fun x y => by cases x <;> cases y <;> decide
  le_meet := fun x y z => by cases x <;> cases y <;> cases z <;> decide

def B2Plus1Grading : B2Plus1Lat.Grading where
  rk | .bot => 0 | .a => 1 | .b => 1 | .u => 2 | .top => 3
  rk_bot := rfl
  rk_covers := fun x y h => by
    have hb : B2Plus1Lat.coversB x y = true := (B2Plus1Lat.coversB_iff x y).mpr h
    cases x <;> cases y <;> revert hb <;> decide

inductive OnePlusB2 | bot | u | a | b | top deriving DecidableEq, Repr

def OnePlusB2Lat : FinLattice OnePlusB2 where
  elems := [.bot, .u, .a, .b, .top]
  elems_nodup := by decide
  elems_complete := fun x => by cases x <;> decide
  le x y := match x, y with
    | .bot, _ => true
    | _, .top => true
    | .u, .u | .u, .a | .u, .b => true
    | .a, .a => true
    | .b, .b => true
    | _, _ => false
  join x y := match x, y with
    | .bot, z | z, .bot => z
    | .u, z | z, .u => z
    | .top, _ | _, .top => .top
    | .a, .a => .a
    | .b, .b => .b
    | _, _ => .top
  meet x y := match x, y with
    | .top, z | z, .top => z
    | .bot, _ | _, .bot => .bot
    | .a, .a => .a
    | .b, .b => .b
    | _, _ => .u
  bot := .bot
  top := .top
  le_refl := fun x => by cases x <;> rfl
  le_trans := fun x y z => by cases x <;> cases y <;> cases z <;> decide
  le_antisymm := fun x y => by cases x <;> cases y <;> decide
  bot_le := fun x => by cases x <;> rfl
  le_top := fun x => by cases x <;> decide
  le_join_left := fun x y => by cases x <;> cases y <;> decide
  le_join_right := fun x y => by cases x <;> cases y <;> decide
  join_le := fun x y z => by cases x <;> cases y <;> cases z <;> decide
  meet_le_left := fun x y => by cases x <;> cases y <;> decide
  meet_le_right := fun x y => by cases x <;> cases y <;> decide
  le_meet := fun x y z => by cases x <;> cases y <;> cases z <;> decide

def OnePlusB2Grading : OnePlusB2Lat.Grading where
  rk | .bot => 0 | .u => 1 | .a => 2 | .b => 2 | .top => 3
  rk_bot := rfl
  rk_covers := fun x y h => by
    have hb : OnePlusB2Lat.coversB x y = true := (OnePlusB2Lat.coversB_iff x y).mpr h
    cases x <;> cases y <;> revert hb <;> decide

/-! ### 6.6 Six-Element Lattice `N₅ ⊕ 1` (`bot ⋖ a ⋖ u ⋖ top`, `bot ⋖ b ⋖ c ⋖ u`) -/

inductive N5Plus1 | bot | a | b | c | u | top deriving DecidableEq, Repr

def N5Plus1Lat : FinLattice N5Plus1 where
  elems := [.bot, .a, .b, .c, .u, .top]
  elems_nodup := by decide
  elems_complete := fun x => by cases x <;> decide
  le x y := match x, y with
    | .bot, _ => true
    | _, .top => true
    | .a, .u | .b, .u | .c, .u | .u, .u => true
    | .a, .a => true
    | .b, .b | .b, .c => true
    | .c, .c => true
    | _, _ => false
  join x y := match x, y with
    | .bot, z | z, .bot => z
    | .top, _ | _, .top => .top
    | .a, .a => .a
    | .b, .b => .b
    | .b, .c | .c, .b | .c, .c => .c
    | _, _ => .u
  meet x y := match x, y with
    | .top, z | z, .top => z
    | .u, z | z, .u => z
    | .bot, _ | _, .bot => .bot
    | .a, .a => .a
    | .c, .c => .c
    | .b, .b | .b, .c | .c, .b => .b
    | _, _ => .bot
  bot := .bot
  top := .top
  le_refl := fun x => by cases x <;> rfl
  le_trans := fun x y z => by cases x <;> cases y <;> cases z <;> decide
  le_antisymm := fun x y => by cases x <;> cases y <;> decide
  bot_le := fun x => by cases x <;> rfl
  le_top := fun x => by cases x <;> decide
  le_join_left := fun x y => by cases x <;> cases y <;> decide
  le_join_right := fun x y => by cases x <;> cases y <;> decide
  join_le := fun x y z => by cases x <;> cases y <;> cases z <;> decide
  meet_le_left := fun x y => by cases x <;> cases y <;> decide
  meet_le_right := fun x y => by cases x <;> cases y <;> decide
  le_meet := fun x y z => by cases x <;> cases y <;> cases z <;> decide

def N5Plus1Idx : Fin 6 → N5Plus1
  | ⟨0, _⟩ => .bot | ⟨1, _⟩ => .a | ⟨2, _⟩ => .b
  | ⟨3, _⟩ => .c   | ⟨4, _⟩ => .u | ⟨5, _⟩ => .top

/-- Shortest covering-chain height from `0̂` on `N₅ ⊕ 1`:
    `bot ↦ 0`, `a, b ↦ 1`, `c, u ↦ 2` (`bot ⋖ a ⋖ u` and `bot ⋖ b ⋖ c`), `top ↦ 3`. -/
def N5Plus1MinHeight : N5Plus1 → Nat
  | .bot => 0 | .a => 1 | .b => 1 | .c => 2 | .u => 2 | .top => 3

/-! ### 6.7 Seven-Element Graded Lattice `Lat7` (`bot ⋖ p, q ⋖ u ⋖ top`, `bot ⋖ r ⋖ v ⋖ top`) -/

inductive Lat7 | bot | p | q | r | u | v | top deriving DecidableEq, Repr

def Lat7Inst : FinLattice Lat7 where
  elems := [.bot, .p, .q, .r, .u, .v, .top]
  elems_nodup := by decide
  elems_complete := fun x => by cases x <;> decide
  le x y := match x, y with
    | .bot, _ => true
    | _, .top => true
    | .p, .p | .p, .u => true
    | .q, .q | .q, .u => true
    | .r, .r | .r, .v => true
    | .u, .u => true
    | .v, .v => true
    | _, _ => false
  join x y := match x, y with
    | .bot, z | z, .bot => z
    | .top, _ | _, .top => .top
    | .p, .p => .p
    | .q, .q => .q
    | .r, .r => .r
    | .u, .u => .u
    | .v, .v => .v
    | .p, .q | .q, .p | .p, .u | .u, .p | .q, .u | .u, .q => .u
    | .r, .v | .v, .r => .v
    | _, _ => .top
  meet x y := match x, y with
    | .top, z | z, .top => z
    | .bot, _ | _, .bot => .bot
    | .p, .p | .p, .u | .u, .p => .p
    | .q, .q | .q, .u | .u, .q => .q
    | .r, .r | .r, .v | .v, .r => .r
    | .u, .u => .u
    | .v, .v => .v
    | _, _ => .bot
  bot := .bot
  top := .top
  le_refl := fun x => by cases x <;> rfl
  le_trans := fun x y z => by cases x <;> cases y <;> cases z <;> decide
  le_antisymm := fun x y => by cases x <;> cases y <;> decide
  bot_le := fun x => by cases x <;> rfl
  le_top := fun x => by cases x <;> decide
  le_join_left := fun x y => by cases x <;> cases y <;> decide
  le_join_right := fun x y => by cases x <;> cases y <;> decide
  join_le := fun x y z => by cases x <;> cases y <;> cases z <;> decide
  meet_le_left := fun x y => by cases x <;> cases y <;> decide
  meet_le_right := fun x y => by cases x <;> cases y <;> decide
  le_meet := fun x y z => by cases x <;> cases y <;> cases z <;> decide

def Lat7Grading : Lat7Inst.Grading where
  rk | .bot => 0 | .p => 1 | .q => 1 | .r => 1 | .u => 2 | .v => 2 | .top => 3
  rk_bot := rfl
  rk_covers := fun x y h => by
    have hb : Lat7Inst.coversB x y = true := (Lat7Inst.coversB_iff x y).mpr h
    cases x <;> cases y <;> revert hb <;> decide

/-! ## Section 7: Non-Vacuity Witnesses and Complete Refutation Theorems -/

/-! ### 7.1 Non-Vacuity Witnesses (`C₃`, `B₂`, `M₃`) -/

theorem nonvacuous_C3 :
    C3Lat.card = 3 ∧
    C3Lat.IsDistributive ∧
    C3Lat.IsModular ∧
    C3Lat.GloballyUniform ∧
    C3Lat.InteriorUniform ∧
    C3Lat.RankUniform C3Grading ∧
    C3Lat.WhitneySymmetric C3Grading ∧
    C3Lat.RankCoveringSymmetric C3Grading ∧
    C3Lat.CoveringMultisetSymmetric := by
  refine ⟨rfl, ?_, C3Lat.distributive_implies_modular ?_,
          C3Lat.all_card_le_3_globally_uniform (by decide), ?_, ?_, ?_, ?_, ?_⟩
  · intro x y z; cases x <;> cases y <;> cases z <;> rfl
  · intro x y z; cases x <;> cases y <;> cases z <;> rfl
  · constructor <;> (intro x y hx hy; cases x <;> cases y <;> simp [FinLattice.IsInterior, C3Lat] at hx hy <;> rfl)
  · constructor <;> (intro x y h; cases x <;> cases y <;> revert h <;> decide)
  · decide
  · intro x y h; cases x <;> cases y <;> revert h <;> decide
  · intro d
    match d with
    | 0 | 1 | 2 => decide
    | d + 3 => rfl

theorem nonvacuous_B2_rank_uniform :
    B2Lat.card = 4 ∧
    B2Lat.IsDistributive ∧
    B2Lat.IsModular ∧
    B2Lat.InteriorUniform ∧
    B2Lat.RankUniform B2Grading ∧
    B2Lat.WhitneySymmetric B2Grading ∧
    B2Lat.RankCoveringSymmetric B2Grading ∧
    B2Lat.CoveringMultisetSymmetric := by
  have hdist : B2Lat.IsDistributive := fun x y z => by
    cases x <;> cases y <;> cases z <;> rfl
  refine ⟨rfl, hdist, B2Lat.distributive_implies_modular hdist, ?_, ?_, ?_, ?_, ?_⟩
  · constructor <;> (intro x y hx hy; cases x <;> cases y <;>
      simp [FinLattice.IsInterior, B2Lat] at hx hy <;> decide)
  · constructor <;> (intro x y h; cases x <;> cases y <;> revert h <;> decide)
  · decide
  · intro x y h; cases x <;> cases y <;> revert h <;> decide
  · intro d
    match d with
    | 0 | 1 | 2 | 3 => decide
    | d + 4 => rfl

/-! ### 7.2 Refutation of Regime I (Global / Non-Extremal / Hasse-Regular / Parity Uniformity) -/

/-- Under global non-extremal covering uniformity, `B₂` (`card = 4 < 5`, distributive and
    modular!) fails BOTH upper uniformity (`c⁺(0̂) = 2 ≠ 1 = c⁺(a)`) and lower uniformity
    (`c⁻(1̂) = 2 ≠ 1 = c⁻(a)`), while all lattices of cardinality `≤ 3` satisfy it. Thus
    the minimal counterexample has size `4` and is modular, refuting Clause 2. -/
theorem disproof_global_minimal_counterexample :
    (∀ {α : Type} [DecidableEq α] (L : FinLattice α), L.card ≤ 3 → L.GloballyUniform) ∧
    B2Lat.card = 4 ∧
    B2Lat.card < 5 ∧
    B2Lat.IsDistributive ∧
    B2Lat.IsModular ∧
    ¬B2Lat.GloballyUpperUniform ∧
    ¬B2Lat.GloballyLowerUniform ∧
    ¬B2Lat.GloballyUniform := by
  have hdist : B2Lat.IsDistributive := fun x y z => by
    cases x <;> cases y <;> cases z <;> rfl
  have hnup : ¬B2Lat.GloballyUpperUniform := by
    intro h
    have h1 := h .bot .a (by decide) (by decide)
    revert h1; decide
  have hnlo : ¬B2Lat.GloballyLowerUniform := by
    intro h
    have h1 := h .top .a (by decide) (by decide)
    revert h1; decide
  exact ⟨fun L hle => L.all_card_le_3_globally_uniform hle,
         rfl, by decide, hdist, B2Lat.distributive_implies_modular hdist,
         hnup, hnlo, fun h => hnup h.1⟩

/-- Even at cardinality `5`, the modular diamond `M₃` (`IsModular`, `¬ IsDistributive`)
    also fails global uniformity (`c⁺(0̂) = 3 ≠ 1 = c⁺(a)`), so `N₅` is not unique at size `5` either. -/
theorem M3_modular_fails_global_uniformity :
    M3Lat.card = 5 ∧ M3Lat.IsModular ∧ ¬M3Lat.IsDistributive ∧ ¬M3Lat.GloballyUniform := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro x y z h; cases x <;> cases y <;> cases z <;> revert h <;> decide
  · intro hd
    have h := hd .a .b .c
    revert h; decide
  · intro ⟨hup, _⟩
    have h := hup .bot .a (by decide) (by decide)
    revert h; decide

/-- Refutation of ancillary Regime I variants:
    - Unrestricted constancy on `L`: fails at `C₂` (`card = 2 < 5`, modular);
    - Undirected Hasse regularity: fails at `C₃` (`card = 3 < 5`, modular), whereas `N₅` IS `2`-regular;
    - Literal arithmetic parity (`2 ∣ c⁺`): fails at `C₂` (`card = 2 < 5`, modular). -/
theorem disproof_ancillary_global_variants :
    (C2Lat.card = 2 ∧ C2Lat.IsModular ∧ ¬C2Lat.UnrestrictedUpperUniform ∧ ¬C2Lat.ParityEvenUpper) ∧
    (C3Lat.card = 3 ∧ C3Lat.IsModular ∧ ¬C3Lat.HasseRegular) ∧
    N5Lat.HasseRegular := by
  refine ⟨⟨rfl, ?_, ?_, ?_⟩, ⟨rfl, ?_, ?_⟩, ?_⟩
  · intro x y z h; cases x <;> cases y <;> cases z <;> revert h <;> decide
  · intro h; have h1 := h .bot .top; revert h1; decide
  · intro h; have h1 := h .bot (by decide); revert h1; decide
  · intro x y z h; cases x <;> cases y <;> cases z <;> revert h <;> decide
  · intro h; have h1 := h .bot .mid; revert h1; decide
  · intro x y; cases x <;> cases y <;> decide

/-! ### 7.3 Properties of `N₅` and Refutation of Regime II (Strict Interior Uniformity) -/

/-- `N₅` has cardinality `5`, is nonmodular (`b ≤ c` yet `b ∨ (a ∧ c) = b ≠ c = (b ∨ a) ∧ c`),
    and admits NO grading (`bot ⋖ a ⋖ top` forces `rk(top) = 2` while `bot ⋖ b ⋖ c ⋖ top`
    forces `rk(top) = 3`). -/
theorem N5_nonmodular_and_nongraded :
    N5Lat.card = 5 ∧ ¬N5Lat.IsModular ∧ ¬Nonempty N5Lat.Grading ∧ ¬N5Lat.IsRankUniform := by
  have hnmod : ¬N5Lat.IsModular := by
    intro hmod
    have h := hmod .b .a .c rfl
    revert h; decide
  have hngrad : ¬Nonempty N5Lat.Grading := by
    rintro ⟨g⟩
    have hc1 : N5Lat.Covers .bot .a := (N5Lat.coversB_iff .bot .a).mp (by decide)
    have hc2 : N5Lat.Covers .a .top := (N5Lat.coversB_iff .a .top).mp (by decide)
    have hc3 : N5Lat.Covers .bot .b := (N5Lat.coversB_iff .bot .b).mp (by decide)
    have hc4 : N5Lat.Covers .b .c   := (N5Lat.coversB_iff .b .c).mp (by decide)
    have hc5 : N5Lat.Covers .c .top := (N5Lat.coversB_iff .c .top).mp (by decide)
    have hbot0 : g.rk .bot = 0 := g.rk_bot
    have htop2 : g.rk .top = 2 := by
      rw [g.rk_covers .a .top hc2, g.rk_covers .bot .a hc1, hbot0]
    have htop3 : g.rk .top = 3 := by
      rw [g.rk_covers .c .top hc5, g.rk_covers .b .c hc4, g.rk_covers .bot .b hc3, hbot0]
    omega
  exact ⟨rfl, hnmod, hngrad, fun ⟨g, _⟩ => hngrad ⟨g⟩⟩

/-- Refutation of Regime II (Strict interior uniformity on `L \ {0̂, 1̂}`):
    1. `N₅` SATISFIES `InteriorUniform` (`c⁺(x) = c⁻(x) = 1` for all `x ∈ {a, b, c}`), so `N₅`
       is NOT a counterexample to interior uniformity at all!
    2. Meanwhile, the 5-element DISTRIBUTIVE (hence MODULAR) lattices `B₂ ⊕ 1` and `1 ⊕ B₂`
       DO fail `InteriorUniform` (`B₂ ⊕ 1` is `InteriorUpperUniform` yet `¬ InteriorLowerUniform`,
       and `1 ⊕ B₂` is `InteriorLowerUniform` yet `¬ InteriorUpperUniform`).
    3. Moreover, `N₅` has `tr(A⁵) = 10 ≠ 0`, so its Hasse adjacency eigenvalue spectrum is NOT
       symmetric about `0`. -/
theorem disproof_interior_uniformity :
    N5Lat.InteriorUniform ∧
    matTrace (matPow (hasseAdj N5Lat N5Idx) 5) = 10 ∧
    (B2Plus1Lat.card = 5 ∧ B2Plus1Lat.IsDistributive ∧ B2Plus1Lat.IsModular ∧
      B2Plus1Lat.InteriorUpperUniform ∧ ¬B2Plus1Lat.InteriorLowerUniform ∧
      ¬B2Plus1Lat.InteriorUniform) ∧
    (OnePlusB2Lat.card = 5 ∧ OnePlusB2Lat.IsDistributive ∧ OnePlusB2Lat.IsModular ∧
      OnePlusB2Lat.InteriorLowerUniform ∧ ¬OnePlusB2Lat.InteriorUpperUniform ∧
      ¬OnePlusB2Lat.InteriorUniform) := by
  have hn5_int : N5Lat.InteriorUniform := by
    constructor <;> (intro x y hx hy; cases x <;> cases y <;>
      simp [FinLattice.IsInterior, N5Lat] at hx hy <;> decide)
  have hb2_dist : B2Plus1Lat.IsDistributive := fun x y z => by
    cases x <;> cases y <;> cases z <;> rfl
  have hb2_iup : B2Plus1Lat.InteriorUpperUniform := by
    intro x y hx hy; cases x <;> cases y <;>
      simp [FinLattice.IsInterior, B2Plus1Lat] at hx hy <;> decide
  have hb2_nilo : ¬B2Plus1Lat.InteriorLowerUniform := by
    intro h
    have h1 := h .a .u ⟨by decide, by decide⟩ ⟨by decide, by decide⟩
    revert h1; decide
  have hob2_dist : OnePlusB2Lat.IsDistributive := fun x y z => by
    cases x <;> cases y <;> cases z <;> rfl
  have hob2_ilo : OnePlusB2Lat.InteriorLowerUniform := by
    intro x y hx hy; cases x <;> cases y <;>
      simp [FinLattice.IsInterior, OnePlusB2Lat] at hx hy <;> decide
  have hob2_niup : ¬OnePlusB2Lat.InteriorUpperUniform := by
    intro h
    have h1 := h .u .a ⟨by decide, by decide⟩ ⟨by decide, by decide⟩
    revert h1; decide
  exact ⟨hn5_int, by decide,
    ⟨rfl, hb2_dist, B2Plus1Lat.distributive_implies_modular hb2_dist,
     hb2_iup, hb2_nilo, fun h => hb2_nilo h.2⟩,
    ⟨rfl, hob2_dist, OnePlusB2Lat.distributive_implies_modular hob2_dist,
     hob2_ilo, hob2_niup, fun h => hob2_niup h.1⟩⟩

/-! ### 7.4 Refutation of Regime III (Graded Rank-Wise Uniformity — Terwilliger Uniform Lattices) -/

/-- Refutation of Clause 1 for Whitney / rank-size spectra and rank-covering profiles:
    `B₂ ⊕ 1` (`card = 5`, distributive and modular) is BOTH rank-upper-uniform AND
    rank-lower-uniform, yet its Whitney spectrum `[1, 2, 1, 1]` is NOT symmetric
    (`[1, 2, 1, 1] ≠ [1, 1, 2, 1]`) and its rank-covering profile is NOT top-bottom symmetric
    (`rk(0̂) + rk(1̂) = 3` yet `c⁺(0̂) = 2 ≠ 1 = c⁻(1̂)`). Moreover, by `grading_unique`, this holds
    for EVERY grading `g` on `B₂ ⊕ 1`. -/
theorem disproof_rank_uniform_whitney_and_profile :
    B2Plus1Lat.card = 5 ∧
    B2Plus1Lat.IsDistributive ∧
    B2Plus1Lat.IsModular ∧
    B2Plus1Lat.RankUpperUniform B2Plus1Grading ∧
    B2Plus1Lat.RankLowerUniform B2Plus1Grading ∧
    B2Plus1Lat.whitneySpectrum B2Plus1Grading = [1, 2, 1, 1] ∧
    ¬B2Plus1Lat.WhitneySymmetric B2Plus1Grading ∧
    ¬B2Plus1Lat.RankCoveringSymmetric B2Plus1Grading ∧
    (∀ g : B2Plus1Lat.Grading, ¬B2Plus1Lat.WhitneySymmetric g) := by
  have hdist : B2Plus1Lat.IsDistributive := fun x y z => by
    cases x <;> cases y <;> cases z <;> rfl
  have hrup : B2Plus1Lat.RankUpperUniform B2Plus1Grading := by
    intro x y h; cases x <;> cases y <;> revert h <;> decide
  have hrlo : B2Plus1Lat.RankLowerUniform B2Plus1Grading := by
    intro x y h; cases x <;> cases y <;> revert h <;> decide
  have hw_eq : B2Plus1Lat.whitneySpectrum B2Plus1Grading = [1, 2, 1, 1] := by decide
  have hnw : ¬B2Plus1Lat.WhitneySymmetric B2Plus1Grading := by decide
  have hnp : ¬B2Plus1Lat.RankCoveringSymmetric B2Plus1Grading := by
    intro h
    have h1 := h .bot .top rfl
    revert h1; decide
  have hall_g : ∀ g : B2Plus1Lat.Grading, ¬B2Plus1Lat.WhitneySymmetric g := by
    intro g
    have hfun : g.rk = B2Plus1Grading.rk := funext (B2Plus1Lat.grading_unique g B2Plus1Grading)
    have hspec : B2Plus1Lat.whitneySpectrum g = B2Plus1Lat.whitneySpectrum B2Plus1Grading := by
      unfold FinLattice.whitneySpectrum FinLattice.height FinLattice.whitneyNum
      simp [hfun]
    unfold FinLattice.WhitneySymmetric
    rw [hspec]
    exact hnw
  exact ⟨rfl, hdist, B2Plus1Lat.distributive_implies_modular hdist,
         hrup, hrlo, hw_eq, hnw, hnp, hall_g⟩

/-- Refutation of Clause 1 for covering-degree multiset spectra and upper/lower uniformity symmetry:
    The 7-element graded lattice `Lat7` (`card = 7`, height `3`) is BOTH `RankUpperUniform`
    and `InteriorUpperUniform`, yet:
    1. `Lat7` is NOT `RankLowerUniform` (`rk(u) = rk(v) = 2`, `c⁻(u) = 2 ≠ 1 = c⁻(v)`),
    2. its Whitney spectrum `[1, 3, 2, 1]` is NOT palindromic, and
    3. its upper covering-degree multiset `{0, 1, 1, 1, 1, 1, 3}` and lower covering-degree
       multiset `{0, 1, 1, 1, 1, 2, 2}` are NOT equal (`upperDegCount 3 = 1 ≠ 0 = lowerDegCount 3`
       and `upperDegCount 2 = 0 ≠ 2 = lowerDegCount 2`). -/
theorem disproof_rank_upper_uniform_multiset :
    Lat7Inst.card = 7 ∧
    Lat7Inst.RankUpperUniform Lat7Grading ∧
    Lat7Inst.InteriorUpperUniform ∧
    ¬Lat7Inst.RankLowerUniform Lat7Grading ∧
    Lat7Inst.whitneySpectrum Lat7Grading = [1, 3, 2, 1] ∧
    ¬Lat7Inst.WhitneySymmetric Lat7Grading ∧
    Lat7Inst.upperDegCount 3 = 1 ∧
    Lat7Inst.lowerDegCount 3 = 0 ∧
    ¬Lat7Inst.CoveringMultisetSymmetric := by
  have hrup : Lat7Inst.RankUpperUniform Lat7Grading := by
    intro x y h; cases x <;> cases y <;> revert h <;> decide
  have hiup : Lat7Inst.InteriorUpperUniform := by
    intro x y hx hy; cases x <;> cases y <;>
      simp [FinLattice.IsInterior, Lat7Inst] at hx hy <;> decide
  have hnrlo : ¬Lat7Inst.RankLowerUniform Lat7Grading := by
    intro h
    have h1 := h .u .v rfl
    revert h1; decide
  have hnms : ¬Lat7Inst.CoveringMultisetSymmetric := by
    intro h
    have h3 := h 3
    revert h3; decide
  exact ⟨rfl, hrup, hiup, hnrlo, by decide, by decide, by decide, by decide, hnms⟩

/-- Refutation of shortest-chain height layer uniformity + Hasse graph eigenvalue symmetry:
    In `N₅ ⊕ 1` (`card = 6`), upper covering numbers are constant on every shortest-chain
    height layer from `0̂`, yet its undirected Hasse adjacency matrix `A` has `tr(A⁵) = 10 ≠ 0`
    (owing to its 5-cycle `bot - a - u - c - b - bot`), so its eigenvalue spectrum is not
    symmetric about `0`. -/
theorem disproof_min_height_hasse_spectrum :
    N5Plus1Lat.card = 6 ∧
    (∀ x y : N5Plus1, N5Plus1MinHeight x = N5Plus1MinHeight y →
      N5Plus1Lat.upperCovNum x = N5Plus1Lat.upperCovNum y) ∧
    matTrace (matPow (hasseAdj N5Plus1Lat N5Plus1Idx) 5) = 10 := by
  refine ⟨rfl, ?_, by decide⟩
  intro x y h
  cases x <;> cases y <;> revert h <;> decide

/-! ### 7.5 Master Disproof Theorem Combining All Canonical Interpretations -/

/-- Master Disproof of Conjecture 00000008545:
    1. Under global covering uniformity, the minimal counterexample isNOT a 5-element
       nonmodular lattice: every lattice of size `≤ 3` is uniform, while `B₂` (size `4`,
       modular/distributive) fails uniformity.
    2. Under strict interior covering uniformity, `N₅` does NOT fail uniformity at all, while
       the 5-element modular/distributive lattices `B₂ ⊕ 1` and `1 ⊕ B₂` DO fail it.
    3. Under graded rank-wise uniformity (where `N₅` IS the minimal counterexample to
       uniformity), upper and lower uniform lattices do NOT have symmetric spectra: `B₂ ⊕ 1`
       (both rank-upper- and rank-lower-uniform) has asymmetric Whitney spectrum `[1, 2, 1, 1]`
       and asymmetric rank-covering profile, while `Lat7` (rank-upper-uniform) even has
       unequal upper and lower covering-degree multisets. -/
theorem conjecture_00000008545_false :
    -- (I) Global uniformity fails at size 4 on a modular lattice (refuting Clause 2)
    (∃ L : FinLattice B2, L.card = 4 ∧ L.IsModular ∧ ¬L.GloballyUniform) ∧
    -- (II) Strict interior uniformity holds on N5 yet fails on modular 5-element lattices (refuting Clause 2)
    (N5Lat.InteriorUniform ∧
      ∃ L : FinLattice B2Plus1, L.card = 5 ∧ L.IsModular ∧ ¬L.InteriorUniform) ∧
    -- (III) Graded rank-uniformity admits upper/lower uniform lattices with asymmetric Whitney,
    --       rank-profile, and covering-multiset spectra (refuting Clause 1)
    (∃ (L : FinLattice B2Plus1) (g : L.Grading),
      L.RankUpperUniform g ∧ L.RankLowerUniform g ∧
      ¬L.WhitneySymmetric g ∧ ¬L.RankCoveringSymmetric g) ∧
    (∃ (L : FinLattice Lat7) (g : L.Grading),
      L.RankUpperUniform g ∧ ¬L.RankLowerUniform g ∧
      ¬L.WhitneySymmetric g ∧ ¬L.CoveringMultisetSymmetric) := by
  exact ⟨
    ⟨B2Lat, rfl, disproof_global_minimal_counterexample.2.2.2.2.1,
     disproof_global_minimal_counterexample.2.2.2.2.2.2.2⟩,
    ⟨disproof_interior_uniformity.1,
     ⟨B2Plus1Lat, rfl, disproof_interior_uniformity.2.2.1.2.2.1,
      disproof_interior_uniformity.2.2.1.2.2.2.2.2⟩⟩,
    ⟨B2Plus1Lat, B2Plus1Grading,
     disproof_rank_uniform_whitney_and_profile.2.2.2.1,
     disproof_rank_uniform_whitney_and_profile.2.2.2.2.1,
     disproof_rank_uniform_whitney_and_profile.2.2.2.2.2.2.1,
     disproof_rank_uniform_whitney_and_profile.2.2.2.2.2.2.2.1⟩,
    ⟨Lat7Inst, Lat7Grading,
     disproof_rank_upper_uniform_multiset.2.1,
     disproof_rank_upper_uniform_multiset.2.2.2.1,
     disproof_rank_upper_uniform_multiset.2.2.2.2.2.1,
     disproof_rank_upper_uniform_multiset.2.2.2.2.2.2.2.2⟩
  ⟩

end Conjecture00000008545

/-! ## Axiom Audit -/
#print axioms Conjecture00000008545.FinLattice.distributive_implies_modular
#print axioms Conjecture00000008545.FinLattice.grading_unique
#print axioms Conjecture00000008545.FinLattice.all_card_le_3_globally_uniform
#print axioms Conjecture00000008545.nonvacuous_C3
#print axioms Conjecture00000008545.nonvacuous_B2_rank_uniform
#print axioms Conjecture00000008545.disproof_global_minimal_counterexample
#print axioms Conjecture00000008545.M3_modular_fails_global_uniformity
#print axioms Conjecture00000008545.disproof_ancillary_global_variants
#print axioms Conjecture00000008545.N5_nonmodular_and_nongraded
#print axioms Conjecture00000008545.disproof_interior_uniformity
#print axioms Conjecture00000008545.disproof_rank_uniform_whitney_and_profile
#print axioms Conjecture00000008545.disproof_rank_upper_uniform_multiset
#print axioms Conjecture00000008545.disproof_min_height_hasse_spectrum
#print axioms Conjecture00000008545.conjecture_00000008545_false
