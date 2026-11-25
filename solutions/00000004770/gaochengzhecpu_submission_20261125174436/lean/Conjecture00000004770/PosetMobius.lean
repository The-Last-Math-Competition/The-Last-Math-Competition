namespace Conjecture00000004770

/-!
# Finite Posets, Lattices, Isomorphisms, and Two-Variable Möbius Theory

Self-contained Core Lean 4.19.0 development of finite posets, join/meet semilattices,
lattices, poset/lattice isomorphisms, the incidence algebra, existence and uniqueness
of the two-variable Möbius function `μ(x, y)`, Möbius inversion, order-dual symmetry,
and isomorphism invariance of both lower-interval and full-interval Möbius spectra.
-/

/-- Universal boolean quantifier over `Fin n`. -/
def finAll : (n : Nat) → (Fin n → Bool) → Bool
  | 0, _ => true
  | n + 1, p => p ⟨0, Nat.zero_lt_succ n⟩ && finAll n (fun i => p ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)

/-- Existential boolean quantifier over `Fin n`. -/
def finAny : (n : Nat) → (Fin n → Bool) → Bool
  | 0, _ => false
  | n + 1, p => p ⟨0, Nat.zero_lt_succ n⟩ || finAny n (fun i => p ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)

/-- Cardinality of `{i : Fin n | p i = true}`. -/
def finCount : (n : Nat) → (Fin n → Bool) → Nat
  | 0, _ => 0
  | n + 1, p =>
      (if p ⟨0, Nat.zero_lt_succ n⟩ then 1 else 0) +
      finCount n (fun i => p ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)

/-- Exact integer sum `∑_{i : Fin n} f(i)`. -/
def finSum : (n : Nat) → (Fin n → Int) → Int
  | 0, _ => 0
  | n + 1, f =>
      f ⟨0, Nat.zero_lt_succ n⟩ +
      finSum n (fun i => f ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)

theorem finAll_eq_true {n : Nat} {p : Fin n → Bool} :
    finAll n p = true ↔ ∀ i : Fin n, p i = true := by
  induction n with
  | zero =>
    constructor
    · intro _ i; exact nomatch i
    · intro _; rfl
  | succ n ih =>
    simp only [finAll, Bool.and_eq_true, ih]
    constructor
    · intro ⟨h0, hrest⟩ ⟨k, hk⟩
      cases k with
      | zero => exact h0
      | succ k' => exact hrest ⟨k', Nat.lt_of_succ_lt_succ hk⟩
    · intro h
      exact ⟨h ⟨0, Nat.zero_lt_succ n⟩, fun i => h ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩⟩

theorem finForall_decide {n : Nat} {P : Fin n → Prop} [DecidablePred P]
    (h : finAll n (fun i => decide (P i)) = true) : ∀ i : Fin n, P i :=
  fun i => of_decide_eq_true (finAll_eq_true.mp h i)

theorem finForall2_decide {n m : Nat} {P : Fin n → Fin m → Prop}
    [∀ i j, Decidable (P i j)]
    (h : finAll n (fun i => finAll m (fun j => decide (P i j))) = true) :
    ∀ (i : Fin n) (j : Fin m), P i j :=
  fun i j => of_decide_eq_true (finAll_eq_true.mp (finAll_eq_true.mp h i) j)

theorem finForall3_decide {n m k : Nat} {P : Fin n → Fin m → Fin k → Prop}
    [∀ i j l, Decidable (P i j l)]
    (h : finAll n (fun i => finAll m (fun j => finAll k (fun l => decide (P i j l)))) = true) :
    ∀ (i : Fin n) (j : Fin m) (l : Fin k), P i j l :=
  fun i j l => of_decide_eq_true (finAll_eq_true.mp (finAll_eq_true.mp (finAll_eq_true.mp h i) j) l)

theorem finAny_eq_true {n : Nat} {p : Fin n → Bool} :
    finAny n p = true ↔ ∃ i : Fin n, p i = true := by
  induction n with
  | zero =>
    constructor
    · intro h; exact nomatch h
    · intro ⟨i, _⟩; exact nomatch i
  | succ n ih =>
    simp only [finAny, Bool.or_eq_true, ih]
    constructor
    · intro h
      cases h with
      | inl h0 => exact ⟨⟨0, Nat.zero_lt_succ n⟩, h0⟩
      | inr hrest =>
        rcases hrest with ⟨i, hi⟩
        exact ⟨⟨i.1 + 1, Nat.succ_lt_succ i.2⟩, hi⟩
    · intro ⟨⟨k, hk⟩, hp⟩
      cases k with
      | zero => exact Or.inl hp
      | succ k' => exact Or.inr ⟨⟨k', Nat.lt_of_succ_lt_succ hk⟩, hp⟩

theorem finCount_le : ∀ (n : Nat) (p : Fin n → Bool), finCount n p ≤ n
  | 0, _ => Nat.le_refl 0
  | n + 1, p => by
    simp only [finCount]
    have ih := finCount_le n (fun i => p ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)
    split <;> omega

theorem finCount_mono : ∀ {n : Nat} {p q : Fin n → Bool},
    (∀ i, p i = true → q i = true) → finCount n p ≤ finCount n q
  | 0, _, _, _ => Nat.le_refl 0
  | n + 1, p, q, h => by
    simp only [finCount]
    have ih := finCount_mono (fun i => h ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)
    have h0 := h ⟨0, Nat.zero_lt_succ n⟩
    cases hp : p ⟨0, Nat.zero_lt_succ n⟩ <;> cases hq : q ⟨0, Nat.zero_lt_succ n⟩
    · simp only [Bool.false_eq_true, ↓reduceIte]; omega
    · simp only [Bool.false_eq_true, ↓reduceIte]; omega
    · exfalso; exact Bool.noConfusion (hq.symm.trans (h0 hp))
    · simp only [↓reduceIte]; omega

theorem finCount_strict_mono : ∀ {n : Nat} {p q : Fin n → Bool} (i₀ : Fin n),
    (∀ i, p i = true → q i = true) →
    p i₀ = false → q i₀ = true →
    finCount n p + 1 ≤ finCount n q
  | 0, _, _, i₀, _, _, _ => nomatch i₀
  | n + 1, p, q, ⟨0, _⟩, h, hp0, hq0 => by
    simp only [finCount, hp0, hq0, Bool.false_eq_true, ↓reduceIte]
    have ih := finCount_mono (fun i => h ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)
    omega
  | n + 1, p, q, ⟨k + 1, hk⟩, h, hpk, hqk => by
    simp only [finCount]
    have ih := finCount_strict_mono ⟨k, Nat.lt_of_succ_lt_succ hk⟩
      (fun i => h ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩) hpk hqk
    have h0 := h ⟨0, Nat.zero_lt_succ n⟩
    cases hp : p ⟨0, Nat.zero_lt_succ n⟩ <;> cases hq : q ⟨0, Nat.zero_lt_succ n⟩
    · simp only [Bool.false_eq_true, ↓reduceIte]; omega
    · simp only [Bool.false_eq_true, ↓reduceIte]; omega
    · exfalso; exact Bool.noConfusion (hq.symm.trans (h0 hp))
    · simp only [↓reduceIte]; omega

theorem finSum_congr : ∀ {n : Nat} {f g : Fin n → Int},
    (∀ i, f i = g i) → finSum n f = finSum n g
  | 0, _, _, _ => rfl
  | n + 1, f, g, h => by
    simp only [finSum]
    rw [h ⟨0, Nat.zero_lt_succ n⟩,
        finSum_congr (fun i => h ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)]

theorem finSum_zero : ∀ (n : Nat), finSum n (fun _ => 0) = 0
  | 0 => rfl
  | n + 1 => by simp [finSum, finSum_zero n]

theorem finSum_add : ∀ (n : Nat) (f g : Fin n → Int),
    finSum n (fun i => f i + g i) = finSum n f + finSum n g
  | 0, _, _ => by simp [finSum]
  | n + 1, f, g => by
    simp only [finSum, finSum_add n]
    omega

theorem finSum_mul_left : ∀ (n : Nat) (c : Int) (f : Fin n → Int),
    finSum n (fun i => c * f i) = c * finSum n f
  | 0, _, _ => by simp [finSum]
  | n + 1, c, f => by
    simp only [finSum, finSum_mul_left n, Int.mul_add]

theorem finSum_mul_right : ∀ (n : Nat) (f : Fin n → Int) (c : Int),
    finSum n (fun i => f i * c) = finSum n f * c
  | 0, _, _ => by simp [finSum]
  | n + 1, f, c => by
    simp only [finSum, finSum_mul_right n, Int.add_mul]

theorem finSum_comm : ∀ (n m : Nat) (f : Fin n → Fin m → Int),
    finSum n (fun i => finSum m (fun j => f i j)) =
    finSum m (fun j => finSum n (fun i => f i j))
  | 0, m, _ => by simp [finSum, finSum_zero m]
  | n + 1, m, f => by
    simp only [finSum]
    rw [finSum_comm n m, ← finSum_add]

theorem finSum_ite_eq : ∀ {n : Nat} (i₀ : Fin n) (f : Fin n → Int),
    finSum n (fun i => if i = i₀ then f i else 0) = f i₀
  | 0, i₀, _ => nomatch i₀
  | n + 1, ⟨0, _⟩, f => by
    simp only [finSum, ↓reduceIte]
    have hzero : finSum n (fun i : Fin n =>
        if (⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ : Fin (n + 1)) = ⟨0, Nat.zero_lt_succ n⟩
        then f ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ else 0) = 0 := by
      rw [finSum_congr (g := fun _ => 0)]
      · exact finSum_zero n
      · intro i
        have hne : (⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ : Fin (n + 1)) ≠ ⟨0, Nat.zero_lt_succ n⟩ := by
          intro heq
          have hval : i.1 + 1 = 0 := congrArg Fin.val heq
          omega
        simp [hne]
    rw [hzero]
    omega
  | n + 1, ⟨k + 1, hk⟩, f => by
    simp only [finSum]
    have hne0 : (⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1)) ≠ ⟨k + 1, hk⟩ := by
      intro heq
      have hval : 0 = k + 1 := congrArg Fin.val heq
      omega
    simp only [hne0, ↓reduceIte, Int.zero_add]
    have hsub : finSum n (fun i : Fin n =>
        if (⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ : Fin (n + 1)) = ⟨k + 1, hk⟩
        then f ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ else 0) =
        finSum n (fun i : Fin n =>
        if i = ⟨k, Nat.lt_of_succ_lt_succ hk⟩
        then f ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ else 0) := by
      apply finSum_congr
      intro i
      have heq_iff :
          ((⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ : Fin (n + 1)) = ⟨k + 1, hk⟩) ↔
          (i = ⟨k, Nat.lt_of_succ_lt_succ hk⟩) := by
        constructor
        · intro h
          apply Fin.ext
          have hval : i.1 + 1 = k + 1 := congrArg Fin.val h
          exact Nat.succ.inj hval
        · intro h
          apply Fin.ext
          have hval : i.1 = k := congrArg Fin.val h
          exact congrArg (· + 1) hval
      by_cases hi : i = ⟨k, Nat.lt_of_succ_lt_succ hk⟩
      · rw [if_pos (heq_iff.mpr hi), if_pos hi]
      · rw [if_neg (mt heq_iff.mp hi), if_neg hi]
    rw [hsub, finSum_ite_eq ⟨k, Nat.lt_of_succ_lt_succ hk⟩]

theorem finSum_split_eq {n : Nat} (i₀ : Fin n) (f : Fin n → Int) :
    finSum n f = f i₀ + finSum n (fun i => if decide (i ≠ i₀) then f i else 0) := by
  have h1 : finSum n f =
      finSum n (fun i => (if i = i₀ then f i else 0) + (if decide (i ≠ i₀) then f i else 0)) := by
    apply finSum_congr
    intro i
    by_cases h : i = i₀
    · subst h; simp
    · simp [h]
  rw [h1, finSum_add, finSum_ite_eq]

/-- Reindexing an integer sum along an explicit bijection `e : Fin n → Fin m`. -/
theorem finSum_bij {n m : Nat} (e : Fin n → Fin m) (eInv : Fin m → Fin n)
    (hleft : ∀ i, eInv (e i) = i) (hright : ∀ j, e (eInv j) = j)
    (f : Fin n → Int) (g : Fin m → Int) (hfg : ∀ i, f i = g (e i)) :
    finSum n f = finSum m g := by
  have h1 : finSum n f = finSum n (fun i => finSum m (fun j => if j = e i then g j else 0)) := by
    apply finSum_congr
    intro i
    rw [finSum_ite_eq (e i) g, hfg i]
  rw [h1, finSum_comm]
  apply finSum_congr
  intro j
  have h2 : finSum n (fun i => if j = e i then g j else 0) =
      finSum n (fun i => if i = eInv j then g j else 0) := by
    apply finSum_congr
    intro i
    have iff_eq : (j = e i) ↔ (i = eInv j) := by
      constructor
      · intro h; rw [h, hleft]
      · intro h; rw [h, hright]
    by_cases hi : i = eInv j
    · rw [if_pos (iff_eq.mpr hi), if_pos hi]
    · rw [if_neg (mt iff_eq.mp hi), if_neg hi]
  rw [h2, finSum_ite_eq (eInv j)]

theorem finCount_eq_int_sum {n : Nat} (p : Fin n → Bool) :
    (finCount n p : Int) = finSum n (fun i => if p i then 1 else 0) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [finCount, finSum]
    cases hp : p ⟨0, Nat.zero_lt_succ n⟩
    · simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add, Int.zero_add]
      exact ih _
    · simp only [↓reduceIte]
      have hcast : ((1 + finCount n (fun i => p ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩) : Nat) : Int) =
          1 + (finCount n (fun i => p ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩) : Int) := by omega
      rw [hcast, ih]

theorem finCount_bij {n m : Nat} (e : Fin n → Fin m) (eInv : Fin m → Fin n)
    (hleft : ∀ i, eInv (e i) = i) (hright : ∀ j, e (eInv j) = j)
    (p : Fin n → Bool) (q : Fin m → Bool) (hpq : ∀ i, p i = q (e i)) :
    finCount n p = finCount m q := by
  have hcast : (finCount n p : Int) = (finCount m q : Int) := by
    rw [finCount_eq_int_sum, finCount_eq_int_sum]
    exact finSum_bij e eInv hleft hright _ _ (fun i => by rw [hpq i])
  omega

/-- A finite poset on `Fin n` with decidable order relation `le`. -/
structure FinPoset (n : Nat) where
  le : Fin n → Fin n → Bool
  le_refl : ∀ x : Fin n, le x x = true
  le_antisymm : ∀ x y : Fin n, le x y = true → le y x = true → x = y
  le_trans : ∀ x y z : Fin n, le x y = true → le y z = true → le x z = true

namespace FinPoset

/-- The order-dual poset `P^op`. -/
def dual {n : Nat} (P : FinPoset n) : FinPoset n where
  le x y := P.le y x
  le_refl x := P.le_refl x
  le_antisymm x y hxy hyx := P.le_antisymm x y hyx hxy
  le_trans x y z hxy hyz := P.le_trans z y x hyz hxy

@[simp] theorem dual_le {n : Nat} (P : FinPoset n) (x y : Fin n) :
    P.dual.le x y = P.le y x := rfl

def IsUpperBound {n : Nat} (P : FinPoset n) (x y u : Fin n) : Prop :=
  P.le x u = true ∧ P.le y u = true

def IsLeastUpperBound {n : Nat} (P : FinPoset n) (x y u : Fin n) : Prop :=
  IsUpperBound P x y u ∧ ∀ w : Fin n, IsUpperBound P x y w → P.le u w = true

def IsLowerBound {n : Nat} (P : FinPoset n) (x y l : Fin n) : Prop :=
  P.le l x = true ∧ P.le l y = true

def IsGreatestLowerBound {n : Nat} (P : FinPoset n) (x y l : Fin n) : Prop :=
  IsLowerBound P x y l ∧ ∀ w : Fin n, IsLowerBound P x y w → P.le w l = true

def IsJoinSemilattice {n : Nat} (P : FinPoset n) : Prop :=
  ∀ x y : Fin n, ∃ u : Fin n, IsLeastUpperBound P x y u

def IsMeetSemilattice {n : Nat} (P : FinPoset n) : Prop :=
  ∀ x y : Fin n, ∃ l : Fin n, IsGreatestLowerBound P x y l

def IsLattice {n : Nat} (P : FinPoset n) : Prop :=
  IsJoinSemilattice P ∧ IsMeetSemilattice P

def IsBot {n : Nat} (P : FinPoset n) (b : Fin n) : Prop :=
  ∀ x : Fin n, P.le b x = true

def IsTop {n : Nat} (P : FinPoset n) (t : Fin n) : Prop :=
  ∀ x : Fin n, P.le x t = true

theorem lub_unique {n : Nat} {P : FinPoset n} {x y u₁ u₂ : Fin n}
    (h1 : IsLeastUpperBound P x y u₁) (h2 : IsLeastUpperBound P x y u₂) : u₁ = u₂ :=
  P.le_antisymm u₁ u₂ (h1.2 u₂ h2.1) (h2.2 u₁ h1.1)

theorem glb_unique {n : Nat} {P : FinPoset n} {x y l₁ l₂ : Fin n}
    (h1 : IsGreatestLowerBound P x y l₁) (h2 : IsGreatestLowerBound P x y l₂) : l₁ = l₂ :=
  P.le_antisymm l₁ l₂ (h2.2 l₁ h1.1) (h1.2 l₂ h2.1)

theorem bot_unique {n : Nat} {P : FinPoset n} {b₁ b₂ : Fin n}
    (h1 : IsBot P b₁) (h2 : IsBot P b₂) : b₁ = b₂ :=
  P.le_antisymm b₁ b₂ (h1 b₂) (h2 b₁)

theorem top_unique {n : Nat} {P : FinPoset n} {t₁ t₂ : Fin n}
    (h1 : IsTop P t₁) (h2 : IsTop P t₂) : t₁ = t₂ :=
  P.le_antisymm t₁ t₂ (h2 t₁) (h1 t₂)

def isLubBool {n : Nat} (P : FinPoset n) (x y u : Fin n) : Bool :=
  P.le x u && P.le y u && finAll n (fun w => !(P.le x w && P.le y w) || P.le u w)

def isGlbBool {n : Nat} (P : FinPoset n) (x y l : Fin n) : Bool :=
  P.le l x && P.le l y && finAll n (fun w => !(P.le w x && P.le w y) || P.le w l)

def isJoinSemilatticeBool {n : Nat} (P : FinPoset n) : Bool :=
  finAll n (fun x => finAll n (fun y => finAny n (fun u => isLubBool P x y u)))

def isMeetSemilatticeBool {n : Nat} (P : FinPoset n) : Bool :=
  finAll n (fun x => finAll n (fun y => finAny n (fun l => isGlbBool P x y l)))

def isLatticeBool {n : Nat} (P : FinPoset n) : Bool :=
  isJoinSemilatticeBool P && isMeetSemilatticeBool P

theorem isLubBool_iff {n : Nat} (P : FinPoset n) (x y u : Fin n) :
    isLubBool P x y u = true ↔ IsLeastUpperBound P x y u := by
  simp only [isLubBool, Bool.and_eq_true, finAll_eq_true, IsLeastUpperBound, IsUpperBound]
  constructor
  · intro ⟨⟨hxu, hyu⟩, hall⟩
    refine ⟨⟨hxu, hyu⟩, fun w ⟨hxw, hyw⟩ => ?_⟩
    have hw := hall w
    simp [hxw, hyw] at hw
    exact hw
  · intro ⟨⟨hxu, hyu⟩, hall⟩
    refine ⟨⟨hxu, hyu⟩, fun w => ?_⟩
    cases hxw : P.le x w <;> cases hyw : P.le y w <;> simp
    exact hall w ⟨hxw, hyw⟩

theorem isGlbBool_iff {n : Nat} (P : FinPoset n) (x y l : Fin n) :
    isGlbBool P x y l = true ↔ IsGreatestLowerBound P x y l := by
  simp only [isGlbBool, Bool.and_eq_true, finAll_eq_true, IsGreatestLowerBound, IsLowerBound]
  constructor
  · intro ⟨⟨hlx, hly⟩, hall⟩
    refine ⟨⟨hlx, hly⟩, fun w ⟨hwx, hwy⟩ => ?_⟩
    have hw := hall w
    simp [hwx, hwy] at hw
    exact hw
  · intro ⟨⟨hlx, hly⟩, hall⟩
    refine ⟨⟨hlx, hly⟩, fun w => ?_⟩
    cases hwx : P.le w x <;> cases hwy : P.le w y <;> simp
    exact hall w ⟨hwx, hwy⟩

theorem isJoinSemilatticeBool_iff {n : Nat} (P : FinPoset n) :
    isJoinSemilatticeBool P = true ↔ IsJoinSemilattice P := by
  simp only [isJoinSemilatticeBool, finAll_eq_true, finAny_eq_true, isLubBool_iff, IsJoinSemilattice]

theorem isMeetSemilatticeBool_iff {n : Nat} (P : FinPoset n) :
    isMeetSemilatticeBool P = true ↔ IsMeetSemilattice P := by
  simp only [isMeetSemilatticeBool, finAll_eq_true, finAny_eq_true, isGlbBool_iff, IsMeetSemilattice]

theorem isLatticeBool_iff {n : Nat} (P : FinPoset n) :
    isLatticeBool P = true ↔ IsLattice P := by
  simp only [isLatticeBool, Bool.and_eq_true, isJoinSemilatticeBool_iff,
             isMeetSemilatticeBool_iff, IsLattice]

end FinPoset

/-- Order isomorphism between two finite posets. -/
structure PosetIso {n m : Nat} (P : FinPoset n) (Q : FinPoset m) where
  toFun : Fin n → Fin m
  invFun : Fin m → Fin n
  left_inv : ∀ x : Fin n, invFun (toFun x) = x
  right_inv : ∀ y : Fin m, toFun (invFun y) = y
  map_le : ∀ x y : Fin n, Q.le (toFun x) (toFun y) = P.le x y

def IsPosetIsomorphic {n m : Nat} (P : FinPoset n) (Q : FinPoset m) : Prop :=
  Nonempty (PosetIso P Q)

def PosetIso.symm {n m : Nat} {P : FinPoset n} {Q : FinPoset m}
    (e : PosetIso P Q) : PosetIso Q P where
  toFun := e.invFun
  invFun := e.toFun
  left_inv := e.right_inv
  right_inv := e.left_inv
  map_le u v := by
    have h := e.map_le (e.invFun u) (e.invFun v)
    rw [e.right_inv u, e.right_inv v] at h
    exact h.symm

theorem PosetIso.card_eq {n m : Nat} {P : FinPoset n} {Q : FinPoset m}
    (e : PosetIso P Q) : n = m := by
  have h1 : finCount n (fun _ => true) = n := by
    clear e P Q
    induction n with
    | zero => rfl
    | succ k ih => simp [finCount, ih]; omega
  have h2 : finCount m (fun _ => true) = m := by
    clear e P Q
    induction m with
    | zero => rfl
    | succ k ih => simp [finCount, ih]; omega
  rw [← h1, ← h2]
  exact finCount_bij e.toFun e.invFun e.left_inv e.right_inv _ _ (fun _ => rfl)

theorem PosetIso.map_bot {n m : Nat} {P : FinPoset n} {Q : FinPoset m}
    (e : PosetIso P Q) {b : Fin n} (hb : P.IsBot b) : Q.IsBot (e.toFun b) := by
  intro y
  rw [← e.right_inv y, e.map_le]
  exact hb (e.invFun y)

theorem PosetIso.map_top {n m : Nat} {P : FinPoset n} {Q : FinPoset m}
    (e : PosetIso P Q) {t : Fin n} (ht : P.IsTop t) : Q.IsTop (e.toFun t) := by
  intro y
  rw [← e.right_inv y, e.map_le]
  exact ht (e.invFun y)

theorem PosetIso.preserves_lub {n m : Nat} {P : FinPoset n} {Q : FinPoset m}
    (e : PosetIso P Q) {x y u : Fin n} (h : P.IsLeastUpperBound x y u) :
    Q.IsLeastUpperBound (e.toFun x) (e.toFun y) (e.toFun u) := by
  refine ⟨⟨?_, ?_⟩, fun w ⟨hxw, hyw⟩ => ?_⟩
  · rw [e.map_le]; exact h.1.1
  · rw [e.map_le]; exact h.1.2
  · rw [← e.right_inv w, e.map_le]
    apply h.2 (e.invFun w)
    constructor
    · rw [← e.map_le, e.right_inv]; exact hxw
    · rw [← e.map_le, e.right_inv]; exact hyw

/-! ## Incidence Algebra and Two-Variable Möbius Function -/

/-- Mathematical specification of the two-variable Möbius function `μ(x, y)` on `P`. -/
def IsMobiusFunction {n : Nat} (P : FinPoset n) (mu : Fin n → Fin n → Int) : Prop :=
  (∀ x y : Fin n, P.le x y = false → mu x y = 0) ∧
  (∀ x y : Fin n, P.le x y = true →
    finSum n (fun z => if P.le x z && P.le z y then mu x z else 0) =
      if x = y then 1 else 0)

def strictLowerIntervalCard {n : Nat} (P : FinPoset n) (x y : Fin n) : Nat :=
  finCount n (fun z => P.le x z && P.le z y && decide (z ≠ y))

/-- Fuel-indexed recursive construction of `μ(x, y)`. -/
def mobiusAux {n : Nat} (P : FinPoset n) : Nat → Fin n → Fin n → Int
  | 0, x, y => if x = y then 1 else 0
  | k + 1, x, y =>
      if P.le x y then
        if x = y then 1
        else - finSum n (fun z =>
          if P.le x z && P.le z y && decide (z ≠ y) then mobiusAux P k x z else 0)
      else 0

/-- The canonical two-variable Möbius function `μ(x, y)` of a finite poset `P`. -/
def mobius {n : Nat} (P : FinPoset n) (x y : Fin n) : Int :=
  mobiusAux P n x y

theorem strictLowerIntervalCard_lt {n : Nat} (P : FinPoset n) {x y z : Fin n}
    (hxz : P.le x z = true) (hzy : P.le z y = true) (hzy_ne : z ≠ y) :
    strictLowerIntervalCard P x z + 1 ≤ strictLowerIntervalCard P x y := by
  unfold strictLowerIntervalCard
  apply finCount_strict_mono z
  · intro w hw
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hw ⊢
    refine ⟨⟨hw.1.1, P.le_trans w z y hw.1.2 hzy⟩, ?_⟩
    intro hwy
    subst hwy
    exact hw.2 (P.le_antisymm w z hw.1.2 hzy)
  · simp
  · simp [hxz, hzy, hzy_ne]

theorem mobiusAux_stabilize {n : Nat} (P : FinPoset n) :
    ∀ (k d : Nat) (x y : Fin n),
      strictLowerIntervalCard P x y ≤ k →
      mobiusAux P k x y = mobiusAux P (k + d) x y
  | 0, d, x, y, hle => by
    cases d with
    | zero => rfl
    | succ d' =>
      by_cases hxy_eq : x = y
      · subst hxy_eq
        simp [mobiusAux, P.le_refl]
      · cases hxy : P.le x y
        · simp [mobiusAux, hxy, hxy_eq]
        · exfalso
          have hpos : finCount n (fun _ => false) + 1 ≤ strictLowerIntervalCard P x y := by
            unfold strictLowerIntervalCard
            apply finCount_strict_mono x
            · intro _ h; nomatch h
            · rfl
            · simp [P.le_refl x, hxy, hxy_eq]
          have h0 : finCount n (fun _ => false) = 0 := by
            clear hpos hle hxy hxy_eq P x y d'
            induction n with
            | zero => rfl
            | succ m ih => simp [finCount, ih]
          omega
  | k + 1, d, x, y, hle => by
    cases d with
    | zero => rfl
    | succ d' =>
      have hk1 : k + 1 + (d' + 1) = (k + d' + 1) + 1 := by omega
      rw [hk1]
      simp only [mobiusAux]
      cases hxy : P.le x y
      · rfl
      · by_cases heq : x = y
        · simp [heq]
        · simp only [heq, ↓reduceIte, Bool.true_eq_false]
          congr 1
          apply finSum_congr
          intro z
          cases hz : P.le x z && P.le z y && decide (z ≠ y)
          · rfl
          · simp only [↓reduceIte]
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hz
            have hlt := strictLowerIntervalCard_lt P hz.1.1 hz.1.2 hz.2
            exact mobiusAux_stabilize P k (d' + 1) x z (by omega)

theorem mobius_unfold {n : Nat} (P : FinPoset n) (x y : Fin n) :
    mobius P x y =
      if P.le x y then
        if x = y then 1
        else - finSum n (fun z =>
          if P.le x z && P.le z y && decide (z ≠ y) then mobius P x z else 0)
      else 0 := by
  have hle : strictLowerIntervalCard P x y ≤ n := finCount_le n _
  have hstab := mobiusAux_stabilize P n 1 x y hle
  rw [mobius, hstab]
  rfl

/-- Main theorem: `mobius P` satisfies the defining Möbius specification on `P`. -/
theorem mobius_spec {n : Nat} (P : FinPoset n) : IsMobiusFunction P (mobius P) := by
  constructor
  · intro x y hfalse
    rw [mobius_unfold, hfalse]
    rfl
  · intro x y hxy
    rw [finSum_split_eq y]
    by_cases heq : x = y
    · subst heq
      simp only [P.le_refl x, Bool.and_self, ↓reduceIte]
      have hmu_xx : mobius P x x = 1 := by
        rw [mobius_unfold, if_pos (P.le_refl x), if_pos rfl]
      have hrest : finSum n (fun z =>
          if decide (z ≠ x) then (if P.le x z && P.le z x then mobius P x z else 0) else 0) = 0 := by
        rw [finSum_congr (g := fun _ => 0)]
        · exact finSum_zero n
        · intro z
          by_cases hzx : z = x
          · subst hzx; simp
          · rw [if_pos (decide_eq_true hzx)]
            cases h1 : P.le x z <;> cases h2 : P.le z x
            · rfl
            · rfl
            · rfl
            · exact absurd (P.le_antisymm z x h2 h1) hzx
      rw [hmu_xx, hrest]
      omega
    · simp only [heq, ↓reduceIte, hxy, P.le_refl y, Bool.and_self]
      have hmu_xy : mobius P x y =
          - finSum n (fun z => if P.le x z && P.le z y && decide (z ≠ y) then mobius P x z else 0) := by
        rw [mobius_unfold, hxy, if_neg heq]
        rfl
      have halign : finSum n (fun z =>
          if decide (z ≠ y) then (if P.le x z && P.le z y then mobius P x z else 0) else 0) =
          finSum n (fun z =>
          if P.le x z && P.le z y && decide (z ≠ y) then mobius P x z else 0) := by
        apply finSum_congr
        intro z
        by_cases hzy : z = y
        · subst hzy; simp
        · cases P.le x z <;> cases P.le z y <;> simp [hzy]
      rw [hmu_xy, halign]
      omega

/-- Incidence-algebra convolution `(f ⋆ g)(x, y) = ∑_z f(x, z) g(z, y)`. -/
def incConv {n : Nat} (f g : Fin n → Fin n → Int) (x y : Fin n) : Int :=
  finSum n (fun z => f x z * g z y)

def incZeta {n : Nat} (P : FinPoset n) (x y : Fin n) : Int :=
  if P.le x y then 1 else 0

def incDelta {n : Nat} (x y : Fin n) : Int :=
  if x = y then 1 else 0

theorem incConv_assoc {n : Nat} (f g h : Fin n → Fin n → Int) (x y : Fin n) :
    incConv (incConv f g) h x y = incConv f (incConv g h) x y := by
  simp only [incConv]
  have h1 : finSum n (fun z => finSum n (fun w => f x w * g w z) * h z y) =
      finSum n (fun z => finSum n (fun w => f x w * g w z * h z y)) := by
    apply finSum_congr; intro z; rw [finSum_mul_right]
  have h2 : finSum n (fun w => f x w * finSum n (fun z => g w z * h z y)) =
      finSum n (fun w => finSum n (fun z => f x w * (g w z * h z y))) := by
    apply finSum_congr; intro w; rw [finSum_mul_left]
  rw [h1, h2, finSum_comm]
  apply finSum_congr; intro w; apply finSum_congr; intro z
  exact Int.mul_assoc _ _ _

theorem incConv_delta_right {n : Nat} (f : Fin n → Fin n → Int) (x y : Fin n) :
    incConv f incDelta x y = f x y := by
  simp only [incConv, incDelta]
  have h : finSum n (fun z => f x z * (if z = y then 1 else 0)) =
      finSum n (fun z => if z = y then f x z else 0) := by
    apply finSum_congr; intro z; split <;> simp
  rw [h, finSum_ite_eq]

theorem incConv_delta_left {n : Nat} (f : Fin n → Fin n → Int) (x y : Fin n) :
    incConv incDelta f x y = f x y := by
  simp only [incConv, incDelta]
  have h : finSum n (fun z => (if x = z then 1 else 0) * f z y) =
      finSum n (fun z => if z = x then f z y else 0) := by
    apply finSum_congr; intro z
    by_cases hxz : x = z
    · subst hxz; simp
    · have hzx : z ≠ x := fun h => hxz h.symm
      simp [hxz, hzx]
  rw [h, finSum_ite_eq]

theorem isMobius_iff_conv_zeta {n : Nat} (P : FinPoset n) (mu : Fin n → Fin n → Int) :
    IsMobiusFunction P mu ↔
      (∀ x y, P.le x y = false → mu x y = 0) ∧
      (∀ x y, incConv mu (incZeta P) x y = incDelta x y) := by
  constructor
  · intro ⟨hsupp, hsum⟩
    refine ⟨hsupp, fun x y => ?_⟩
    cases hxy : P.le x y
    · have hne : x ≠ y := by
        intro heq; subst heq; exact Bool.noConfusion (hxy.symm.trans (P.le_refl x))
      simp only [incConv, incZeta, incDelta, hne, ↓reduceIte]
      rw [finSum_congr (g := fun _ => 0)]
      · exact finSum_zero n
      · intro z
        cases hxz : P.le x z
        · rw [hsupp x z hxz]; simp
        · cases hzy : P.le z y
          · simp
          · exfalso
            exact Bool.noConfusion (hxy.symm.trans (P.le_trans x z y hxz hzy))
    · have h1 : incConv mu (incZeta P) x y =
          finSum n (fun z => if P.le x z && P.le z y then mu x z else 0) := by
        apply finSum_congr
        intro z
        simp only [incZeta]
        cases hxz : P.le x z
        · rw [hsupp x z hxz]; simp
        · cases hzy : P.le z y <;> simp
      rw [h1, hsum x y hxy, incDelta]
  · intro ⟨hsupp, hconv⟩
    refine ⟨hsupp, fun x y hxy => ?_⟩
    have hc := hconv x y
    rw [incDelta] at hc
    rw [← hc]
    apply finSum_congr
    intro z
    simp only [incZeta]
    cases hxz : P.le x z
    · rw [hsupp x z hxz]; simp
    · cases hzy : P.le z y <;> simp

theorem zeta_dual_mobius_right {n : Nat} (P : FinPoset n) :
    ∀ x y : Fin n, incConv (incZeta P) (fun u v => mobius P.dual v u) x y = incDelta x y := by
  intro x y
  have hdual := (isMobius_iff_conv_zeta P.dual (mobius P.dual)).mp (mobius_spec P.dual)
  have hc := hdual.2 y x
  unfold incConv incZeta incDelta at hc ⊢
  simp only [FinPoset.dual_le] at hc
  have hswap : finSum n (fun z => (if P.le x z then 1 else 0) * mobius P.dual y z) =
      finSum n (fun z => mobius P.dual y z * (if P.le x z then 1 else 0)) := by
    apply finSum_congr; intro z; exact Int.mul_comm _ _
  rw [hswap, hc]
  by_cases hxy : x = y
  · subst hxy; simp
  · have hyx : y ≠ x := fun h => hxy h.symm
    simp [hxy, hyx]

/-- Uniqueness of `μ` on any finite poset `P`. -/
theorem mobius_unique {n : Nat} (P : FinPoset n) (mu : Fin n → Fin n → Int)
    (hmu : IsMobiusFunction P mu) : mu = mobius P := by
  have h1 := ((isMobius_iff_conv_zeta P mu).mp hmu).2
  have h2 := ((isMobius_iff_conv_zeta P (mobius P)).mp (mobius_spec P)).2
  let r : Fin n → Fin n → Int := fun u v => mobius P.dual v u
  have hr := zeta_dual_mobius_right P
  funext x y
  have step1 : mu x y = incConv mu (incConv (incZeta P) r) x y := by
    have hcongr : incConv (incZeta P) r = incDelta := by funext u v; exact hr u v
    rw [hcongr, incConv_delta_right]
  have step2 : incConv (incConv mu (incZeta P)) r x y = r x y := by
    have hcongr : incConv mu (incZeta P) = incDelta := by funext u v; exact h1 u v
    rw [hcongr, incConv_delta_left]
  have eq_mu_r : mu x y = r x y := by
    rw [step1, ← incConv_assoc, step2]
  have step3 : mobius P x y = incConv (mobius P) (incConv (incZeta P) r) x y := by
    have hcongr : incConv (incZeta P) r = incDelta := by funext u v; exact hr u v
    rw [hcongr, incConv_delta_right]
  have step4 : incConv (incConv (mobius P) (incZeta P)) r x y = r x y := by
    have hcongr : incConv (mobius P) (incZeta P) = incDelta := by funext u v; exact h2 u v
    rw [hcongr, incConv_delta_left]
  have eq_mob_r : mobius P x y = r x y := by
    rw [step3, ← incConv_assoc, step4]
  exact eq_mu_r.trans eq_mob_r.symm

/-- Order-Dual Symmetry: `μ_{P^op}(x, y) = μ_P(y, x)`. -/
theorem mobius_dual {n : Nat} (P : FinPoset n) (x y : Fin n) :
    mobius P.dual x y = mobius P y x := by
  have h2 := ((isMobius_iff_conv_zeta P (mobius P)).mp (mobius_spec P)).2
  let r : Fin n → Fin n → Int := fun u v => mobius P.dual v u
  have hr := zeta_dual_mobius_right P
  have step3 : mobius P y x = incConv (mobius P) (incConv (incZeta P) r) y x := by
    have hcongr : incConv (incZeta P) r = incDelta := by funext u v; exact hr u v
    rw [hcongr, incConv_delta_right]
  have step4 : incConv (incConv (mobius P) (incZeta P)) r y x = r y x := by
    have hcongr : incConv (mobius P) (incZeta P) = incDelta := by funext u v; exact h2 u v
    rw [hcongr, incConv_delta_left]
  exact (step3.trans ((incConv_assoc _ _ _ y x).symm.trans step4)).symm

/-- Möbius inversion formula on finite posets. -/
theorem mobius_inversion {n : Nat} (P : FinPoset n) (f g : Fin n → Int)
    (hg : ∀ y : Fin n, g y = finSum n (fun x => if P.le x y then f x else 0)) :
    ∀ y : Fin n, f y = finSum n (fun x => g x * mobius P x y) := by
  intro y
  have hrew : finSum n (fun x => g x * mobius P x y) =
      finSum n (fun x => finSum n (fun w => (if P.le w x then f w else 0) * mobius P x y)) := by
    apply finSum_congr
    intro x
    rw [hg x, finSum_mul_right]
  rw [hrew, finSum_comm]
  have hinner : finSum n (fun w => finSum n (fun x => (if P.le w x then f w else 0) * mobius P x y)) =
      finSum n (fun w => f w * incConv (incZeta P) (mobius P) w y) := by
    apply finSum_congr
    intro w
    unfold incConv
    rw [← finSum_mul_left]
    apply finSum_congr
    intro x
    simp only [incZeta]
    cases P.le w x <;> simp [Int.mul_assoc]
  rw [hinner]
  have hzeta_mu : ∀ w, incConv (incZeta P) (mobius P) w y = incDelta w y := by
    intro w
    have hd := zeta_dual_mobius_right P w y
    rw [← hd]
    unfold incConv
    apply finSum_congr
    intro z
    dsimp only
    rw [mobius_dual P y z]
  have hdelta : finSum n (fun w => f w * incConv (incZeta P) (mobius P) w y) =
      finSum n (fun w => if w = y then f w else 0) := by
    apply finSum_congr
    intro w
    rw [hzeta_mu w, incDelta]
    split <;> simp
  rw [hdelta, finSum_ite_eq]

/-! ## Isomorphism Invariance of Möbius Function and Möbius Spectra -/

theorem PosetIso.map_mobius {n m : Nat} {P : FinPoset n} {Q : FinPoset m}
    (e : PosetIso P Q) (x y : Fin n) :
    mobius Q (e.toFun x) (e.toFun y) = mobius P x y := by
  let muPull : Fin n → Fin n → Int := fun u v => mobius Q (e.toFun u) (e.toFun v)
  have hspec : IsMobiusFunction P muPull := by
    have hQ := mobius_spec Q
    constructor
    · intro u v hfalse
      exact hQ.1 (e.toFun u) (e.toFun v) (by rw [e.map_le]; exact hfalse)
    · intro u v huv
      have hQv : Q.le (e.toFun u) (e.toFun v) = true := by rw [e.map_le]; exact huv
      have hsumQ := hQ.2 (e.toFun u) (e.toFun v) hQv
      have hbij : finSum n (fun z => if P.le u z && P.le z v then muPull u z else 0) =
          finSum m (fun w => if Q.le (e.toFun u) w && Q.le w (e.toFun v)
                             then mobius Q (e.toFun u) w else 0) := by
        apply finSum_bij e.toFun e.invFun e.left_inv e.right_inv
        intro z
        simp only [muPull, e.map_le]
      rw [hbij, hsumQ]
      have heq_iff : (e.toFun u = e.toFun v) ↔ (u = v) := by
        constructor
        · intro h; rw [← e.left_inv u, h, e.left_inv v]
        · intro h; rw [h]
      by_cases huv_eq : u = v
      · rw [if_pos (heq_iff.mpr huv_eq), if_pos huv_eq]
      · rw [if_neg (mt heq_iff.mp huv_eq), if_neg huv_eq]
  have hunique := mobius_unique P muPull hspec
  exact congrFun (congrFun hunique x) y

/-- Multiplicity of value `v ∈ ℤ` in the lower-interval Möbius spectrum `{μ(0̂, x) : x ∈ P}`. -/
def lowerMobiusMult {n : Nat} (P : FinPoset n) (bot : Fin n) (v : Int) : Nat :=
  finCount n (fun x => decide (mobius P bot x = v))

/-- Multiplicity of value `v ∈ ℤ` in the upper-interval Möbius spectrum `{μ(x, 1̂) : x ∈ P}`. -/
def upperMobiusMult {n : Nat} (P : FinPoset n) (top : Fin n) (v : Int) : Nat :=
  finCount n (fun x => decide (mobius P x top = v))

/-- Exact integer-valued full-interval multiplicity `∑_{x : Fin n} #{y : x ≤ y ∧ μ(x, y) = v}`. -/
def fullMobiusCount {n : Nat} (P : FinPoset n) (v : Int) : Int :=
  finSum n (fun x => finSum n (fun y => if P.le x y && decide (mobius P x y = v) then 1 else 0))

theorem PosetIso.lowerMobiusMult_eq {n m : Nat} {P : FinPoset n} {Q : FinPoset m}
    (e : PosetIso P Q) {bP : Fin n} {bQ : Fin m}
    (hbP : P.IsBot bP) (hbQ : Q.IsBot bQ) (v : Int) :
    lowerMobiusMult P bP v = lowerMobiusMult Q bQ v := by
  have hb_eq : e.toFun bP = bQ := FinPoset.bot_unique (e.map_bot hbP) hbQ
  unfold lowerMobiusMult
  apply finCount_bij e.toFun e.invFun e.left_inv e.right_inv
  intro x
  rw [← hb_eq, e.map_mobius bP x]

theorem PosetIso.upperMobiusMult_eq {n m : Nat} {P : FinPoset n} {Q : FinPoset m}
    (e : PosetIso P Q) {tP : Fin n} {tQ : Fin m}
    (htP : P.IsTop tP) (htQ : Q.IsTop tQ) (v : Int) :
    upperMobiusMult P tP v = upperMobiusMult Q tQ v := by
  have ht_eq : e.toFun tP = tQ := FinPoset.top_unique (e.map_top htP) htQ
  unfold upperMobiusMult
  apply finCount_bij e.toFun e.invFun e.left_inv e.right_inv
  intro x
  rw [← ht_eq, e.map_mobius x tP]

theorem PosetIso.fullMobiusCount_eq {n m : Nat} {P : FinPoset n} {Q : FinPoset m}
    (e : PosetIso P Q) (v : Int) :
    fullMobiusCount P v = fullMobiusCount Q v := by
  unfold fullMobiusCount
  apply finSum_bij e.toFun e.invFun e.left_inv e.right_inv
  intro x
  apply finSum_bij e.toFun e.invFun e.left_inv e.right_inv
  intro y
  rw [e.map_le x y, e.map_mobius x y]

/-- Order-duality preserves the full two-variable Möbius spectrum identically! -/
theorem fullMobiusCount_dual {n : Nat} (P : FinPoset n) (v : Int) :
    fullMobiusCount P.dual v = fullMobiusCount P v := by
  unfold fullMobiusCount
  rw [finSum_comm]
  apply finSum_congr
  intro y
  apply finSum_congr
  intro x
  rw [FinPoset.dual_le, mobius_dual P x y]

end Conjecture00000004770
