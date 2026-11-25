/-
  Conjecture 00000008534 — Whitney Log-Concavity of Geometric Lattices
  Complete self-contained formalization and disproof in Core Lean 4 (v4.19.0).
  Zero external dependencies, zero sorry/admit, zero native_decide, zero custom axioms.
-/

namespace WhitneyLogConcavity

/-! ## 1. Commutative Ring Tactic over `Int` and Finite Combinatorial Primitives -/

/-- Normalization + linear arithmetic solver for polynomial ring identities over `Int`. -/
macro "int_ring" : tactic =>
  `(tactic| (
    simp only [Int.sub_eq_add_neg, Int.mul_add, Int.add_mul, Int.neg_mul, Int.mul_neg,
      Int.neg_add, Int.neg_neg, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm,
      Int.one_mul, Int.mul_one, Int.zero_mul, Int.mul_zero, Int.add_zero, Int.zero_add] <;>
    omega))

theorem band_iff {a b : Bool} : (a && b) = true ↔ (a = true ∧ b = true) := by
  cases a <;> cases b <;> decide

/-- Sum of an `Int`-valued function over `Fin n`. -/
def sumFin : (n : Nat) → (Fin n → Int) → Int
  | 0, _ => 0
  | n + 1, f => sumFin n (fun i => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) + f ⟨n, Nat.lt_succ_self n⟩

/-- Count of elements in `Fin n` satisfying a boolean predicate `p`. -/
def countFin : (n : Nat) → (Fin n → Bool) → Nat
  | 0, _ => 0
  | n + 1, p =>
      countFin n (fun i => p ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) +
      (if p ⟨n, Nat.lt_succ_self n⟩ then 1 else 0)

/-- Universal boolean quantifier over `Fin n`. -/
def allFin : (n : Nat) → (Fin n → Bool) → Bool
  | 0, _ => true
  | n + 1, p =>
      allFin n (fun i => p ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) && p ⟨n, Nat.lt_succ_self n⟩

/-- Existential boolean quantifier over `Fin n`. -/
def anyFin : (n : Nat) → (Fin n → Bool) → Bool
  | 0, _ => false
  | n + 1, p =>
      anyFin n (fun i => p ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) || p ⟨n, Nat.lt_succ_self n⟩

theorem allFin_eq_true {n : Nat} {p : Fin n → Bool} :
    allFin n p = true ↔ ∀ i : Fin n, p i = true := by
  induction n with
  | zero =>
    constructor
    · intro _ i; exact absurd i.isLt (Nat.not_lt_zero _)
    · intro _; rfl
  | succ m ih =>
    simp only [allFin, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨hinit, hlast⟩ ⟨v, hv⟩
      by_cases hvm : v < m
      · exact hinit ⟨v, hvm⟩
      · have heq : v = m := by omega
        subst heq
        exact hlast
    · intro hall
      exact ⟨fun i => hall ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩, hall ⟨m, Nat.lt_succ_self m⟩⟩

theorem anyFin_eq_true {n : Nat} {p : Fin n → Bool} :
    anyFin n p = true ↔ ∃ i : Fin n, p i = true := by
  induction n with
  | zero =>
    constructor
    · intro h; cases h
    · rintro ⟨i, _⟩; exact absurd i.isLt (Nat.not_lt_zero _)
  | succ m ih =>
    simp only [anyFin, Bool.or_eq_true, ih]
    constructor
    · rintro (⟨i, hi⟩ | hlast)
      · exact ⟨⟨i.val, Nat.lt_succ_of_lt i.isLt⟩, hi⟩
      · exact ⟨⟨m, Nat.lt_succ_self m⟩, hlast⟩
    · rintro ⟨⟨v, hv⟩, hp⟩
      by_cases hvm : v < m
      · exact Or.inl ⟨⟨v, hvm⟩, hp⟩
      · have heq : v = m := by omega
        subst heq
        exact Or.inr hp

theorem sumFin_add {n : Nat} (f g : Fin n → Int) :
    sumFin n (fun i => f i + g i) = sumFin n f + sumFin n g := by
  induction n with
  | zero => rfl
  | succ m ih =>
    simp only [sumFin]
    rw [ih]
    omega

theorem sumFin_congr {n : Nat} {f g : Fin n → Int} (h : ∀ i : Fin n, f i = g i) :
    sumFin n f = sumFin n g := by
  induction n with
  | zero => rfl
  | succ m ih =>
    simp only [sumFin]
    rw [ih (fun i => h ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩), h ⟨m, Nat.lt_succ_self m⟩]

theorem sumFin_single {n : Nat} (x : Fin n) (c : Int) :
    sumFin n (fun y => if y == x then c else 0) = c := by
  induction n with
  | zero => exact absurd x.isLt (Nat.not_lt_zero _)
  | succ m ih =>
    simp only [sumFin]
    by_cases hxm : x.val < m
    · have hne : (⟨m, Nat.lt_succ_self m⟩ == x) = false := by
        cases hbeq : (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)) == x
        · rfl
        · have heq := LawfulBEq.eq_of_beq hbeq
          have : m = x.val := congrArg Fin.val heq
          omega
      rw [hne, if_neg Bool.false_ne_true, Int.add_zero]
      have hsub :
          (fun i : Fin m =>
            if (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (m + 1)) == x then c else 0) =
          (fun i : Fin m => if i == ⟨x.val, hxm⟩ then c else 0) := by
        funext i
        have hiff : ((⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (m + 1)) == x) =
            (i == ⟨x.val, hxm⟩) := by
          cases h1 : ((⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (m + 1)) == x) <;>
          cases h2 : (i == (⟨x.val, hxm⟩ : Fin m))
          · rfl
          · have e2 := LawfulBEq.eq_of_beq h2
            have hv : i.val = x.val := by rw [e2]
            have e1 : (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (m + 1)) = x := Fin.ext hv
            rw [beq_iff_eq.mpr e1] at h1; cases h1
          · have e1 := LawfulBEq.eq_of_beq h1
            have hv : i.val = x.val := by rw [← e1]
            have e2 : i = ⟨x.val, hxm⟩ := Fin.ext hv
            rw [beq_iff_eq.mpr e2] at h2; cases h2
          · rfl
        rw [hiff]
      rw [hsub]
      exact ih ⟨x.val, hxm⟩
    · have hxval : x.val = m := by omega
      have hxeq : (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)) = x := Fin.ext hxval.symm
      have hzero : sumFin m (fun i =>
          if (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (m + 1)) == x then c else 0) = 0 := by
        have hcongr : ∀ i : Fin m,
            (if (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (m + 1)) == x then c else 0) = 0 := by
          intro i
          cases hb : ((⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (m + 1)) == x)
          · rfl
          · have e := LawfulBEq.eq_of_beq hb
            have : i.val = x.val := congrArg Fin.val e
            omega
        rw [sumFin_congr hcongr]
        clear ih hxm hxval hxeq hcongr x
        induction m with
        | zero => rfl
        | succ k ihk => simp only [sumFin, ihk, Int.add_zero]
      rw [hzero, beq_iff_eq.mpr hxeq, if_pos rfl, Int.zero_add]

/-! ## 2. Finite Geometric Lattices -/

/-- Cover relation `x ⋖ y` in a finite poset `(Fin sz, le)`. -/
def Covers {sz : Nat} (le : Fin sz → Fin sz → Bool) (x y : Fin sz) : Prop :=
  le x y = true ∧ x ≠ y ∧ ∀ z : Fin sz, le x z = true → le z y = true → (z = x ∨ z = y)

/-- Boolean decision procedure for `Covers`. -/
def coversBool {sz : Nat} (le : Fin sz → Fin sz → Bool) (x y : Fin sz) : Bool :=
  le x y && (x != y) && allFin sz (fun z => !(le x z && le z y) || (z == x) || (z == y))

theorem coversBool_eq_true {sz : Nat} {le : Fin sz → Fin sz → Bool} {x y : Fin sz} :
    coversBool le x y = true ↔ Covers le x y := by
  simp only [coversBool, Covers, Bool.and_eq_true, bne_iff_ne, allFin_eq_true,
    Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_imp, beq_iff_eq]
  constructor
  · rintro ⟨⟨hxy, hne⟩, hall⟩
    refine ⟨hxy, hne, ?_⟩
    intro z hxz hzy
    rcases hall z with (himp | hzx) | hzy_eq
    · exfalso; have := himp hxz; rw [hzy] at this; cases this
    · exact Or.inl hzx
    · exact Or.inr hzy_eq
  · rintro ⟨hxy, hne, hall⟩
    refine ⟨⟨hxy, hne⟩, fun z => ?_⟩
    by_cases hxz : le x z = true
    · by_cases hzy : le z y = true
      · rcases hall z hxz hzy with rfl | rfl
        · exact Or.inl (Or.inr rfl)
        · exact Or.inr rfl
      · exact Or.inl (Or.inl (fun _ => Bool.eq_false_iff.mpr hzy))
    · exact Or.inl (Or.inl (fun h => absurd h hxz))

/-- A finite geometric lattice: a finite bounded, graded, upper-semimodular, atomic lattice. -/
structure GeometricLattice where
  size : Nat
  le : Fin size → Fin size → Bool
  join : Fin size → Fin size → Fin size
  meet : Fin size → Fin size → Fin size
  bot : Fin size
  top : Fin size
  rk : Fin size → Nat
  -- Partial order axioms
  le_refl : ∀ x : Fin size, le x x = true
  le_antisymm : ∀ x y : Fin size, le x y = true → le y x = true → x = y
  le_trans : ∀ x y z : Fin size, le x y = true → le y z = true → le x z = true
  -- Bounded lattice universal properties
  bot_le : ∀ x : Fin size, le bot x = true
  le_top : ∀ x : Fin size, le x top = true
  join_spec : ∀ x y z : Fin size, le (join x y) z = true ↔ (le x z = true ∧ le y z = true)
  meet_spec : ∀ x y z : Fin size, le z (meet x y) = true ↔ (le z x = true ∧ le z y = true)
  -- Grading / Jordan-Dedekind rank axioms
  rk_bot : rk bot = 0
  rk_mono_strict : ∀ x y : Fin size, le x y = true → x ≠ y → rk x < rk y
  rk_cover : ∀ x y : Fin size, Covers le x y → rk y = rk x + 1
  cover_below : ∀ x : Fin size, x ≠ bot → ∃ w : Fin size, Covers le w x
  -- Upper semimodularity
  semimodular : ∀ x y : Fin size, rk (join x y) + rk (meet x y) ≤ rk x + rk y
  -- Atomicity (atoms are join-dense)
  atomic : ∀ x u : Fin size,
    (∀ a : Fin size, Covers le bot a → le a x = true → le a u = true) → le x u = true

/-- Rank `r = rk(⊤)` of a geometric lattice. -/
def GeometricLattice.rank (L : GeometricLattice) : Nat := L.rk L.top

/-- Modularity of a geometric lattice (`rk(x ∨ y) + rk(x ∧ y) = rk(x) + rk(y)` everywhere). -/
def IsModular (L : GeometricLattice) : Prop :=
  ∀ x y : Fin L.size, L.rk (L.join x y) + L.rk (L.meet x y) = L.rk x + L.rk y

/-- Atoms of `L` are precisely the elements of rank `1`. -/
theorem atom_iff_rk_one (L : GeometricLattice) (a : Fin L.size) :
    Covers L.le L.bot a ↔ L.rk a = 1 := by
  constructor
  · intro hcov
    have h := L.rk_cover L.bot a hcov
    rw [L.rk_bot] at h
    exact h
  · intro hrk
    refine ⟨L.bot_le a, ?_, ?_⟩
    · intro heq; rw [← heq, L.rk_bot] at hrk; omega
    · intro z _ hza
      by_cases hzb : z = L.bot
      · exact Or.inl hzb
      · by_cases hza_eq : z = a
        · exact Or.inr hza_eq
        · exfalso
          have h1 := L.rk_mono_strict L.bot z (L.bot_le z) (Ne.symm hzb)
          have h2 := L.rk_mono_strict z a hza hza_eq
          have hb0 := L.rk_bot
          omega

/-- Uniqueness of the Jordan-Dedekind rank function on any `GeometricLattice`. -/
theorem rk_unique (L : GeometricLattice) (r' : Fin L.size → Nat)
    (hbot : r' L.bot = 0)
    (hcov : ∀ x y : Fin L.size, Covers L.le x y → r' y = r' x + 1) :
    ∀ x : Fin L.size, r' x = L.rk x := by
  have aux : ∀ n : Nat, ∀ x : Fin L.size, L.rk x ≤ n → r' x = L.rk x := by
    intro n
    induction n with
    | zero =>
      intro x hx
      by_cases hxb : x = L.bot
      · subst hxb; rw [hbot, L.rk_bot]
      · exfalso
        have := L.rk_mono_strict L.bot x (L.bot_le x) (Ne.symm hxb)
        have hb0 := L.rk_bot
        omega
    | succ m ih =>
      intro x hx
      by_cases hxb : x = L.bot
      · subst hxb; rw [hbot, L.rk_bot]
      · rcases L.cover_below x hxb with ⟨w, hwx⟩
        have hrk := L.rk_cover w x hwx
        have hr' := hcov w x hwx
        have hwm : L.rk w ≤ m := by omega
        rw [hr', ih w hwm, hrk]
  intro x
  exact aux (L.rk x) x (Nat.le_refl _)

theorem rk_le_rank (L : GeometricLattice) (x : Fin L.size) : L.rk x ≤ L.rank := by
  unfold GeometricLattice.rank
  by_cases hxt : x = L.top
  · subst hxt; exact Nat.le_refl _
  · exact Nat.le_of_lt (L.rk_mono_strict x L.top (L.le_top x) hxt)

/-! ## 3. Whitney Numbers of the Second and First Kind & Möbius Inversion -/

/-- Build `[f 0, f 1, ..., f (len - 1)]` by structural recursion. -/
def mapRangeAux (f : Nat → Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | c + 1, start => f start :: mapRangeAux f c (start + 1)

theorem mapRangeAux_length (f : Nat → Nat) :
    ∀ (c start : Nat), (mapRangeAux f c start).length = c := by
  intro c
  induction c with
  | zero => intro _; rfl
  | succ m ih => intro start; simp [mapRangeAux, ih]

theorem mapRangeAux_getElem (f : Nat → Nat) :
    ∀ (c start i : Nat) (hi : i < (mapRangeAux f c start).length),
      (mapRangeAux f c start)[i] = f (start + i) := by
  intro c
  induction c with
  | zero =>
    intro _ _ hi
    exact absurd hi (Nat.not_lt_zero _)
  | succ m ih =>
    intro start i hi
    cases i with
    | zero =>
      simp only [mapRangeAux, List.getElem_cons_zero, Nat.add_zero]
    | succ j =>
      simp only [mapRangeAux, List.getElem_cons_succ]
      have hj : j < (mapRangeAux f m (start + 1)).length := by
        simp [mapRangeAux] at hi; omega
      rw [ih (start + 1) j hj]
      exact congrArg f (by omega)

/-- `k`-th Whitney number of the second kind `W_k(L)`: number of flats of rank `k`. -/
def whitneySecondAt (L : GeometricLattice) (k : Nat) : Nat :=
  countFin L.size (fun x => L.rk x == k)

/-- Rank distribution `(W_0(L), W_1(L), ..., W_r(L))` (Whitney numbers of the second kind). -/
def whitneySecond (L : GeometricLattice) : List Nat :=
  mapRangeAux (whitneySecondAt L) (L.rank + 1) 0

theorem whitneySecond_length (L : GeometricLattice) :
    (whitneySecond L).length = L.rank + 1 :=
  mapRangeAux_length _ _ _

theorem whitneySecond_getElem (L : GeometricLattice) (k : Nat)
    (hk : k < (whitneySecond L).length) :
    (whitneySecond L)[k] = whitneySecondAt L k := by
  unfold whitneySecond
  rw [mapRangeAux_getElem (whitneySecondAt L) (L.rank + 1) 0 k hk, Nat.zero_add]

/-- Fuel-indexed lower-interval Möbius function `μ_L(⊥, x)`. -/
def muBotAux (L : GeometricLattice) : Nat → Fin L.size → Int
  | 0, x => if x == L.bot then 1 else 0
  | fuel + 1, x =>
      if x == L.bot then 1
      else - sumFin L.size (fun y =>
        if L.le y x && (y != x) then muBotAux L fuel y else 0)

/-- Lower-interval Möbius function `μ_L(⊥, x)` on a geometric lattice. -/
def muBot (L : GeometricLattice) (x : Fin L.size) : Int :=
  muBotAux L (L.rk x) x

theorem muBotAux_stable (L : GeometricLattice) :
    ∀ (m f1 f2 : Nat) (x : Fin L.size),
      L.rk x ≤ m → m ≤ f1 → m ≤ f2 → muBotAux L f1 x = muBotAux L f2 x := by
  intro m
  induction m with
  | zero =>
    intro f1 f2 x hx _ _
    have hxb : x = L.bot := by
      by_cases h : x = L.bot
      · exact h
      · exfalso
        have := L.rk_mono_strict L.bot x (L.bot_le x) (Ne.symm h)
        have hb0 := L.rk_bot
        omega
    subst hxb
    cases f1 <;> cases f2 <;> simp [muBotAux]
  | succ k ih =>
    intro f1 f2 x hx hf1 hf2
    by_cases hxb : x = L.bot
    · subst hxb
      cases f1 <;> cases f2 <;> simp [muBotAux]
    · rcases Nat.exists_eq_succ_of_ne_zero (by omega : f1 ≠ 0) with ⟨f1', rfl⟩
      rcases Nat.exists_eq_succ_of_ne_zero (by omega : f2 ≠ 0) with ⟨f2', rfl⟩
      have hbeq : (x == L.bot) = false := beq_false_of_ne hxb
      simp only [muBotAux, hbeq]
      have hcongr : ∀ y : Fin L.size,
          (if (L.le y x && (y != x)) = true then muBotAux L f1' y else 0) =
          (if (L.le y x && (y != x)) = true then muBotAux L f2' y else 0) := by
        intro y
        by_cases hy : (L.le y x && (y != x)) = true
        · simp only [hy, if_pos rfl]
          simp only [Bool.and_eq_true, bne_iff_ne] at hy
          have hyrk := L.rk_mono_strict y x hy.1 hy.2
          exact ih f1' f2' y (by omega) (by omega) (by omega)
        · simp only [hy, if_neg Bool.false_ne_true]
      rw [sumFin_congr hcongr]

/-- Defining base value `μ_L(⊥, ⊥) = 1`. -/
theorem muBot_bot (L : GeometricLattice) : muBot L L.bot = 1 := by
  unfold muBot
  rw [L.rk_bot]
  simp [muBotAux]

/-- Defining recurrence `μ_L(⊥, x) = - ∑_{y < x} μ_L(⊥, y)` for `x ≠ ⊥`. -/
theorem muBot_ne_bot (L : GeometricLattice) (x : Fin L.size) (hx : x ≠ L.bot) :
    muBot L x = - sumFin L.size (fun y => if L.le y x && (y != x) then muBot L y else 0) := by
  have hpos : 0 < L.rk x := by
    have := L.rk_mono_strict L.bot x (L.bot_le x) (Ne.symm hx)
    have hb0 := L.rk_bot
    omega
  unfold muBot
  rcases Nat.exists_eq_succ_of_ne_zero (by omega : L.rk x ≠ 0) with ⟨r', hr'⟩
  have h1 : muBotAux L (L.rk x) x = muBotAux L (r' + 1) x := by rw [hr']
  rw [h1]
  have hbeq : (x == L.bot) = false := beq_false_of_ne hx
  simp only [muBotAux, hbeq]
  have hcongr : ∀ y : Fin L.size,
      (if (L.le y x && (y != x)) = true then muBotAux L r' y else 0) =
      (if (L.le y x && (y != x)) = true then muBotAux L (L.rk y) y else 0) := by
    intro y
    by_cases hy : (L.le y x && (y != x)) = true
    · simp only [hy, if_pos rfl]
      simp only [Bool.and_eq_true, bne_iff_ne] at hy
      have hyrk := L.rk_mono_strict y x hy.1 hy.2
      exact muBotAux_stable L (L.rk y) r' (L.rk y) y (Nat.le_refl _) (by omega) (Nat.le_refl _)
    · simp only [hy, if_neg Bool.false_ne_true]
  rw [sumFin_congr hcongr]
  simp

/-- Möbius interval identity: `∑_{y ≤ x} μ_L(⊥, y) = 0` for every `x ≠ ⊥`. -/
theorem muBot_interval_sum_zero (L : GeometricLattice) (x : Fin L.size) (hx : x ≠ L.bot) :
    sumFin L.size (fun y => if L.le y x then muBot L y else 0) = 0 := by
  have hsplit : ∀ y : Fin L.size,
      (if L.le y x = true then muBot L y else 0) =
      (if (L.le y x && (y != x)) = true then muBot L y else 0) +
      (if y == x then muBot L x else 0) := by
    intro y
    by_cases hyx : y = x
    · subst hyx
      simp [L.le_refl]
    · have hbne : (y != x) = true := bne_iff_ne.mpr hyx
      have hbeq : (y == x) = false := beq_false_of_ne hyx
      by_cases hle : L.le y x = true <;> simp [hle, hbne, hbeq]
  rw [sumFin_congr hsplit, sumFin_add, sumFin_single, muBot_ne_bot L x hx]
  omega

/-- `k`-th signed Whitney number of the first kind `w_k(L) = ∑_{rk(x)=k} μ_L(⊥, x)`. -/
def whitneyFirstSignedAt (L : GeometricLattice) (k : Nat) : Int :=
  sumFin L.size (fun x => if L.rk x == k then muBot L x else 0)

/-- `k`-th unsigned Whitney number of the first kind `|w_k(L)|`. -/
def whitneyFirstUnsignedAt (L : GeometricLattice) (k : Nat) : Nat :=
  (whitneyFirstSignedAt L k).natAbs

/-- Unsigned Whitney numbers of the first kind `(|w_0(L)|, |w_1(L)|, ..., |w_r(L)|)`. -/
def whitneyFirstUnsigned (L : GeometricLattice) : List Nat :=
  mapRangeAux (whitneyFirstUnsignedAt L) (L.rank + 1) 0

theorem whitneyFirstUnsigned_length (L : GeometricLattice) :
    (whitneyFirstUnsigned L).length = L.rank + 1 :=
  mapRangeAux_length _ _ _

theorem whitneyFirstUnsigned_getElem (L : GeometricLattice) (k : Nat)
    (hk : k < (whitneyFirstUnsigned L).length) :
    (whitneyFirstUnsigned L)[k] = whitneyFirstUnsignedAt L k := by
  unfold whitneyFirstUnsigned
  rw [mapRangeAux_getElem (whitneyFirstUnsignedAt L) (L.rank + 1) 0 k hk, Nat.zero_add]

/-! ## 4. Determinants, Total Unimodularity, and Matroid Representations -/

/-- Pure structural index-skipping map (avoids `dite` during kernel reduction). -/
def skipNat : Nat → Nat → Nat
  | 0, i => i + 1
  | _ + 1, 0 => 0
  | j + 1, i + 1 => skipNat j i + 1

theorem skipNat_lt : ∀ {k : Nat} (j i : Nat), j < k + 1 → i < k → skipNat j i < k + 1
  | _, 0, _, _, hi => Nat.succ_lt_succ hi
  | k, _ + 1, 0, _, _ => Nat.zero_lt_succ k
  | 0, _ + 1, _ + 1, _, hi => absurd hi (Nat.not_lt_zero _)
  | _ + 1, j + 1, i + 1, hj, hi =>
      Nat.succ_lt_succ (skipNat_lt j i (Nat.lt_of_succ_lt_succ hj) (Nat.lt_of_succ_lt_succ hi))

/-- Order-preserving index map skipping `j`. -/
def skipIdx {k : Nat} (j : Fin (k + 1)) (i : Fin k) : Fin (k + 1) :=
  ⟨skipNat j.val i.val, skipNat_lt j.val i.val j.isLt i.isLt⟩

/-- `(0, j)`-minor of a `(k + 1) × (k + 1)` matrix. -/
def minor0 {k : Nat} (M : Fin (k + 1) → Fin (k + 1) → Int) (j : Fin (k + 1)) :
    Fin k → Fin k → Int :=
  fun r c => M ⟨r.val + 1, Nat.succ_lt_succ r.isLt⟩ (skipIdx j c)

/-- Alternating sign `(-1)^n`. -/
def altSign : Nat → Int
  | 0 => 1
  | n + 1 => - altSign n

/-- Determinant of a `k × k` integer matrix via Laplace expansion along row 0. -/
def det : {k : Nat} → (Fin k → Fin k → Int) → Int
  | 0, _ => 1
  | k + 1, M =>
      sumFin (k + 1) (fun j => altSign j.val * M ⟨0, Nat.zero_lt_succ k⟩ j * det (minor0 M j))

/-- `k × k` submatrix of `A` selected by `rows` and `cols`. -/
def submatrix {m n k : Nat} (A : Fin m → Fin n → Int)
    (rows : Fin k → Fin m) (cols : Fin k → Fin n) : Fin k → Fin k → Int :=
  fun i j => A (rows i) (cols j)

/-- Strict monotonicity on finite index maps (canonical row/column submatrix selection). -/
def StrictMonoFin {k m : Nat} (f : Fin k → Fin m) : Prop :=
  ∀ i j : Fin k, i.val < j.val → (f i).val < (f j).val

theorem strictMonoFin_bound {k m : Nat} {f : Fin k → Fin m} (hf : StrictMonoFin f) : k ≤ m := by
  have step : ∀ (v : Nat) (hv : v < k), v ≤ (f ⟨v, hv⟩).val := by
    intro v
    induction v with
    | zero => intro _; exact Nat.zero_le _
    | succ u ih =>
      intro hu
      have hu' : u < k := Nat.lt_of_succ_lt hu
      have h1 := ih hu'
      have h2 := hf ⟨u, hu'⟩ ⟨u + 1, hu⟩ (Nat.lt_succ_self u)
      omega
  cases k with
  | zero => exact Nat.zero_le _
  | succ k' =>
    have hk := step k' (Nat.lt_succ_self k')
    have hlt := (f ⟨k', Nat.lt_succ_self k'⟩).isLt
    omega

/-- An `m × n` integer matrix is totally unimodular iff every `k × k` submatrix has
    determinant in `{-1, 0, 1}`. -/
def IsTotallyUnimodular {m n : Nat} (A : Fin m → Fin n → Int) : Prop :=
  ∀ (k : Nat) (rows : Fin k → Fin m) (cols : Fin k → Fin n),
    StrictMonoFin rows → StrictMonoFin cols →
    let d := det (submatrix A rows cols)
    d = -1 ∨ d = 0 ∨ d = 1

/-- Bijection between `Fin n` and the atoms of `L`. -/
structure AtomIndexing (L : GeometricLattice) (n : Nat) where
  atomOf : Fin n → Fin L.size
  is_atom : ∀ i : Fin n, Covers L.le L.bot (atomOf i)
  inj : ∀ i j : Fin n, atomOf i = atomOf j → i = j
  surj : ∀ a : Fin L.size, Covers L.le L.bot a → ∃ i : Fin n, atomOf i = a

/-- Join of a subset `S : Fin n → Bool` of indexed atoms in `L`. -/
def joinSubsetAux (L : GeometricLattice) {n : Nat} (atomOf : Fin n → Fin L.size)
    (S : Fin n → Bool) : (k : Nat) → k ≤ n → Fin L.size
  | 0, _ => L.bot
  | k + 1, hk =>
      let prev := joinSubsetAux L atomOf S k (Nat.le_of_succ_le hk)
      let i : Fin n := ⟨k, hk⟩
      if S i then L.join prev (atomOf i) else prev

def joinSubset (L : GeometricLattice) {n : Nat} (atomOf : Fin n → Fin L.size)
    (S : Fin n → Bool) : Fin L.size :=
  joinSubsetAux L atomOf S n (Nat.le_refl n)

theorem le_joinSubsetAux (L : GeometricLattice) {n : Nat} (atomOf : Fin n → Fin L.size)
    (S : Fin n → Bool) :
    ∀ (k : Nat) (hk : k ≤ n) (j : Fin n),
      j.val < k → S j = true → L.le (atomOf j) (joinSubsetAux L atomOf S k hk) = true := by
  intro k
  induction k with
  | zero =>
    intro _ j hj _
    exact absurd hj (Nat.not_lt_zero _)
  | succ m ih =>
    intro hk j hj hSj
    simp only [joinSubsetAux]
    let prev := joinSubsetAux L atomOf S m (Nat.le_of_succ_le hk)
    let im : Fin n := ⟨m, hk⟩
    have hjoin_ub : ∀ a b : Fin L.size, L.le a (L.join a b) = true ∧ L.le b (L.join a b) = true :=
      fun a b => (L.join_spec a b (L.join a b)).mp (L.le_refl _)
    by_cases hjm : j.val < m
    · have hprev := ih (Nat.le_of_succ_le hk) j hjm hSj
      cases hSim : S im
      · simp only [if_neg Bool.false_ne_true]; exact hprev
      · simp only [if_pos rfl]
        exact L.le_trans _ _ _ hprev (hjoin_ub prev (atomOf im)).1
    · have hjeq : j = ⟨m, hk⟩ := Fin.ext (show j.val = m by omega)
      rw [← hjeq, hSj, if_pos rfl]
      exact (hjoin_ub prev (atomOf j)).2

theorem le_joinSubset (L : GeometricLattice) {n : Nat} (atomOf : Fin n → Fin L.size)
    (S : Fin n → Bool) (j : Fin n) (hSj : S j = true) :
    L.le (atomOf j) (joinSubset L atomOf S) = true :=
  le_joinSubsetAux L atomOf S n (Nat.le_refl n) j j.isLt hSj

/-- Existence of a non-vanishing `d × d` minor over `ℚ` on column subset `S`. -/
def HasNonzeroMinorQ {m n : Nat} (A : Fin m → Fin n → Int) (S : Fin n → Bool) (d : Nat) : Prop :=
  ∃ (rows : Fin d → Fin m) (cols : Fin d → Fin n),
    StrictMonoFin rows ∧ StrictMonoFin cols ∧
    (∀ j : Fin d, S (cols j) = true) ∧
    det (submatrix A rows cols) ≠ 0

/-- `A` represents `L` over `ℚ` (determinantal column rank matches lattice flat rank). -/
def RepresentsOverQ (L : GeometricLattice) {m n : Nat}
    (idx : AtomIndexing L n) (A : Fin m → Fin n → Int) : Prop :=
  ∀ S : Fin n → Bool,
    let r := L.rk (joinSubset L idx.atomOf S)
    HasNonzeroMinorQ A S r ∧ ∀ d : Nat, r < d → ¬ HasNonzeroMinorQ A S d

/-- Existence of a non-vanishing `d × d` minor over `𝔽₂` on column subset `S`. -/
def HasNonzeroMinorF2 {m n : Nat} (A : Fin m → Fin n → Int) (S : Fin n → Bool) (d : Nat) : Prop :=
  ∃ (rows : Fin d → Fin m) (cols : Fin d → Fin n),
    StrictMonoFin rows ∧ StrictMonoFin cols ∧
    (∀ j : Fin d, S (cols j) = true) ∧
    det (submatrix A rows cols) % 2 ≠ 0

/-- `A` represents `L` over `𝔽₂`. -/
def RepresentsOverF2 (L : GeometricLattice) {m n : Nat}
    (idx : AtomIndexing L n) (A : Fin m → Fin n → Int) : Prop :=
  ∀ S : Fin n → Bool,
    let r := L.rk (joinSubset L idx.atomOf S)
    HasNonzeroMinorF2 A S r ∧ ∀ d : Nat, r < d → ¬ HasNonzeroMinorF2 A S d

/-- A geometric lattice is unimodular (regular) iff it admits a representation over `ℚ`
    by a totally unimodular integer matrix of arbitrary row dimension `m`. -/
def IsUnimodular (L : GeometricLattice) : Prop :=
  ∃ (m n : Nat) (idx : AtomIndexing L n) (A : Fin m → Fin n → Int),
    IsTotallyUnimodular A ∧ RepresentsOverQ L idx A

/-- A geometric lattice is binary iff it admits a representation over `𝔽₂`. -/
def IsBinary (L : GeometricLattice) : Prop :=
  ∃ (m n : Nat) (idx : AtomIndexing L n) (A : Fin m → Fin n → Int),
    RepresentsOverF2 L idx A

/-- Tutte's bridge lemma: every unimodular geometric lattice is binary (`𝔽₂`-representable),
    since reducing a totally unimodular matrix modulo `2` preserves all non-vanishing minors. -/
theorem unimodular_implies_binary (L : GeometricLattice) : IsUnimodular L → IsBinary L := by
  rintro ⟨m, n, idx, A, hTU, hRepQ⟩
  refine ⟨m, n, idx, A, ?_⟩
  have hiff : ∀ (S : Fin n → Bool) (d : Nat),
      HasNonzeroMinorQ A S d ↔ HasNonzeroMinorF2 A S d := by
    intro S d
    constructor
    · rintro ⟨rows, cols, hrm, hcm, hS, hdet⟩
      refine ⟨rows, cols, hrm, hcm, hS, ?_⟩
      rcases hTU d rows cols hrm hcm with h | h | h <;> omega
    · rintro ⟨rows, cols, hrm, hcm, hS, hdet2⟩
      refine ⟨rows, cols, hrm, hcm, hS, ?_⟩
      omega
  intro S
  rcases hRepQ S with ⟨h1, h2⟩
  exact ⟨(hiff S _).mp h1, fun d hd hF2 => h2 d hd ((hiff S d).mpr hF2)⟩

/-! ## 5. Verified Decidable Constructors for Concrete Lattices and Representations -/

def checkGeometricLattice (sz : Nat) (le : Fin sz → Fin sz → Bool)
    (join meet : Fin sz → Fin sz → Fin sz) (bot top : Fin sz) (rk : Fin sz → Nat) : Bool :=
  -- 1. le_refl
  allFin sz (fun x => le x x) &&
  -- 2. le_antisymm
  allFin sz (fun x => allFin sz (fun y => !(le x y && le y x) || (x == y))) &&
  -- 3. le_trans
  allFin sz (fun x => allFin sz (fun y => allFin sz (fun z => !(le x y && le y z) || le x z))) &&
  -- 4. bot_le & le_top
  allFin sz (fun x => le bot x && le x top) &&
  -- 5. join_spec
  allFin sz (fun x => allFin sz (fun y => allFin sz (fun z =>
    le (join x y) z == (le x z && le y z)))) &&
  -- 6. meet_spec
  allFin sz (fun x => allFin sz (fun y => allFin sz (fun z =>
    le z (meet x y) == (le z x && le z y)))) &&
  -- 7. rk_bot
  (rk bot == 0) &&
  -- 8. rk_mono_strict
  allFin sz (fun x => allFin sz (fun y => !(le x y && (x != y)) || decide (rk x < rk y))) &&
  -- 9. rk_cover
  allFin sz (fun x => allFin sz (fun y => !coversBool le x y || (rk y == rk x + 1))) &&
  -- 10. cover_below
  allFin sz (fun x => (x == bot) || anyFin sz (fun w => coversBool le w x)) &&
  -- 11. semimodular
  allFin sz (fun x => allFin sz (fun y => decide (rk (join x y) + rk (meet x y) ≤ rk x + rk y))) &&
  -- 12. atomic
  allFin sz (fun x => allFin sz (fun u =>
    !(allFin sz (fun a => !(coversBool le bot a && le a x) || le a u)) || le x u))

theorem checkGeometricLattice_sound (sz : Nat) (le : Fin sz → Fin sz → Bool)
    (join meet : Fin sz → Fin sz → Fin sz) (bot top : Fin sz) (rk : Fin sz → Nat)
    (h : checkGeometricLattice sz le join meet bot top rk = true) :
    (∀ x : Fin sz, le x x = true) ∧
    (∀ x y : Fin sz, le x y = true → le y x = true → x = y) ∧
    (∀ x y z : Fin sz, le x y = true → le y z = true → le x z = true) ∧
    (∀ x : Fin sz, le bot x = true) ∧
    (∀ x : Fin sz, le x top = true) ∧
    (∀ x y z : Fin sz, le (join x y) z = true ↔ (le x z = true ∧ le y z = true)) ∧
    (∀ x y z : Fin sz, le z (meet x y) = true ↔ (le z x = true ∧ le z y = true)) ∧
    (rk bot = 0) ∧
    (∀ x y : Fin sz, le x y = true → x ≠ y → rk x < rk y) ∧
    (∀ x y : Fin sz, Covers le x y → rk y = rk x + 1) ∧
    (∀ x : Fin sz, x ≠ bot → ∃ w : Fin sz, Covers le w x) ∧
    (∀ x y : Fin sz, rk (join x y) + rk (meet x y) ≤ rk x + rk y) ∧
    (∀ x u : Fin sz,
      (∀ a : Fin sz, Covers le bot a → le a x = true → le a u = true) → le x u = true) := by
  simp only [checkGeometricLattice, band_iff] at h
  rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩
  refine ⟨allFin_eq_true.mp h1, ?_, ?_,
          fun x => (band_iff.mp (allFin_eq_true.mp h4 x)).1,
          fun x => (band_iff.mp (allFin_eq_true.mp h4 x)).2,
          ?_, ?_, beq_iff_eq.mp h7, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y hxy hyx
    have hx := allFin_eq_true.mp (allFin_eq_true.mp h2 x) y
    rw [hxy, hyx] at hx
    exact beq_iff_eq.mp hx
  · intro x y z hxy hyz
    have hx := allFin_eq_true.mp (allFin_eq_true.mp (allFin_eq_true.mp h3 x) y) z
    rw [hxy, hyz] at hx
    exact hx
  · intro x y z
    have hx := beq_iff_eq.mp (allFin_eq_true.mp (allFin_eq_true.mp (allFin_eq_true.mp h5 x) y) z)
    rw [hx, band_iff]
  · intro x y z
    have hx := beq_iff_eq.mp (allFin_eq_true.mp (allFin_eq_true.mp (allFin_eq_true.mp h6 x) y) z)
    rw [hx, band_iff]
  · intro x y hxy hne
    have hx := allFin_eq_true.mp (allFin_eq_true.mp h8 x) y
    have hbne : (x != y) = true := bne_iff_ne.mpr hne
    rw [hxy, hbne] at hx
    exact of_decide_eq_true hx
  · intro x y hcov
    have hx := allFin_eq_true.mp (allFin_eq_true.mp h9 x) y
    have hc : coversBool le x y = true := coversBool_eq_true.mpr hcov
    rw [hc] at hx
    exact beq_iff_eq.mp hx
  · intro x hne
    have hx := allFin_eq_true.mp h10 x
    have hbeq : (x == bot) = false := beq_false_of_ne hne
    rw [hbeq, Bool.false_or] at hx
    rcases anyFin_eq_true.mp hx with ⟨w, hw⟩
    exact ⟨w, coversBool_eq_true.mp hw⟩
  · intro x y
    exact of_decide_eq_true (allFin_eq_true.mp (allFin_eq_true.mp h11 x) y)
  · intro x u hall
    have hx := allFin_eq_true.mp (allFin_eq_true.mp h12 x) u
    have hprem : allFin sz (fun a => !(coversBool le bot a && le a x) || le a u) = true := by
      apply allFin_eq_true.mpr
      intro a
      by_cases hc : (coversBool le bot a && le a x) = true
      · simp only [hc, Bool.not_true, Bool.false_or]
        rcases band_iff.mp hc with ⟨hca, hax⟩
        exact hall a (coversBool_eq_true.mp hca) hax
      · simp [hc]
    rw [hprem] at hx
    exact hx

def mkGeometricLattice (sz : Nat) (le : Fin sz → Fin sz → Bool)
    (join meet : Fin sz → Fin sz → Fin sz) (bot top : Fin sz) (rk : Fin sz → Nat)
    (h : checkGeometricLattice sz le join meet bot top rk = true) : GeometricLattice :=
  let s := checkGeometricLattice_sound sz le join meet bot top rk h
  { size := sz
    le := le
    join := join
    meet := meet
    bot := bot
    top := top
    rk := rk
    le_refl := s.1
    le_antisymm := s.2.1
    le_trans := s.2.2.1
    bot_le := s.2.2.2.1
    le_top := s.2.2.2.2.1
    join_spec := s.2.2.2.2.2.1
    meet_spec := s.2.2.2.2.2.2.1
    rk_bot := s.2.2.2.2.2.2.2.1
    rk_mono_strict := s.2.2.2.2.2.2.2.2.1
    rk_cover := s.2.2.2.2.2.2.2.2.2.1
    cover_below := s.2.2.2.2.2.2.2.2.2.2.1
    semimodular := s.2.2.2.2.2.2.2.2.2.2.2.1
    atomic := s.2.2.2.2.2.2.2.2.2.2.2.2 }

/-- Append `last : Fin m` onto `init : Fin k → Fin last.val` to get `Fin (k + 1) → Fin m`. -/
def snocStrict {k m : Nat} (last : Fin m) (init : Fin k → Fin last.val) : Fin (k + 1) → Fin m :=
  fun i =>
    if h : i.val < k then
      ⟨(init ⟨i.val, h⟩).val, Nat.lt_trans (init ⟨i.val, h⟩).isLt last.isLt⟩
    else
      last

/-- Enumerate strictly increasing maps `Fin k → Fin m` (universal). -/
def allStrictMono : (k m : Nat) → ((Fin k → Fin m) → Bool) → Bool
  | 0, _, p => p (fun i => absurd i.isLt (Nat.not_lt_zero _))
  | k + 1, m, p =>
      allFin m (fun last => allStrictMono k last.val (fun init => p (snocStrict last init)))

/-- Enumerate strictly increasing maps `Fin k → Fin m` (existential). -/
def anyStrictMono : (k m : Nat) → ((Fin k → Fin m) → Bool) → Bool
  | 0, _, p => p (fun i => absurd i.isLt (Nat.not_lt_zero _))
  | k + 1, m, p =>
      anyFin m (fun last => anyStrictMono k last.val (fun init => p (snocStrict last init)))

theorem snocStrict_strictMono {k m : Nat} (last : Fin m) (init : Fin k → Fin last.val)
    (hinit : StrictMonoFin init) : StrictMonoFin (snocStrict last init) := by
  intro i j hij
  simp only [snocStrict]
  by_cases hik : i.val < k
  · by_cases hjk : j.val < k
    · simp only [dif_pos hik, dif_pos hjk]
      exact hinit ⟨i.val, hik⟩ ⟨j.val, hjk⟩ hij
    · simp only [dif_pos hik, dif_neg hjk]
      exact (init ⟨i.val, hik⟩).isLt
  · exfalso
    have : j.val ≤ k := by omega
    omega

theorem strictMono_decomp {k m : Nat} (f : Fin (k + 1) → Fin m) (hf : StrictMonoFin f) :
    let last := f ⟨k, Nat.lt_succ_self k⟩
    ∃ init : Fin k → Fin last.val, StrictMonoFin init ∧ f = snocStrict last init := by
  let last := f ⟨k, Nat.lt_succ_self k⟩
  let init : Fin k → Fin last.val := fun i =>
    ⟨(f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩).val,
     hf ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ ⟨k, Nat.lt_succ_self k⟩ i.isLt⟩
  refine ⟨init, ?_, ?_⟩
  · intro i j hij
    exact hf ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ hij
  · funext ⟨v, hv⟩
    simp only [snocStrict]
    by_cases hvk : v < k
    · simp only [dif_pos hvk]; rfl
    · simp only [dif_neg hvk]
      have heq : v = k := by omega
      subst heq; rfl

theorem allStrictMono_eq_true {k : Nat} :
    ∀ {m : Nat} {p : (Fin k → Fin m) → Bool},
      allStrictMono k m p = true ↔ ∀ f : Fin k → Fin m, StrictMonoFin f → p f = true := by
  induction k with
  | zero =>
    intro m p
    simp only [allStrictMono]
    constructor
    · intro h0 f _
      have heq : f = (fun i => absurd i.isLt (Nat.not_lt_zero _)) := by
        funext i; exact absurd i.isLt (Nat.not_lt_zero _)
      rw [heq]; exact h0
    · intro hall
      exact hall _ (fun i => absurd i.isLt (Nat.not_lt_zero _))
  | succ k' ih =>
    intro m p
    simp only [allStrictMono, allFin_eq_true]
    constructor
    · intro hall f hf
      rcases strictMono_decomp f hf with ⟨init, hinit, hfeq⟩
      rw [hfeq]
      exact (ih.mp (hall (f ⟨k', Nat.lt_succ_self k'⟩))) init hinit
    · intro hall last
      apply ih.mpr
      intro init hinit
      exact hall (snocStrict last init) (snocStrict_strictMono last init hinit)

theorem anyStrictMono_eq_true {k : Nat} :
    ∀ {m : Nat} {p : (Fin k → Fin m) → Bool},
      anyStrictMono k m p = true ↔ ∃ f : Fin k → Fin m, StrictMonoFin f ∧ p f = true := by
  induction k with
  | zero =>
    intro m p
    simp only [allStrictMono, anyStrictMono]
    constructor
    · intro h0
      exact ⟨fun i => absurd i.isLt (Nat.not_lt_zero _),
             fun i => absurd i.isLt (Nat.not_lt_zero _), h0⟩
    · rintro ⟨f, _, hf⟩
      have heq : f = (fun i => absurd i.isLt (Nat.not_lt_zero _)) := by
        funext i; exact absurd i.isLt (Nat.not_lt_zero _)
      rw [← heq]; exact hf
  | succ k' ih =>
    intro m p
    simp only [anyStrictMono, anyFin_eq_true]
    constructor
    · rintro ⟨last, hlast⟩
      rcases ih.mp hlast with ⟨init, hinit, hp⟩
      exact ⟨snocStrict last init, snocStrict_strictMono last init hinit, hp⟩
    · rintro ⟨f, hf, hp⟩
      rcases strictMono_decomp f hf with ⟨init, hinit, hfeq⟩
      refine ⟨f ⟨k', Nat.lt_succ_self k'⟩, ih.mpr ⟨init, hinit, ?_⟩⟩
      rw [← hfeq]; exact hp

/-- Enumerate all boolean subsets `Fin n → Bool`. -/
def snocBool {n : Nat} (b : Bool) (init : Fin n → Bool) : Fin (n + 1) → Bool :=
  fun i => if h : i.val < n then init ⟨i.val, h⟩ else b

def allSubsets : (n : Nat) → ((Fin n → Bool) → Bool) → Bool
  | 0, p => p (fun i => absurd i.isLt (Nat.not_lt_zero _))
  | n + 1, p =>
      allSubsets n (fun init => p (snocBool false init) && p (snocBool true init))

theorem allSubsets_eq_true {n : Nat} :
    ∀ {p : (Fin n → Bool) → Bool},
      allSubsets n p = true ↔ ∀ S : Fin n → Bool, p S = true := by
  induction n with
  | zero =>
    intro p
    simp only [allSubsets]
    constructor
    · intro h0 S
      have heq : S = (fun i => absurd i.isLt (Nat.not_lt_zero _)) := by
        funext i; exact absurd i.isLt (Nat.not_lt_zero _)
      rw [heq]; exact h0
    · intro hall; exact hall _
  | succ m ih =>
    intro p
    simp only [allSubsets, ih]
    constructor
    · intro hall S
      let init : Fin m → Bool := fun i => S ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩
      have hpair := band_iff.mp (hall init)
      have hSeq : S = snocBool (S ⟨m, Nat.lt_succ_self m⟩) init := by
        funext ⟨v, hv⟩
        simp only [snocBool]
        by_cases hvm : v < m
        · simp only [dif_pos hvm]; rfl
        · simp only [dif_neg hvm]
          have heq : v = m := by omega
          subst heq; rfl
      rw [hSeq]
      cases S ⟨m, Nat.lt_succ_self m⟩
      · exact hpair.1
      · exact hpair.2
    · intro hall init
      exact band_iff.mpr ⟨hall _, hall _⟩

def checkAtomIndexing (L : GeometricLattice) (n : Nat) (atomOf : Fin n → Fin L.size) : Bool :=
  allFin n (fun i => coversBool L.le L.bot (atomOf i)) &&
  allFin n (fun i => allFin n (fun j => !(atomOf i == atomOf j) || (i == j))) &&
  allFin L.size (fun a => !coversBool L.le L.bot a || anyFin n (fun i => atomOf i == a))

theorem checkAtomIndexing_sound (L : GeometricLattice) (n : Nat)
    (atomOf : Fin n → Fin L.size) (h : checkAtomIndexing L n atomOf = true) :
    (∀ i : Fin n, Covers L.le L.bot (atomOf i)) ∧
    (∀ i j : Fin n, atomOf i = atomOf j → i = j) ∧
    (∀ a : Fin L.size, Covers L.le L.bot a → ∃ i : Fin n, atomOf i = a) := by
  simp only [checkAtomIndexing, band_iff] at h
  rcases h with ⟨⟨h1, h2⟩, h3⟩
  refine ⟨?_, ?_, ?_⟩
  · intro i; exact coversBool_eq_true.mp (allFin_eq_true.mp h1 i)
  · intro i j heq
    have hi := allFin_eq_true.mp (allFin_eq_true.mp h2 i) j
    rw [beq_iff_eq.mpr heq] at hi
    exact beq_iff_eq.mp hi
  · intro a ha
    have ha' := allFin_eq_true.mp h3 a
    rw [coversBool_eq_true.mpr ha] at ha'
    rcases anyFin_eq_true.mp ha' with ⟨i, hi⟩
    exact ⟨i, beq_iff_eq.mp hi⟩

def mkAtomIndexing (L : GeometricLattice) (n : Nat) (atomOf : Fin n → Fin L.size)
    (h : checkAtomIndexing L n atomOf = true) : AtomIndexing L n :=
  let s := checkAtomIndexing_sound L n atomOf h
  { atomOf := atomOf, is_atom := s.1, inj := s.2.1, surj := s.2.2 }

def hasNonzeroMinorQBool {m n : Nat} (A : Fin m → Fin n → Int)
    (S : Fin n → Bool) (d : Nat) : Bool :=
  anyStrictMono d m (fun rows =>
    anyStrictMono d n (fun cols =>
      allFin d (fun j => S (cols j)) && (det (submatrix A rows cols) != 0)))

theorem hasNonzeroMinorQBool_eq_true {m n : Nat} {A : Fin m → Fin n → Int}
    {S : Fin n → Bool} {d : Nat} :
    hasNonzeroMinorQBool A S d = true ↔ HasNonzeroMinorQ A S d := by
  simp only [hasNonzeroMinorQBool, HasNonzeroMinorQ, anyStrictMono_eq_true]
  constructor
  · rintro ⟨rows, hrm, cols, hcm, hrest⟩
    rcases band_iff.mp hrest with ⟨hS, hdet⟩
    exact ⟨rows, cols, hrm, hcm, allFin_eq_true.mp hS, bne_iff_ne.mp hdet⟩
  · rintro ⟨rows, cols, hrm, hcm, hS, hdet⟩
    exact ⟨rows, hrm, cols, hcm,
      band_iff.mpr ⟨allFin_eq_true.mpr hS, bne_iff_ne.mpr hdet⟩⟩

def checkUnimodularRep (L : GeometricLattice) (m n : Nat)
    (idx : AtomIndexing L n) (A : Fin m → Fin n → Int) : Bool :=
  allFin (m + 1) (fun k =>
    allStrictMono k.val m (fun rows =>
      allStrictMono k.val n (fun cols =>
        let d := det (submatrix A rows cols)
        (d == -1) || (d == 0) || (d == 1)))) &&
  allSubsets n (fun S =>
    let r := L.rk (joinSubset L idx.atomOf S)
    hasNonzeroMinorQBool A S r &&
    allFin (m + 1) (fun d => !decide (r < d.val) || !hasNonzeroMinorQBool A S d.val))

theorem mkIsUnimodular (L : GeometricLattice) (m n : Nat)
    (idx : AtomIndexing L n) (A : Fin m → Fin n → Int)
    (h : checkUnimodularRep L m n idx A = true) : IsUnimodular L := by
  rcases band_iff.mp h with ⟨hTU_bool, hRep_bool⟩
  refine ⟨m, n, idx, A, ?_, ?_⟩
  · intro k rows cols hrm hcm
    have hkm : k ≤ m := strictMonoFin_bound hrm
    have hk := allFin_eq_true.mp hTU_bool ⟨k, Nat.lt_succ_of_le hkm⟩
    have hrc := (allStrictMono_eq_true.mp ((allStrictMono_eq_true.mp hk) rows hrm)) cols hcm
    simp only [Bool.or_eq_true, beq_iff_eq] at hrc
    rcases hrc with (h1 | h0) | hp1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h0)
    · exact Or.inr (Or.inr hp1)
  · intro S
    have hS := allSubsets_eq_true.mp hRep_bool S
    rcases band_iff.mp hS with ⟨h1, h2⟩
    refine ⟨hasNonzeroMinorQBool_eq_true.mp h1, ?_⟩
    intro d hrd hminor
    rcases hminor with ⟨rows, cols, hrm, hcm, hcolsS, hdet⟩
    have hdm : d ≤ m := strictMonoFin_bound hrm
    have hd_chk := allFin_eq_true.mp h2 ⟨d, Nat.lt_succ_of_le hdm⟩
    rw [decide_eq_true hrd, Bool.not_true, Bool.false_or] at hd_chk
    have htrue : hasNonzeroMinorQBool A S d = true :=
      hasNonzeroMinorQBool_eq_true.mpr ⟨rows, cols, hrm, hcm, hcolsS, hdet⟩
    rw [htrue] at hd_chk
    cases hd_chk

/-! ## 6. Concrete Geometric Lattices (Bitmask Construction of Uniform Flats) -/

/-- Find the first index in `masks` matching `target` (defaults to `0`). -/
def findMaskIdxAux {sz : Nat} (masks : Fin sz → Nat) (target : Nat) : (k : Nat) → k ≤ sz → Nat
  | 0, _ => 0
  | k + 1, hk =>
      if masks ⟨k, hk⟩ == target then k
      else findMaskIdxAux masks target k (Nat.le_of_succ_le hk)

def findMaskFin {sz : Nat} (hpos : 0 < sz) (masks : Fin sz → Nat) (target : Nat) : Fin sz :=
  let idx := findMaskIdxAux masks target sz (Nat.le_refl sz)
  if h : idx < sz then ⟨idx, h⟩ else ⟨0, hpos⟩

/-- Smallest flat (first in rank-ordered `masks`) containing bitmask `sub`. -/
def closureMaskAux {sz : Nat} (masks : Fin sz → Nat) (sub : Nat) : (k : Nat) → k ≤ sz → Nat
  | 0, _ => sz - 1
  | k + 1, hk =>
      let rest := closureMaskAux masks sub k (Nat.le_of_succ_le hk)
      let idx := sz - 1 - k
      have hidx : idx < sz := by omega
      if (masks ⟨idx, hidx⟩ &&& sub) == sub then idx else rest

def closureMaskFin {sz : Nat} (hpos : 0 < sz) (masks : Fin sz → Nat) (sub : Nat) : Fin sz :=
  let idx := closureMaskAux masks sub sz (Nat.le_refl sz)
  if h : idx < sz then ⟨idx, h⟩ else ⟨0, hpos⟩

/-- Build `(le, join, meet)` from rank-sorted flat bitmasks. -/
def maskLe {sz : Nat} (masks : Fin sz → Nat) (x y : Fin sz) : Bool :=
  (masks x &&& masks y) == masks x

def maskMeet {sz : Nat} (hpos : 0 < sz) (masks : Fin sz → Nat) (x y : Fin sz) : Fin sz :=
  findMaskFin hpos masks (masks x &&& masks y)

def maskJoin {sz : Nat} (hpos : 0 < sz) (masks : Fin sz → Nat) (x y : Fin sz) : Fin sz :=
  closureMaskFin hpos masks (masks x ||| masks y)

/-- Boolean lattice `B₁ ≅ L(U_{1,1})` of rank `1` (2 elements). -/
def masksB1 : Fin 2 → Nat := fun i => match i.val with | 0 => 0 | _ => 1
def rkB1 : Fin 2 → Nat := fun i => match i.val with | 0 => 0 | _ => 1
def B1 : GeometricLattice :=
  mkGeometricLattice 2 (maskLe masksB1) (maskJoin (by omega) masksB1)
    (maskMeet (by omega) masksB1) ⟨0, by omega⟩ ⟨1, by omega⟩ rkB1 (by decide)

/-- Boolean lattice `B₂ ≅ L(U_{2,2})` of rank `2` (4 elements). -/
def masksB2 : Fin 4 → Nat := fun i =>
  match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | _ => 3
def rkB2 : Fin 4 → Nat := fun i =>
  match i.val with | 0 => 0 | 1 => 1 | 2 => 1 | _ => 2
def B2 : GeometricLattice :=
  mkGeometricLattice 4 (maskLe masksB2) (maskJoin (by omega) masksB2)
    (maskMeet (by omega) masksB2) ⟨0, by omega⟩ ⟨3, by omega⟩ rkB2 (by decide)

/-- Diamond lattice `M₃ ≅ L(U_{2,3}) ≅ L(M(K₃))` of rank `2` (5 elements). -/
def masksM3 : Fin 5 → Nat := fun i =>
  match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | _ => 7
def rkM3 : Fin 5 → Nat := fun i =>
  match i.val with | 0 => 0 | 1 => 1 | 2 => 1 | 3 => 1 | _ => 2
def M3 : GeometricLattice :=
  mkGeometricLattice 5 (maskLe masksM3) (maskJoin (by omega) masksM3)
    (maskMeet (by omega) masksM3) ⟨0, by omega⟩ ⟨4, by omega⟩ rkM3 (by decide)

/-- 4-point line geometric lattice `M₄ ≅ L(U_{2,4})` of rank `2` (6 elements). -/
def masksM4 : Fin 6 → Nat := fun i =>
  match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 8 | _ => 15
def rkM4 : Fin 6 → Nat := fun i =>
  match i.val with | 0 => 0 | 1 => 1 | 2 => 1 | 3 => 1 | 4 => 1 | _ => 2
def M4 : GeometricLattice :=
  mkGeometricLattice 6 (maskLe masksM4) (maskJoin (by omega) masksM4)
    (maskMeet (by omega) masksM4) ⟨0, by omega⟩ ⟨5, by omega⟩ rkM4 (by decide)

/-- Boolean lattice `B₃ ≅ L(U_{3,3})` of rank `3` (8 elements). -/
def masksB3 : Fin 8 → Nat := fun i =>
  match i.val with
  | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | _ => 7
def rkB3 : Fin 8 → Nat := fun i =>
  match i.val with
  | 0 => 0 | 1 => 1 | 2 => 1 | 3 => 1 | 4 => 2 | 5 => 2 | 6 => 2 | _ => 3
def B3 : GeometricLattice :=
  mkGeometricLattice 8 (maskLe masksB3) (maskJoin (by omega) masksB3)
    (maskMeet (by omega) masksB3) ⟨0, by omega⟩ ⟨7, by omega⟩ rkB3 (by decide)

/-- 4-cycle graphic lattice `L(U_{3,4}) ≅ L(M(C₄))` of rank `3` (12 elements). -/
def masksU34 : Fin 12 → Nat := fun i =>
  match i.val with
  | 0 => 0
  | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 8
  | 5 => 3 | 6 => 5 | 7 => 6 | 8 => 9 | 9 => 10 | 10 => 12
  | _ => 15
def rkU34 : Fin 12 → Nat := fun i =>
  match i.val with
  | 0 => 0
  | 1 => 1 | 2 => 1 | 3 => 1 | 4 => 1
  | 5 => 2 | 6 => 2 | 7 => 2 | 8 => 2 | 9 => 2 | 10 => 2
  | _ => 3
def LU34 : GeometricLattice :=
  mkGeometricLattice 12 (maskLe masksU34) (maskJoin (by omega) masksU34)
    (maskMeet (by omega) masksU34) ⟨0, by omega⟩ ⟨11, by omega⟩ rkU34 (by decide)

/-! ## 7. Unimodularity Witnesses (`B₁, B₂, M₃, B₃, L(U_{3,4})`) -/

def idxB1 : AtomIndexing B1 1 :=
  mkAtomIndexing B1 1 (fun _ => ⟨1, by decide⟩) (by decide)
def matB1 : Fin 1 → Fin 1 → Int := fun _ _ => 1
theorem isUnimodular_B1 : IsUnimodular B1 :=
  mkIsUnimodular B1 1 1 idxB1 matB1 (by decide)

def idxB2 : AtomIndexing B2 2 :=
  mkAtomIndexing B2 2 (fun i => ⟨i.val + 1, Nat.succ_lt_succ (Nat.lt_trans i.isLt (by decide))⟩) (by decide)
def matB2 : Fin 2 → Fin 2 → Int := fun i j => if i == j then 1 else 0
theorem isUnimodular_B2 : IsUnimodular B2 :=
  mkIsUnimodular B2 2 2 idxB2 matB2 (by decide)

def idxM3 : AtomIndexing M3 3 :=
  mkAtomIndexing M3 3 (fun i => ⟨i.val + 1, Nat.succ_lt_succ (Nat.lt_trans i.isLt (by decide))⟩) (by decide)
def matM3 : Fin 2 → Fin 3 → Int := fun i j =>
  match i.val, j.val with
  | 0, 0 => 1 | 0, 1 => 0 | 0, _ => 1
  | _, 0 => 0 | _, 1 => 1 | _, _ => 1
theorem isUnimodular_M3 : IsUnimodular M3 :=
  mkIsUnimodular M3 2 3 idxM3 matM3 (by decide)

def idxB3 : AtomIndexing B3 3 :=
  mkAtomIndexing B3 3 (fun i => ⟨i.val + 1, Nat.succ_lt_succ (Nat.lt_trans i.isLt (by decide))⟩) (by decide)
def matB3 : Fin 3 → Fin 3 → Int := fun i j => if i == j then 1 else 0
theorem isUnimodular_B3 : IsUnimodular B3 :=
  mkIsUnimodular B3 3 3 idxB3 matB3 (by decide)

def idxU34 : AtomIndexing LU34 4 :=
  mkAtomIndexing LU34 4 (fun i => ⟨i.val + 1, Nat.succ_lt_succ (Nat.lt_trans i.isLt (by decide))⟩) (by decide)
def matU34 : Fin 3 → Fin 4 → Int := fun i j =>
  if j.val == 3 then 1 else if i.val == j.val then 1 else 0
theorem isUnimodular_LU34 : IsUnimodular LU34 :=
  mkIsUnimodular LU34 3 4 idxU34 matU34 (by decide)

/-- `M₄` is modular, whereas `L(U_{3,4})` is unimodular yet NOT modular. -/
theorem isModular_M4 : IsModular M4 := by
  have h : allFin M4.size (fun x => allFin M4.size (fun y =>
      M4.rk (M4.join x y) + M4.rk (M4.meet x y) == M4.rk x + M4.rk y)) = true := by decide
  intro x y
  exact beq_iff_eq.mp (allFin_eq_true.mp (allFin_eq_true.mp h x) y)

theorem not_isModular_LU34 : ¬ IsModular LU34 := by
  intro hmod
  -- Disjoint rank-2 flats `{0,1}` (index 5) and `{2,3}` (index 10) satisfy `3 + 0 ≠ 2 + 2`.
  have h := hmod ⟨5, by decide⟩ ⟨10, by decide⟩
  revert h; decide

/-! ## 8. Proof that `M₄ ≅ L(U_{2,4})` is Neither Binary nor Unimodular -/

def det2 {m n : Nat} (A : Fin m → Fin n → Int) (r0 r1 : Fin m) (c0 c1 : Fin n) : Int :=
  A r0 c0 * A r1 c1 - A r0 c1 * A r1 c0

def det3 {m n : Nat} (A : Fin m → Fin n → Int)
    (r0 r1 r2 : Fin m) (c0 c1 c2 : Fin n) : Int :=
  A r0 c0 * (A r1 c1 * A r2 c2 - A r1 c2 * A r2 c1) -
  A r0 c1 * (A r1 c0 * A r2 c2 - A r1 c2 * A r2 c0) +
  A r0 c2 * (A r1 c0 * A r2 c1 - A r1 c1 * A r2 c0)

theorem det_submatrix_2 {m n : Nat} (A : Fin m → Fin n → Int)
    (rows : Fin 2 → Fin m) (cols : Fin 2 → Fin n) :
    det (submatrix A rows cols) =
      det2 A (rows ⟨0, by omega⟩) (rows ⟨1, by omega⟩)
             (cols ⟨0, by omega⟩) (cols ⟨1, by omega⟩) := by
  let a00 := A (rows ⟨0, by omega⟩) (cols ⟨0, by omega⟩)
  let a01 := A (rows ⟨0, by omega⟩) (cols ⟨1, by omega⟩)
  let a10 := A (rows ⟨1, by omega⟩) (cols ⟨0, by omega⟩)
  let a11 := A (rows ⟨1, by omega⟩) (cols ⟨1, by omega⟩)
  change ((0 + 1 * a00 * (0 + 1 * a11 * 1)) + (-1) * a01 * (0 + 1 * a10 * 1)) =
         (a00 * a11 - a01 * a10)
  generalize a00 = x00, a01 = x01, a10 = x10, a11 = x11
  int_ring

theorem det_submatrix_3 {m n : Nat} (A : Fin m → Fin n → Int)
    (rows : Fin 3 → Fin m) (cols : Fin 3 → Fin n) :
    det (submatrix A rows cols) =
      det3 A (rows ⟨0, by omega⟩) (rows ⟨1, by omega⟩) (rows ⟨2, by omega⟩)
             (cols ⟨0, by omega⟩) (cols ⟨1, by omega⟩) (cols ⟨2, by omega⟩) := by
  let a00 := A (rows ⟨0, by omega⟩) (cols ⟨0, by omega⟩)
  let a01 := A (rows ⟨0, by omega⟩) (cols ⟨1, by omega⟩)
  let a02 := A (rows ⟨0, by omega⟩) (cols ⟨2, by omega⟩)
  let a10 := A (rows ⟨1, by omega⟩) (cols ⟨0, by omega⟩)
  let a11 := A (rows ⟨1, by omega⟩) (cols ⟨1, by omega⟩)
  let a12 := A (rows ⟨1, by omega⟩) (cols ⟨2, by omega⟩)
  let a20 := A (rows ⟨2, by omega⟩) (cols ⟨0, by omega⟩)
  let a21 := A (rows ⟨2, by omega⟩) (cols ⟨1, by omega⟩)
  let a22 := A (rows ⟨2, by omega⟩) (cols ⟨2, by omega⟩)
  change (((0 +
      1 * a00 * ((0 + 1 * a11 * (0 + 1 * a22 * 1)) + (-1) * a12 * (0 + 1 * a21 * 1))) +
      (-1) * a01 * ((0 + 1 * a10 * (0 + 1 * a22 * 1)) + (-1) * a12 * (0 + 1 * a20 * 1))) +
      (-(-1)) * a02 * ((0 + 1 * a10 * (0 + 1 * a21 * 1)) + (-1) * a11 * (0 + 1 * a20 * 1))) =
    (a00 * (a11 * a22 - a12 * a21) - a01 * (a10 * a22 - a12 * a20) + a02 * (a10 * a21 - a11 * a20))
  generalize a00 = x00, a01 = x01, a02 = x02, a10 = x10, a11 = x11, a12 = x12,
             a20 = x20, a21 = x21, a22 = x22
  int_ring

def mkTriple {m : Nat} (a b c : Fin m) : Fin 3 → Fin m :=
  fun i => match i.val with | 0 => a | 1 => b | _ => c

/-- Sort 3 pairwise distinct `Fin m` elements into a `StrictMonoFin` triple, tracking sign. -/
theorem sort3_exists {m : Nat} (a b c : Fin m)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ (f : Fin 3 → Fin m),
      StrictMonoFin f ∧
      (∀ i : Fin 3, f i = a ∨ f i = b ∨ f i = c) ∧
      ((f ⟨0, by omega⟩ = a ∧ f ⟨1, by omega⟩ = b ∧ f ⟨2, by omega⟩ = c) ∨
       (f ⟨0, by omega⟩ = a ∧ f ⟨1, by omega⟩ = c ∧ f ⟨2, by omega⟩ = b) ∨
       (f ⟨0, by omega⟩ = c ∧ f ⟨1, by omega⟩ = a ∧ f ⟨2, by omega⟩ = b) ∨
       (f ⟨0, by omega⟩ = b ∧ f ⟨1, by omega⟩ = a ∧ f ⟨2, by omega⟩ = c) ∨
       (f ⟨0, by omega⟩ = b ∧ f ⟨1, by omega⟩ = c ∧ f ⟨2, by omega⟩ = a) ∨
       (f ⟨0, by omega⟩ = c ∧ f ⟨1, by omega⟩ = b ∧ f ⟨2, by omega⟩ = a)) := by
  have hab_v : a.val ≠ b.val := fun h => hab (Fin.ext h)
  have hac_v : a.val ≠ c.val := fun h => hac (Fin.ext h)
  have hbc_v : b.val ≠ c.val := fun h => hbc (Fin.ext h)
  have mkSM : ∀ (x y z : Fin m), x.val < y.val → y.val < z.val →
      StrictMonoFin (mkTriple x y z) := by
    intro x y z hxy hyz ⟨i, hi⟩ ⟨j, hj⟩ hij
    match i, j with
    | 0, 1 => exact hxy
    | 0, 2 => exact Nat.lt_trans hxy hyz
    | 1, 2 => exact hyz
    | 0, j + 3 => omega
    | 1, j + 3 => omega
    | 2, j + 3 => omega
    | i + 3, _ => omega
  have mkMem : ∀ (x y z : Fin m),
      (x = a ∨ x = b ∨ x = c) → (y = a ∨ y = b ∨ y = c) → (z = a ∨ z = b ∨ z = c) →
      ∀ i : Fin 3, mkTriple x y z i = a ∨ mkTriple x y z i = b ∨ mkTriple x y z i = c := by
    intro x y z hx hy hz ⟨i, hi⟩
    match i with
    | 0 => exact hx
    | 1 => exact hy
    | 2 => exact hz
    | i + 3 => omega
  by_cases h1 : a.val < b.val
  · by_cases h2 : b.val < c.val
    · refine ⟨mkTriple a b c, mkSM a b c h1 h2,
        mkMem a b c (Or.inl rfl) (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl)),
        Or.inl ⟨rfl, rfl, rfl⟩⟩
    · by_cases h3 : a.val < c.val
      · refine ⟨mkTriple a c b, mkSM a c b h3 (by omega),
          mkMem a c b (Or.inl rfl) (Or.inr (Or.inr rfl)) (Or.inr (Or.inl rfl)),
          Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)⟩
      · refine ⟨mkTriple c a b, mkSM c a b (by omega) h1,
          mkMem c a b (Or.inr (Or.inr rfl)) (Or.inl rfl) (Or.inr (Or.inl rfl)),
          Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))⟩
  · have hba : b.val < a.val := by omega
    by_cases h2 : a.val < c.val
    · refine ⟨mkTriple b a c, mkSM b a c hba h2,
        mkMem b a c (Or.inr (Or.inl rfl)) (Or.inl rfl) (Or.inr (Or.inr rfl)),
        Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)))⟩
    · by_cases h3 : b.val < c.val
      · refine ⟨mkTriple b c a, mkSM b c a h3 (by omega),
          mkMem b c a (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl)) (Or.inl rfl),
          Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))))⟩
      · refine ⟨mkTriple c b a, mkSM c b a (by omega) hba,
          mkMem c b a (Or.inr (Or.inr rfl)) (Or.inr (Or.inl rfl)) (Or.inl rfl),
          Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))))⟩

theorem det3_perm_rows {m n : Nat} (A : Fin m → Fin n → Int)
    (a b c : Fin m) (u v w : Fin n) (f : Fin 3 → Fin m)
    (hperm : (f ⟨0, by omega⟩ = a ∧ f ⟨1, by omega⟩ = b ∧ f ⟨2, by omega⟩ = c) ∨
             (f ⟨0, by omega⟩ = a ∧ f ⟨1, by omega⟩ = c ∧ f ⟨2, by omega⟩ = b) ∨
             (f ⟨0, by omega⟩ = c ∧ f ⟨1, by omega⟩ = a ∧ f ⟨2, by omega⟩ = b) ∨
             (f ⟨0, by omega⟩ = b ∧ f ⟨1, by omega⟩ = a ∧ f ⟨2, by omega⟩ = c) ∨
             (f ⟨0, by omega⟩ = b ∧ f ⟨1, by omega⟩ = c ∧ f ⟨2, by omega⟩ = a) ∨
             (f ⟨0, by omega⟩ = c ∧ f ⟨1, by omega⟩ = b ∧ f ⟨2, by omega⟩ = a)) :
    det3 A a b c u v w = det3 A (f ⟨0, by omega⟩) (f ⟨1, by omega⟩) (f ⟨2, by omega⟩) u v w ∨
    det3 A a b c u v w = - det3 A (f ⟨0, by omega⟩) (f ⟨1, by omega⟩) (f ⟨2, by omega⟩) u v w := by
  rcases hperm with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ |
                    ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ <;>
  rw [h0, h1, h2]
  · exact Or.inl rfl
  · right; unfold det3; int_ring
  · left; unfold det3; int_ring
  · right; unfold det3; int_ring
  · left; unfold det3; int_ring
  · right; unfold det3; int_ring

theorem det3_perm_cols {m n : Nat} (A : Fin m → Fin n → Int)
    (r0 r1 r2 : Fin m) (a b c : Fin n) (g : Fin 3 → Fin n)
    (hperm : (g ⟨0, by omega⟩ = a ∧ g ⟨1, by omega⟩ = b ∧ g ⟨2, by omega⟩ = c) ∨
             (g ⟨0, by omega⟩ = a ∧ g ⟨1, by omega⟩ = c ∧ g ⟨2, by omega⟩ = b) ∨
             (g ⟨0, by omega⟩ = c ∧ g ⟨1, by omega⟩ = a ∧ g ⟨2, by omega⟩ = b) ∨
             (g ⟨0, by omega⟩ = b ∧ g ⟨1, by omega⟩ = a ∧ g ⟨2, by omega⟩ = c) ∨
             (g ⟨0, by omega⟩ = b ∧ g ⟨1, by omega⟩ = c ∧ g ⟨2, by omega⟩ = a) ∨
             (g ⟨0, by omega⟩ = c ∧ g ⟨1, by omega⟩ = b ∧ g ⟨2, by omega⟩ = a)) :
    det3 A r0 r1 r2 a b c = det3 A r0 r1 r2 (g ⟨0, by omega⟩) (g ⟨1, by omega⟩) (g ⟨2, by omega⟩) ∨
    det3 A r0 r1 r2 a b c = - det3 A r0 r1 r2 (g ⟨0, by omega⟩) (g ⟨1, by omega⟩) (g ⟨2, by omega⟩) := by
  rcases hperm with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ |
                    ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ <;>
  rw [h0, h1, h2]
  · exact Or.inl rfl
  · right; unfold det3; int_ring
  · left; unfold det3; int_ring
  · right; unfold det3; int_ring
  · left; unfold det3; int_ring
  · right; unfold det3; int_ring

/-- Modulo-2 Cramer-Plücker projection lemma: if columns `c0, c1` have an odd `2 × 2` minor
    on rows `(r0, r1)`, and all `3 × 3` minors extending `(r0, r1; c0, c1)` to `(s0/s1; ca/cb)`
    are even, then any evenness of `det2(r0, r1; ca, cb)` forces `det2(s0, s1; ca, cb)` to be even. -/
theorem cramer_plucker_mod2 {m n : Nat} (A : Fin m → Fin n → Int)
    (r0 r1 s0 s1 : Fin m) (c0 c1 ca cb : Fin n)
    (hd01 : det2 A r0 r1 c0 c1 % 2 ≠ 0)
    (he0 : det3 A r0 r1 s0 c0 c1 ca % 2 = 0)
    (he1 : det3 A r0 r1 s1 c0 c1 ca % 2 = 0)
    (hf0 : det3 A r0 r1 s0 c0 c1 cb % 2 = 0)
    (hf1 : det3 A r0 r1 s1 c0 c1 cb % 2 = 0)
    (hcab : det2 A r0 r1 ca cb % 2 = 0) :
    det2 A s0 s1 ca cb % 2 = 0 := by
  let d01 := det2 A r0 r1 c0 c1
  let E0 := det3 A r0 r1 s0 c0 c1 ca
  let E1 := det3 A r0 r1 s1 c0 c1 ca
  let F0 := det3 A r0 r1 s0 c0 c1 cb
  let F1 := det3 A r0 r1 s1 c0 c1 cb
  let Pa := det2 A r0 r1 c0 ca * A s0 c1 - det2 A r0 r1 c1 ca * A s0 c0
  let Qa := det2 A r0 r1 c0 ca * A s1 c1 - det2 A r0 r1 c1 ca * A s1 c0
  let Pb := det2 A r0 r1 c0 cb * A s0 c1 - det2 A r0 r1 c1 cb * A s0 c0
  let Qb := det2 A r0 r1 c0 cb * A s1 c1 - det2 A r0 r1 c1 cb * A s1 c0
  have hE0 : d01 * A s0 ca = E0 + Pa := by dsimp [d01, E0, Pa, det3, det2]; int_ring
  have hE1 : d01 * A s1 ca = E1 + Qa := by dsimp [d01, E1, Qa, det3, det2]; int_ring
  have hF0 : d01 * A s0 cb = F0 + Pb := by dsimp [d01, F0, Pb, det3, det2]; int_ring
  have hF1 : d01 * A s1 cb = F1 + Qb := by dsimp [d01, F1, Qb, det3, det2]; int_ring
  have hPluck : Pa * Qb - Pb * Qa = d01 * det2 A s0 s1 c0 c1 * det2 A r0 r1 ca cb := by
    dsimp [Pa, Qa, Pb, Qb, d01, det2]; int_ring
  have hMain : (d01 * d01) * det2 A s0 s1 ca cb =
      E0 * (F1 + Qb) + Pa * F1 - F0 * (E1 + Qa) - Pb * E1 +
      d01 * det2 A s0 s1 c0 c1 * det2 A r0 r1 ca cb := by
    have hL : (d01 * d01) * det2 A s0 s1 ca cb =
        (d01 * A s0 ca) * (d01 * A s1 cb) - (d01 * A s0 cb) * (d01 * A s1 ca) := by
      dsimp [det2]; int_ring
    rw [hL, hE0, hE1, hF0, hF1]
    have hAlg : (E0 + Pa) * (F1 + Qb) - (F0 + Pb) * (E1 + Qa) =
        E0 * (F1 + Qb) + Pa * F1 - F0 * (E1 + Qa) - Pb * E1 + (Pa * Qb - Pb * Qa) := by
      int_ring
    rw [hAlg, hPluck]
  obtain ⟨q, hd_odd⟩ : ∃ q : Int, d01 = 2 * q + 1 := ⟨d01 / 2, by omega⟩
  obtain ⟨kE0, hE0_ev⟩ : ∃ k : Int, E0 = 2 * k := ⟨E0 / 2, by omega⟩
  obtain ⟨kE1, hE1_ev⟩ : ∃ k : Int, E1 = 2 * k := ⟨E1 / 2, by omega⟩
  obtain ⟨kF0, hF0_ev⟩ : ∃ k : Int, F0 = 2 * k := ⟨F0 / 2, by omega⟩
  obtain ⟨kF1, hF1_ev⟩ : ∃ k : Int, F1 = 2 * k := ⟨F1 / 2, by omega⟩
  let Dcab := det2 A r0 r1 ca cb
  obtain ⟨kD, hDcab_ev⟩ : ∃ k : Int, Dcab = 2 * k := ⟨Dcab / 2, by omega⟩
  change (d01 * d01) * det2 A s0 s1 ca cb =
      E0 * (F1 + Qb) + Pa * F1 - F0 * (E1 + Qa) - Pb * E1 +
      d01 * det2 A s0 s1 c0 c1 * Dcab at hMain
  have two_eq : ∀ z : Int, 2 * z = z + z := fun _ => by omega
  let K := (q * q + q * q + q + q) * det2 A s0 s1 ca cb
  have hd_sq : (d01 * d01) * det2 A s0 s1 ca cb =
      K + K + det2 A s0 s1 ca cb := by
    dsimp only [K]; rw [hd_odd]; simp only [two_eq]; int_ring
  let R := kE0 * (F1 + Qb) + Pa * kF1 - kF0 * (E1 + Qa) -
           Pb * kE1 + d01 * det2 A s0 s1 c0 c1 * kD
  have hRHS_ev : E0 * (F1 + Qb) + Pa * F1 - F0 * (E1 + Qa) - Pb * E1 +
      d01 * det2 A s0 s1 c0 c1 * Dcab = R + R := by
    dsimp only [R]; rw [hE0_ev, hE1_ev, hF0_ev, hF1_ev, hDcab_ev]; simp only [two_eq]; int_ring
  rw [hd_sq, hRHS_ev] at hMain
  omega

/-- Modulo-2 `2 × 2` determinant on `Bool × Bool` vectors in `𝔽₂²`. -/
def det2Bool (u v : Bool × Bool) : Bool :=
  xor (u.1 && v.2) (v.1 && u.2)

theorem det2_mod2_eq_det2Bool (x0 y0 x1 y1 : Int) :
    ((x0 * y1 - x1 * y0) % 2 != 0) =
      det2Bool (x0 % 2 != 0, y0 % 2 != 0) (x1 % 2 != 0, y1 % 2 != 0) := by
  have hx0 : x0 = 2 * (x0 / 2) + (x0 % 2) := by omega
  have hy0 : y0 = 2 * (y0 / 2) + (y0 % 2) := by omega
  have hx1 : x1 = 2 * (x1 / 2) + (x1 % 2) := by omega
  have hy1 : y1 = 2 * (y1 / 2) + (y1 % 2) := by omega
  have hrem : (x0 * y1 - x1 * y0) % 2 = ((x0 % 2) * (y1 % 2) - (x1 % 2) * (y0 % 2)) % 2 := by
    have hdiff : x0 * y1 - x1 * y0 =
        2 * (2 * (x0 / 2) * (y1 / 2) + (x0 / 2) * (y1 % 2) + (x0 % 2) * (y1 / 2) -
             2 * (x1 / 2) * (y0 / 2) - (x1 / 2) * (y0 % 2) - (x1 % 2) * (y0 / 2)) +
        ((x0 % 2) * (y1 % 2) - (x1 % 2) * (y0 % 2)) := by
      conv => lhs; rw [hx0, hy0, hx1, hy1]
      int_ring
    omega
  rw [hrem]
  have bx0 : x0 % 2 = 0 ∨ x0 % 2 = 1 := by omega
  have by0 : y0 % 2 = 0 ∨ y0 % 2 = 1 := by omega
  have bx1 : x1 % 2 = 0 ∨ x1 % 2 = 1 := by omega
  have by1 : y1 % 2 = 0 ∨ y1 % 2 = 1 := by omega
  rcases bx0 with h0 | h0 <;> rcases by0 with k0 | k0 <;>
  rcases bx1 with h1 | h1 <;> rcases by1 with k1 | k1 <;>
  rw [h0, k0, h1, k1] <;> rfl

/-- Pigeonhole over `𝔽₂² \ {(0,0)}`: no 4 vectors in `𝔽₂²` have all 6 pairwise determinants nonzero. -/
theorem no_four_vectors_f2_2 :
    ¬ ∃ (v : Fin 4 → Bool × Bool),
      det2Bool (v ⟨0, by omega⟩) (v ⟨1, by omega⟩) = true ∧
      det2Bool (v ⟨0, by omega⟩) (v ⟨2, by omega⟩) = true ∧
      det2Bool (v ⟨0, by omega⟩) (v ⟨3, by omega⟩) = true ∧
      det2Bool (v ⟨1, by omega⟩) (v ⟨2, by omega⟩) = true ∧
      det2Bool (v ⟨1, by omega⟩) (v ⟨3, by omega⟩) = true ∧
      det2Bool (v ⟨2, by omega⟩) (v ⟨3, by omega⟩) = true := by
  have hchk :
      allSubsets 8 (fun bits =>
        let v : Fin 4 → Bool × Bool := fun i =>
          (bits ⟨2 * i.val, by omega⟩, bits ⟨2 * i.val + 1, by omega⟩)
        !(det2Bool (v ⟨0, by omega⟩) (v ⟨1, by omega⟩) &&
          det2Bool (v ⟨0, by omega⟩) (v ⟨2, by omega⟩) &&
          det2Bool (v ⟨0, by omega⟩) (v ⟨3, by omega⟩) &&
          det2Bool (v ⟨1, by omega⟩) (v ⟨2, by omega⟩) &&
          det2Bool (v ⟨1, by omega⟩) (v ⟨3, by omega⟩) &&
          det2Bool (v ⟨2, by omega⟩) (v ⟨3, by omega⟩))) = true := by decide
  rintro ⟨v, h01, h02, h03, h12, h13, h23⟩
  let bits : Fin 8 → Bool := fun k =>
    match k.val with
    | 0 => (v ⟨0, by omega⟩).1 | 1 => (v ⟨0, by omega⟩).2
    | 2 => (v ⟨1, by omega⟩).1 | 3 => (v ⟨1, by omega⟩).2
    | 4 => (v ⟨2, by omega⟩).1 | 5 => (v ⟨2, by omega⟩).2
    | 6 => (v ⟨3, by omega⟩).1 | _ => (v ⟨3, by omega⟩).2
  have hb := allSubsets_eq_true.mp hchk bits
  simp only [bits, h01, h02, h03, h12, h13, h23] at hb
  cases hb

/-- `M₄ ≅ L(U_{2,4})` is NOT binary (`𝔽₂`-representable). -/
theorem not_isBinary_M4 : ¬ IsBinary M4 := by
  rintro ⟨m, n, idx, A, hRep⟩
  -- Extract the 4 distinct column indices corresponding to the 4 atoms `1, 2, 3, 4` of `M₄`.
  have hcov1 : Covers M4.le M4.bot ⟨1, by decide⟩ := coversBool_eq_true.mp (by decide)
  have hcov2 : Covers M4.le M4.bot ⟨2, by decide⟩ := coversBool_eq_true.mp (by decide)
  have hcov3 : Covers M4.le M4.bot ⟨3, by decide⟩ := coversBool_eq_true.mp (by decide)
  have hcov4 : Covers M4.le M4.bot ⟨4, by decide⟩ := coversBool_eq_true.mp (by decide)
  rcases idx.surj ⟨1, by decide⟩ hcov1 with ⟨c0, hc0⟩
  rcases idx.surj ⟨2, by decide⟩ hcov2 with ⟨c1, hc1⟩
  rcases idx.surj ⟨3, by decide⟩ hcov3 with ⟨c2, hc2⟩
  rcases idx.surj ⟨4, by decide⟩ hcov4 with ⟨c3, hc3⟩
  have hne01 : c0 ≠ c1 := fun h => by rw [h, hc1] at hc0; cases hc0
  have hne02 : c0 ≠ c2 := fun h => by rw [h, hc2] at hc0; cases hc0
  have hne03 : c0 ≠ c3 := fun h => by rw [h, hc3] at hc0; cases hc0
  have hne12 : c1 ≠ c2 := fun h => by rw [h, hc2] at hc1; cases hc1
  have hne13 : c1 ≠ c3 := fun h => by rw [h, hc3] at hc1; cases hc1
  have hne23 : c2 ≠ c3 := fun h => by rw [h, hc3] at hc2; cases hc2
  -- Any two distinct atoms of `M₄` join to `⊤` (rank 2).
  have pair_rk2 : ∀ (u v : Fin n),
      Covers M4.le M4.bot (idx.atomOf u) →
      Covers M4.le M4.bot (idx.atomOf v) → u ≠ v →
      M4.rk (joinSubset M4 idx.atomOf (fun t => (t == u) || (t == v))) = 2 := by
    intro u v hu hv huv
    let S : Fin n → Bool := fun t => (t == u) || (t == v)
    let x := joinSubset M4 idx.atomOf S
    have hux : M4.le (idx.atomOf u) x = true :=
      le_joinSubset M4 idx.atomOf S u (by simp [S])
    have hvx : M4.le (idx.atomOf v) x = true :=
      le_joinSubset M4 idx.atomOf S v (by simp [S])
    have hauv : idx.atomOf u ≠ idx.atomOf v := fun h => huv (idx.inj u v h)
    have hM4_top : allFin M4.size (fun a => allFin M4.size (fun b => allFin M4.size (fun z =>
        !(coversBool M4.le M4.bot a && coversBool M4.le M4.bot b && (a != b) &&
          M4.le a z && M4.le b z) || (M4.rk z == 2)))) = true := by decide
    have hchk := allFin_eq_true.mp (allFin_eq_true.mp
      (allFin_eq_true.mp hM4_top (idx.atomOf u)) (idx.atomOf v)) x
    rw [coversBool_eq_true.mpr hu, coversBool_eq_true.mpr hv,
        bne_iff_ne.mpr hauv, hux, hvx] at hchk
    exact beq_iff_eq.mp hchk
  -- Hence every pair `(u, v)` of distinct atoms has an odd `2 × 2` minor.
  have pair_odd_minor : ∀ (u v : Fin n),
      Covers M4.le M4.bot (idx.atomOf u) →
      Covers M4.le M4.bot (idx.atomOf v) → u ≠ v →
      ∃ s0 s1 : Fin m, det2 A s0 s1 u v % 2 ≠ 0 := by
    intro u v hu hv huv
    let S : Fin n → Bool := fun t => (t == u) || (t == v)
    have hrk := pair_rk2 u v hu hv huv
    have hmin := (hRep S).1
    rw [hrk] at hmin
    rcases hmin with ⟨rows, cols, _, hcm, hcolsS, hdet⟩
    rw [det_submatrix_2] at hdet
    let d0 := cols ⟨0, by omega⟩
    let d1 := cols ⟨1, by omega⟩
    have hd01_lt : d0.val < d1.val := hcm ⟨0, by omega⟩ ⟨1, by omega⟩ Nat.zero_lt_one
    have hd0S : d0 = u ∨ d0 = v := by
      have := hcolsS ⟨0, by omega⟩
      simp only [S, Bool.or_eq_true, beq_iff_eq] at this; exact this
    have hd1S : d1 = u ∨ d1 = v := by
      have := hcolsS ⟨1, by omega⟩
      simp only [S, Bool.or_eq_true, beq_iff_eq] at this; exact this
    refine ⟨rows ⟨0, by omega⟩, rows ⟨1, by omega⟩, ?_⟩
    change det2 A (rows ⟨0, by omega⟩) (rows ⟨1, by omega⟩) d0 d1 % 2 ≠ 0 at hdet
    rcases hd0S with hd0 | hd0 <;> rcases hd1S with hd1 | hd1
    · rw [hd0, hd1] at hd01_lt; exact absurd hd01_lt (Nat.lt_irrefl _)
    · rw [hd0, hd1] at hdet; exact hdet
    · rw [hd0, hd1] at hdet
      have hswap : det2 A (rows ⟨0, by omega⟩) (rows ⟨1, by omega⟩) v u =
          - det2 A (rows ⟨0, by omega⟩) (rows ⟨1, by omega⟩) u v := by
        unfold det2; int_ring
      rw [hswap] at hdet; omega
    · rw [hd0, hd1] at hd01_lt; exact absurd hd01_lt (Nat.lt_irrefl _)
  -- Obtain the reference row pair `(r0, r1)` on which `det2(c0, c1)` is odd.
  have hu0 : Covers M4.le M4.bot (idx.atomOf c0) := by rw [hc0]; exact hcov1
  have hu1 : Covers M4.le M4.bot (idx.atomOf c1) := by rw [hc1]; exact hcov2
  have hu2 : Covers M4.le M4.bot (idx.atomOf c2) := by rw [hc2]; exact hcov3
  have hu3 : Covers M4.le M4.bot (idx.atomOf c3) := by rw [hc3]; exact hcov4
  rcases pair_odd_minor c0 c1 hu0 hu1 hne01 with ⟨r0, r1, hr01_odd⟩
  have hr01_ne : r0 ≠ r1 := by
    intro heq; rw [heq] at hr01_odd
    have : det2 A r1 r1 c0 c1 = 0 := by unfold det2; int_ring
    rw [this] at hr01_odd; exact hr01_odd rfl
  -- Every `3 × 3` minor `(r0, r1, s; c0, c1, ck)` for `ck ∈ {c0, c1, c2, c3}` is even (`% 2 = 0`).
  have triple_even : ∀ (s : Fin m) (ck : Fin n),
      (ck = c0 ∨ ck = c1 ∨ ck = c2 ∨ ck = c3) →
      det3 A r0 r1 s c0 c1 ck % 2 = 0 := by
    intro s ck hck
    by_cases hs0 : s = r0
    · rw [hs0]; have : det3 A r0 r1 r0 c0 c1 ck = 0 := by unfold det3; int_ring
      rw [this]; rfl
    · by_cases hs1 : s = r1
      · rw [hs1]; have : det3 A r0 r1 r1 c0 c1 ck = 0 := by unfold det3; int_ring
        rw [this]; rfl
      · by_cases hck0 : ck = c0
        · rw [hck0]; have : det3 A r0 r1 s c0 c1 c0 = 0 := by unfold det3; int_ring
          rw [this]; rfl
        · by_cases hck1 : ck = c1
          · rw [hck1]; have : det3 A r0 r1 s c0 c1 c1 = 0 := by unfold det3; int_ring
            rw [this]; rfl
          · -- Now `r0, r1, s` are pairwise distinct and `c0, c1, ck` are pairwise distinct.
            rcases sort3_exists r0 r1 s hr01_ne (Ne.symm hs0) (Ne.symm hs1) with
              ⟨f, hf_sm, _, hf_perm⟩
            rcases sort3_exists c0 c1 ck hne01 (Ne.symm hck0) (Ne.symm hck1) with
              ⟨g, hg_sm, hg_mem, hg_perm⟩
            let S3 : Fin n → Bool := fun t => (t == c0) || (t == c1) || (t == ck)
            have hrk_le : M4.rk (joinSubset M4 idx.atomOf S3) ≤ 2 := rk_le_rank M4 _
            have hno3 := (hRep S3).2 3 (by omega)
            have hgS3 : ∀ j : Fin 3, S3 (g j) = true := by
              intro j
              rcases hg_mem j with hj | hj | hj <;> simp [S3, hj]
            have hsub_ev : det (submatrix A f g) % 2 = 0 := by
              by_cases hmod : det (submatrix A f g) % 2 = 0
              · exact hmod
              · exfalso; exact hno3 ⟨f, g, hf_sm, hg_sm, hgS3, hmod⟩
            rw [det_submatrix_3] at hsub_ev
            have hr_sign := det3_perm_rows A r0 r1 s c0 c1 ck f hf_perm
            have hc_sign := det3_perm_cols A (f ⟨0, by omega⟩) (f ⟨1, by omega⟩) (f ⟨2, by omega⟩)
              c0 c1 ck g hg_perm
            rcases hr_sign with hr | hr <;> rcases hc_sign with hc | hc <;> omega
  -- By `cramer_plucker_mod2`, `det2 A r0 r1 ca cb % 2 ≠ 0` for all 6 pairs among `c0, c1, c2, c3`.
  have pair_r01_odd : ∀ (ca cb : Fin n),
      (ca = c0 ∨ ca = c1 ∨ ca = c2 ∨ ca = c3) →
      (cb = c0 ∨ cb = c1 ∨ cb = c2 ∨ cb = c3) →
      Covers M4.le M4.bot (idx.atomOf ca) →
      Covers M4.le M4.bot (idx.atomOf cb) → ca ≠ cb →
      det2 A r0 r1 ca cb % 2 ≠ 0 := by
    intro ca cb hca hcb huca hucb hcab h_ev
    rcases pair_odd_minor ca cb huca hucb hcab with ⟨s0, s1, hs01_odd⟩
    have hs01_ev := cramer_plucker_mod2 A r0 r1 s0 s1 c0 c1 ca cb hr01_odd
      (triple_even s0 ca hca) (triple_even s1 ca hca)
      (triple_even s0 cb hcb) (triple_even s1 cb hcb) h_ev
    exact hs01_odd hs01_ev
  have m0 : c0 = c0 ∨ c0 = c1 ∨ c0 = c2 ∨ c0 = c3 := Or.inl rfl
  have m1 : c1 = c0 ∨ c1 = c1 ∨ c1 = c2 ∨ c1 = c3 := Or.inr (Or.inl rfl)
  have m2 : c2 = c0 ∨ c2 = c1 ∨ c2 = c2 ∨ c2 = c3 := Or.inr (Or.inr (Or.inl rfl))
  have m3 : c3 = c0 ∨ c3 = c1 ∨ c3 = c2 ∨ c3 = c3 := Or.inr (Or.inr (Or.inr rfl))
  have d01 := pair_r01_odd c0 c1 m0 m1 hu0 hu1 hne01
  have d02 := pair_r01_odd c0 c2 m0 m2 hu0 hu2 hne02
  have d03 := pair_r01_odd c0 c3 m0 m3 hu0 hu3 hne03
  have d12 := pair_r01_odd c1 c2 m1 m2 hu1 hu2 hne12
  have d13 := pair_r01_odd c1 c3 m1 m3 hu1 hu3 hne13
  have d23 := pair_r01_odd c2 c3 m2 m3 hu2 hu3 hne23
  -- Map the 4 columns `(A r0 ci, A r1 ci)` into `𝔽₂²` and contradict `no_four_vectors_f2_2`.
  let vec : Fin 4 → Bool × Bool := fun i =>
    let ci := match i.val with | 0 => c0 | 1 => c1 | 2 => c2 | _ => c3
    (A r0 ci % 2 != 0, A r1 ci % 2 != 0)
  have toBool : ∀ (ca cb : Fin n), det2 A r0 r1 ca cb % 2 ≠ 0 →
      det2Bool (A r0 ca % 2 != 0, A r1 ca % 2 != 0) (A r0 cb % 2 != 0, A r1 cb % 2 != 0) = true := by
    intro ca cb hd
    rw [← det2_mod2_eq_det2Bool]
    exact bne_iff_ne.mpr hd
  exact no_four_vectors_f2_2
    ⟨vec, toBool c0 c1 d01, toBool c0 c2 d02, toBool c0 c3 d03,
          toBool c1 c2 d12, toBool c1 c3 d13, toBool c2 c3 d23⟩

/-- `M₄ ≅ L(U_{2,4})` is NOT unimodular (regular). -/
theorem not_isUnimodular_M4 : ¬ IsUnimodular M4 :=
  fun hU => not_isBinary_M4 (unimodular_implies_binary M4 hU)

/-! ## 9. Log-Concavity, Flats, and All Formalizations of Conjecture 00000008534 -/

/-- Log-concavity of `a = [a_0, ..., a_r]`: `a_{k-1} * a_{k+1} ≤ a_k^2` for all `1 ≤ k ≤ r - 1`. -/
def IsLogConcave (a : List Nat) : Prop :=
  ∀ (k : Nat) (hk1 : 1 ≤ k) (hk2 : k + 1 < a.length),
    a[k - 1] * a[k + 1] ≤ a[k] * a[k]

/-- Strict log-concavity: `a_{k-1} * a_{k+1} < a_k^2` for all `1 ≤ k ≤ r - 1`. -/
def IsStrictlyLogConcave (a : List Nat) : Prop :=
  ∀ (k : Nat) (hk1 : 1 ≤ k) (hk2 : k + 1 < a.length),
    a[k - 1] * a[k + 1] < a[k] * a[k]

/-- Non-vacuous strict log-concavity (additionally requiring rank `r ≥ 2`, i.e. `a.length ≥ 3`). -/
def IsStrictlyLogConcaveNonVacuous (a : List Nat) : Prop :=
  3 ≤ a.length ∧ IsStrictlyLogConcave a

/-- Standard log-concavity flat at interior rank `k`: `a_k^2 = a_{k-1} * a_{k+1}`. -/
def IsLCFlatAt (a : List Nat) (k : Nat) : Prop :=
  ∃ (_ : 1 ≤ k) (_ : k + 1 < a.length),
    a[k] * a[k] = a[k - 1] * a[k + 1]

/-- Alternative value-plateau flat at rank `k`: `a_k = a_{k+1}`. -/
def IsPlateauFlatAt (a : List Nat) (k : Nat) : Prop :=
  ∃ (_ : k + 1 < a.length),
    a[k] = a[k + 1]

/-- Absence of any adjacent value plateau. -/
def HasNoPlateau (a : List Nat) : Prop :=
  ∀ k : Nat, ¬ IsPlateauFlatAt a k

/-- `FirstFlatAt P a s` means `s` is the smallest index at which flat predicate `P` holds. -/
def FirstFlatAt (P : List Nat → Nat → Prop) (a : List Nat) (s : Nat) : Prop :=
  P a s ∧ ∀ j : Nat, j < s → ¬ P a j

/-- A candidate specification of "the doubly-flat element stratum" assigns to each
    geometric lattice `L` a predicate `S L : Nat → Prop` on rank strata (subsuming
    single-stratum functions `s : GeometricLattice → Nat` via `fun L k => k = s L`). -/
abbrev StratumSpec := GeometricLattice → Nat → Prop

/-- Explicit Whitney sequences of our concrete geometric lattices (verified by kernel reduction). -/
theorem whitneySecond_B1 : whitneySecond B1 = [1, 1] := rfl
theorem whitneyFirst_B1 : whitneyFirstUnsigned B1 = [1, 1] := rfl

theorem whitneySecond_B2 : whitneySecond B2 = [1, 2, 1] := rfl
theorem whitneyFirst_B2 : whitneyFirstUnsigned B2 = [1, 2, 1] := rfl

theorem whitneySecond_M3 : whitneySecond M3 = [1, 3, 1] := rfl
theorem whitneyFirst_M3 : whitneyFirstUnsigned M3 = [1, 3, 2] := rfl

theorem whitneySecond_M4 : whitneySecond M4 = [1, 4, 1] := rfl
theorem whitneyFirst_M4 : whitneyFirstUnsigned M4 = [1, 4, 3] := rfl

theorem whitneySecond_B3 : whitneySecond B3 = [1, 3, 3, 1] := rfl
theorem whitneyFirst_B3 : whitneyFirstUnsigned B3 = [1, 3, 3, 1] := rfl

theorem whitneySecond_LU34 : whitneySecond LU34 = [1, 4, 6, 1] := rfl
theorem whitneyFirst_LU34 : whitneyFirstUnsigned LU34 = [1, 4, 6, 3] := rfl

/-- Positive non-vacuity witnesses: `B₂`, `M₃`, and `L(U_{3,4})` are unimodular geometric lattices
    whose Whitney sequences (`W_k` and `|w_k|`) are non-vacuously strictly log-concave and plateau-free. -/
theorem positive_witnesses_unimodular :
    (IsUnimodular B2 ∧ IsStrictlyLogConcaveNonVacuous (whitneySecond B2) ∧
      IsStrictlyLogConcaveNonVacuous (whitneyFirstUnsigned B2)) ∧
    (IsUnimodular M3 ∧ IsStrictlyLogConcaveNonVacuous (whitneySecond M3) ∧
      IsStrictlyLogConcaveNonVacuous (whitneyFirstUnsigned M3)) ∧
    (IsUnimodular LU34 ∧ IsStrictlyLogConcaveNonVacuous (whitneySecond LU34) ∧
      IsStrictlyLogConcaveNonVacuous (whitneyFirstUnsigned LU34)) := by
  refine ⟨⟨isUnimodular_B2, ?_, ?_⟩, ⟨isUnimodular_M3, ?_, ?_⟩, ⟨isUnimodular_LU34, ?_, ?_⟩⟩
  · refine ⟨by decide, fun k hk1 hk2 => ?_⟩
    change k + 1 < 3 at hk2
    have hk : k = 1 := by omega
    subst hk; decide +revert
  · refine ⟨by decide, fun k hk1 hk2 => ?_⟩
    change k + 1 < 3 at hk2
    have hk : k = 1 := by omega
    subst hk; decide +revert
  · refine ⟨by decide, fun k hk1 hk2 => ?_⟩
    change k + 1 < 3 at hk2
    have hk : k = 1 := by omega
    subst hk; decide +revert
  · refine ⟨by decide, fun k hk1 hk2 => ?_⟩
    change k + 1 < 3 at hk2
    have hk : k = 1 := by omega
    subst hk; decide +revert
  · refine ⟨by decide, fun k hk1 hk2 => ?_⟩
    change k + 1 < 4 at hk2
    have hk : k = 1 ∨ k = 2 := by omega
    rcases hk with rfl | rfl <;> decide +revert
  · refine ⟨by decide, fun k hk1 hk2 => ?_⟩
    change k + 1 < 4 at hk2
    have hk : k = 1 ∨ k = 2 := by omega
    rcases hk with rfl | rfl <;> decide +revert

/-- Strict log-concavity and absence of ANY flat (both LC-equality and plateau) for `M₄ = L(U_{2,4})`. -/
theorem M4_strict_and_flat_free :
    IsStrictlyLogConcave (whitneySecond M4) ∧
    IsStrictlyLogConcave (whitneyFirstUnsigned M4) ∧
    (∀ k : Nat, ¬ IsLCFlatAt (whitneySecond M4) k) ∧
    (∀ k : Nat, ¬ IsLCFlatAt (whitneyFirstUnsigned M4) k) ∧
    HasNoPlateau (whitneySecond M4) ∧
    HasNoPlateau (whitneyFirstUnsigned M4) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk1 hk2
    change k + 1 < 3 at hk2
    have hk : k = 1 := by omega
    subst hk; decide +revert
  · intro k hk1 hk2
    change k + 1 < 3 at hk2
    have hk : k = 1 := by omega
    subst hk; decide +revert
  · rintro k ⟨hk1, hk2, heq⟩
    change k + 1 < 3 at hk2
    have hk : k = 1 := by omega
    subst hk; revert heq; decide +revert
  · rintro k ⟨hk1, hk2, heq⟩
    change k + 1 < 3 at hk2
    have hk : k = 1 := by omega
    subst hk; revert heq; decide +revert
  · rintro k ⟨hk2, heq⟩
    change k + 1 < 3 at hk2
    have hk : k = 0 ∨ k = 1 := by omega
    rcases hk with rfl | rfl <;> (revert heq; decide +revert)
  · rintro k ⟨hk2, heq⟩
    change k + 1 < 3 at hk2
    have hk : k = 0 ∨ k = 1 := by omega
    rcases hk with rfl | rfl <;> (revert heq; decide +revert)

/-! ### Main Disproof Theorems Across All Mathematical Conventions -/

/-- **Convention 1 (Primary — literal `SOURCE.md` statement: Whitney numbers of the second kind `W_k`,
    log-concavity flat `W_k^2 = W_{k-1} W_{k+1}`)**:
    For EVERY candidate specification `S : StratumSpec` of the "doubly-flat element stratum",
    Conjecture 00000008534 is FALSE, refuted by `M₄ ≅ L(U_{2,4})`. -/
def Conjecture00000008534_SecondKind_LCFlat (S : StratumSpec) : Prop :=
  ∀ L : GeometricLattice,
    let W := whitneySecond L
    IsLogConcave W ∧
    (IsUnimodular L → IsStrictlyLogConcave W) ∧
    (¬ IsUnimodular L → ∃ k : Nat, FirstFlatAt IsLCFlatAt W k ∧ S L k)

theorem disproof_conjecture_secondKind_lcFlat :
    ∀ S : StratumSpec, ¬ Conjecture00000008534_SecondKind_LCFlat S := by
  intro S hConj
  rcases (hConj M4).2.2 not_isUnimodular_M4 with ⟨k, ⟨hflat, _⟩, _⟩
  exact M4_strict_and_flat_free.2.2.1 k hflat

/-- **Convention 2 (Unsigned Whitney numbers of the first kind `|w_k|`,
    log-concavity flat `|w_k|^2 = |w_{k-1}| |w_{k+1}|`)**:
    Refuted for EVERY `S : StratumSpec` by `M₄ ≅ L(U_{2,4})`. -/
def Conjecture00000008534_FirstKind_LCFlat (S : StratumSpec) : Prop :=
  ∀ L : GeometricLattice,
    let w := whitneyFirstUnsigned L
    IsLogConcave w ∧
    (IsUnimodular L → IsStrictlyLogConcave w) ∧
    (¬ IsUnimodular L → ∃ k : Nat, FirstFlatAt IsLCFlatAt w k ∧ S L k)

theorem disproof_conjecture_firstKind_lcFlat :
    ∀ S : StratumSpec, ¬ Conjecture00000008534_FirstKind_LCFlat S := by
  intro S hConj
  rcases (hConj M4).2.2 not_isUnimodular_M4 with ⟨k, ⟨hflat, _⟩, _⟩
  exact M4_strict_and_flat_free.2.2.2.1 k hflat

/-- **Convention 3 (Adjacent value-plateau flat `a_k = a_{k+1}`, for both `W_k` and `|w_k|`)**:
    Under the value-plateau reading, BOTH branches of the dichotomy fail simultaneously:
    (a) `M₄ = L(U_{2,4})` is non-unimodular yet has NO plateau in `W_k` or `|w_k|`;
    (b) `B₃ = L(U_{3,3})` (rank 3) and `B₁` (rank 1) ARE unimodular yet DO have a plateau (`3 = 3` and `1 = 1`),
        so even the unimodular branch ("strict when unimodular") fails! -/
theorem disproof_conjecture_plateau_both_branches :
    -- Branch (a): non-unimodular M4 has no plateau in either W_k or |w_k|
    (¬ IsUnimodular M4 ∧ HasNoPlateau (whitneySecond M4) ∧ HasNoPlateau (whitneyFirstUnsigned M4)) ∧
    -- Branch (b): unimodular B3 (rank 3) has a plateau at k = 1 in both W_k and |w_k|
    (IsUnimodular B3 ∧ B3.rank = 3 ∧
      IsPlateauFlatAt (whitneySecond B3) 1 ∧ IsPlateauFlatAt (whitneyFirstUnsigned B3) 1) := by
  refine ⟨⟨not_isUnimodular_M4, M4_strict_and_flat_free.2.2.2.2.1, M4_strict_and_flat_free.2.2.2.2.2⟩,
          ⟨isUnimodular_B3, rfl, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩⟩

/-- **Convention 4 (Boundary & alternative property checks)**:
    (a) Under non-vacuous strict log-concavity (`r ≥ 2`), unimodular `B₁` (`W = [1, 1]`) already fails
        the unimodular branch (`IsUnimodular B1 ∧ ¬ IsStrictlyLogConcaveNonVacuous (whitneySecond B1)`).
    (b) Even if "unimodular" were conflated with lattice modularity (`IsModular`),
        `L(U_{3,4})` is non-modular (`¬ IsModular LU34`) yet has zero LC-flats and zero plateaus
        in both `W = [1, 4, 6, 1]` and `|w| = [1, 4, 6, 3]`. -/
theorem boundary_and_modularity_checks :
    (IsUnimodular B1 ∧ ¬ IsStrictlyLogConcaveNonVacuous (whitneySecond B1)) ∧
    (¬ IsModular LU34 ∧
      (∀ k : Nat, ¬ IsLCFlatAt (whitneySecond LU34) k) ∧
      (∀ k : Nat, ¬ IsLCFlatAt (whitneyFirstUnsigned LU34) k) ∧
      HasNoPlateau (whitneySecond LU34) ∧
      HasNoPlateau (whitneyFirstUnsigned LU34)) := by
  refine ⟨⟨isUnimodular_B1, ?_⟩, ⟨not_isModular_LU34, ?_, ?_, ?_, ?_⟩⟩
  · rintro ⟨hlen, _⟩
    revert hlen; decide
  · rintro k ⟨hk1, hk2, heq⟩
    change k + 1 < 4 at hk2
    have hk : k = 1 ∨ k = 2 := by omega
    rcases hk with rfl | rfl <;> (revert heq; decide +revert)
  · rintro k ⟨hk1, hk2, heq⟩
    change k + 1 < 4 at hk2
    have hk : k = 1 ∨ k = 2 := by omega
    rcases hk with rfl | rfl <;> (revert heq; decide +revert)
  · rintro k ⟨hk2, heq⟩
    change k + 1 < 4 at hk2
    have hk : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk with rfl | rfl | rfl <;> (revert heq; decide +revert)
  · rintro k ⟨hk2, heq⟩
    change k + 1 < 4 at hk2
    have hk : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk with rfl | rfl | rfl <;> (revert heq; decide +revert)

end WhitneyLogConcavity

/-! ## 10. Axiom Verification (`propext`, `Classical.choice`, `Quot.sound` only) -/

#print axioms WhitneyLogConcavity.rk_unique
#print axioms WhitneyLogConcavity.muBot_interval_sum_zero
#print axioms WhitneyLogConcavity.unimodular_implies_binary
#print axioms WhitneyLogConcavity.not_isBinary_M4
#print axioms WhitneyLogConcavity.not_isUnimodular_M4
#print axioms WhitneyLogConcavity.positive_witnesses_unimodular
#print axioms WhitneyLogConcavity.disproof_conjecture_secondKind_lcFlat
#print axioms WhitneyLogConcavity.disproof_conjecture_firstKind_lcFlat
#print axioms WhitneyLogConcavity.disproof_conjecture_plateau_both_branches
#print axioms WhitneyLogConcavity.boundary_and_modularity_checks
