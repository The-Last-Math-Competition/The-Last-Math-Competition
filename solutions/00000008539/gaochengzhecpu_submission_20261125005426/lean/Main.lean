/-
  Conjecture 00000008539 — The Last Math Competition
  Self-contained formalization in Core Lean 4 (v4.19.0, zero external dependencies).

  Statement (SOURCE.md):
    Definition: The Mobius function is the inverse of zeta in the incidence algebra.
    Conjecture: The absolute values of the Mobius function of a geometric lattice form a
    log-concave sequence with first term 1; and equality holds globally only for Boolean
    lattices. (Mobius log-concavity)

  Summary of Formalized Results:
  1. Incidence Algebra & Mobius Function (Section 2):
     Full formalization of finite posets `FinPoset`, their incidence algebras `IncidenceAlg`
     over `Int` (`delta`, `zeta`, associative convolution `mul`), explicit construction of
     `mobius`, proof that `mobius` is a two-sided inverse of `zeta` (`mobius_is_mobius`),
     and proof of uniqueness (`mobius_unique`).
  2. Geometric & Boolean Lattices (Section 3):
     Faithful textbook definitions of `FinLattice`, `GeometricLattice` (atomistic, graded by
     unique rank `rk`, submodular), `Covers`, `IsAtom`, `IsMaximalChain`, and
     `IsBooleanLattice` (distributive and complemented).
  3. Weisner's Theorem, Rota's Sign Theorem & Boolean Characterization (Section 4):
     - `weisner_thm`: Weisner's identity for arbitrary finite lattices.
     - `rota_sign_thm`: Rota's strict sign theorem `(-1)^rk(y) * mu(bot, y) ≥ 1` for all
       elements of any finite geometric lattice.
     - `geom_rk_le_one_isBoolean`: Every geometric lattice of rank `≤ 1` is Boolean.
     - `isBoolean_iff_natAbs_mu_top_eq_one`: A finite geometric lattice `L` is Boolean
       if and only if `|mu(bot, top)| = 1`.
  4. All Natural Sequence Conventions & Complete Disproofs / Classifications (Sections 5–8):
     - Convention I (Unsigned Whitney numbers of the first kind `w_k^+(L) = ∑_{rk(x)=k} |mu(0,x)|`):
       * First term `w_0^+(L) = 1` always holds (`whitney1Abs_zero`).
       * Complete classification of global equality (`whitney1Abs_global_eq_iff_rank_le_one`):
         For EVERY finite geometric lattice `L`, global equality `w_k^2 = w_{k-1} w_{k+1}`
         (`1 ≤ k ≤ rank - 1`) holds IF AND ONLY IF `L.rank ≤ 1` (vacuously, over an empty
         interior index set). No geometric lattice of rank `≥ 2` — Boolean or not — ever
         attains global equality (`whitney1Abs_no_global_eq_of_rank_ge_two`).
       * Disproof of the equality-case characterization (`disproof_convention_I_whitney_iff`):
         On `B_2` (rank-2 Boolean geometric lattice), `w^+(B_2) = (1, 2, 1)` satisfies
         `2^2 = 4 ≠ 1 = 1 * 1`, refuting `GlobalLogConcaveEq ↔ IsBooleanLattice`.
       * Note on the degenerate one-way material implication (`whitney1Abs_global_eq_imp_boolean`):
         `GlobalLogConcaveEq → IsBooleanLattice` holds solely by vacuity for `rank ≥ 2` and
         degeneracy (`rank ≤ 1 → Boolean`).
     - Convention II (Elementwise `|mu(0, x_k)|` along maximal chains / rank-selectors, and
       rank-averaged `w_k^+(L) / W_k(L)`):
       * Boolean lattices DO yield `(1, 1, ..., 1)` and attain global equality for ALL ranks
         (`boolean_chain_global_eq`, `boolean_avg_global_eq`).
       * Universal failure of log-concavity (`nonBoolean_rankSelector_not_logConcave`,
         `nonBoolean_avg_not_logConcave`): For EVERY non-Boolean geometric lattice `L`,
         log-concavity fails along EVERY maximal chain / rank-selector and for rank-averages!
       * Explicit disproof on `M_3` (`disproof_convention_II_chain`, `disproof_convention_II_avg`):
         The 5-element diamond geometric lattice `M_3` yields `(1, 1, 2)`, violating `1^2 ≥ 1 * 2`.
     - Convention III (Binomial-normalized Whitney numbers `w_k^+(L) / C(n, k)` / ultra-log-concavity):
       * Explicit disproof on `U_{3,4}` (`disproof_convention_III_ultra`):
         `w^+(U_{3,4}) = (1, 4, 6, 3)` gives `(1, 4/3, 2, 3)` with `(4/3)^2 = 16/9 < 2 = 1 * 2`.
-/

namespace Conjecture00000008539

/-! ## Section 1: Finite List Sums and Counting Helpers -/

def listSum {α : Type} (l : List α) (f : α → Int) : Int :=
  match l with
  | [] => 0
  | x :: xs => f x + listSum xs f

def natSum {α : Type} (l : List α) (f : α → Nat) : Nat :=
  match l with
  | [] => 0
  | x :: xs => f x + natSum xs f

theorem listSum_congr {α : Type} {l : List α} {f g : α → Int}
    (h : ∀ x, x ∈ l → f x = g x) : listSum l f = listSum l g := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [listSum]
    rw [h x (List.Mem.head xs), ih (fun y hy => h y (List.Mem.tail x hy))]

theorem listSum_zero {α : Type} {l : List α} {f : α → Int}
    (h : ∀ x, x ∈ l → f x = 0) : listSum l f = 0 := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [listSum]
    rw [h x (List.Mem.head xs), ih (fun y hy => h y (List.Mem.tail x hy))]
    rfl

theorem listSum_add {α : Type} (l : List α) (f g : α → Int) :
    listSum l (fun x => f x + g x) = listSum l f + listSum l g := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [listSum, ih]
    omega

theorem listSum_neg {α : Type} (l : List α) (f : α → Int) :
    listSum l (fun x => - f x) = - listSum l f := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [listSum, ih]
    omega

theorem listSum_mul_left {α : Type} (l : List α) (c : Int) (f : α → Int) :
    c * listSum l f = listSum l (fun x => c * f x) := by
  induction l with
  | nil => simp [listSum]
  | cons x xs ih =>
    simp only [listSum, Int.mul_add, ih]

theorem listSum_mul_right {α : Type} (l : List α) (f : α → Int) (c : Int) :
    listSum l f * c = listSum l (fun x => f x * c) := by
  induction l with
  | nil => simp [listSum]
  | cons x xs ih =>
    simp only [listSum, Int.add_mul, ih]

theorem listSum_comm {α β : Type} (l1 : List α) (l2 : List β) (h : α → β → Int) :
    listSum l1 (fun x => listSum l2 (fun y => h x y)) =
      listSum l2 (fun y => listSum l1 (fun x => h x y)) := by
  induction l1 with
  | nil =>
    symm
    exact listSum_zero (fun _ _ => rfl)
  | cons x xs ih =>
    simp only [listSum, ih, ← listSum_add]

theorem listSum_ite_eq {α : Type} [DecidableEq α] {l : List α}
    (hnodup : l.Nodup) {a : α} (ha : a ∈ l) (f : α → Int) :
    listSum l (fun x => if x = a then f x else 0) = f a := by
  induction l with
  | nil => cases ha
  | cons b bs ih =>
    have hnotmem : b ∉ bs := (List.nodup_cons.mp hnodup).1
    have hbs : bs.Nodup := (List.nodup_cons.mp hnodup).2
    simp only [listSum]
    by_cases hba : b = a
    · subst hba
      simp only [ite_true]
      have hz : listSum bs (fun x => if x = b then f x else 0) = 0 := by
        apply listSum_zero
        intro x hx
        have hne : x ≠ b := fun h => hnotmem (h ▸ hx)
        simp [hne]
      omega
    · simp only [hba, ite_false]
      cases ha with
      | head => exact absurd rfl hba
      | tail _ habs =>
        have hrec := ih hbs habs
        omega

theorem listSum_split {α : Type} (l : List α) (p : α → Prop) [DecidablePred p] (f : α → Int) :
    listSum l f =
      listSum l (fun x => if p x then f x else 0) +
      listSum l (fun x => if ¬ p x then f x else 0) := by
  rw [← listSum_add]
  apply listSum_congr
  intro x _
  by_cases hp : p x <;> simp [hp]

theorem listSum_nonneg {α : Type} {l : List α} {f : α → Int}
    (h : ∀ x, x ∈ l → 0 ≤ f x) : 0 ≤ listSum l f := by
  induction l with
  | nil => exact Int.le_refl 0
  | cons x xs ih =>
    simp only [listSum]
    have hx := h x (List.Mem.head xs)
    have hxs := ih (fun y hy => h y (List.Mem.tail x hy))
    omega

theorem listSum_mem_le {α : Type} {l : List α} {f : α → Int}
    (h : ∀ x, x ∈ l → 0 ≤ f x) {a : α} (ha : a ∈ l) : f a ≤ listSum l f := by
  induction l with
  | nil => cases ha
  | cons x xs ih =>
    simp only [listSum]
    cases ha with
    | head =>
      have hxs := listSum_nonneg (fun y hy => h y (List.Mem.tail a hy))
      omega
    | tail _ haxs =>
      have hx := h x (List.Mem.head xs)
      have hrec := ih (fun y hy => h y (List.Mem.tail x hy)) haxs
      omega

theorem listSum_pair_le {α : Type} {l : List α} (hnodup : l.Nodup) {f : α → Int}
    (h : ∀ x, x ∈ l → 0 ≤ f x) {a b : α} (ha : a ∈ l) (hb : b ∈ l) (hab : a ≠ b) :
    f a + f b ≤ listSum l f := by
  induction l with
  | nil => cases ha
  | cons c cs ih =>
    have hcs : cs.Nodup := (List.nodup_cons.mp hnodup).2
    have hfcs : ∀ y, y ∈ cs → 0 ≤ f y := fun y hy => h y (List.Mem.tail c hy)
    simp only [listSum]
    cases ha with
    | head =>
      cases hb with
      | head => exact absurd rfl hab
      | tail _ hbcs =>
        have hle := listSum_mem_le hfcs hbcs
        omega
    | tail _ hacs =>
      cases hb with
      | head =>
        have hle := listSum_mem_le hfcs hacs
        omega
      | tail _ hbcs =>
        have hc := h c (List.Mem.head cs)
        have hrec := ih hcs hfcs hacs hbcs
        omega

theorem natSum_congr {α : Type} {l : List α} {f g : α → Nat}
    (h : ∀ x, x ∈ l → f x = g x) : natSum l f = natSum l g := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [natSum]
    rw [h x (List.Mem.head xs), ih (fun y hy => h y (List.Mem.tail x hy))]

theorem natSum_zero {α : Type} {l : List α} {f : α → Nat}
    (h : ∀ x, x ∈ l → f x = 0) : natSum l f = 0 := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [natSum]
    rw [h x (List.Mem.head xs), ih (fun y hy => h y (List.Mem.tail x hy))]

theorem natSum_le_of_le {α : Type} {l : List α} {f g : α → Nat}
    (h : ∀ x, x ∈ l → f x ≤ g x) : natSum l f ≤ natSum l g := by
  induction l with
  | nil => exact Nat.le_refl 0
  | cons x xs ih =>
    simp only [natSum]
    have hx := h x (List.Mem.head xs)
    have hxs := ih (fun y hy => h y (List.Mem.tail x hy))
    omega

theorem natSum_lt_of_le_of_lt {α : Type} {l : List α} {f g : α → Nat}
    (hle : ∀ x, x ∈ l → f x ≤ g x) {v : α} (hv : v ∈ l) (hlt : f v < g v) :
    natSum l f < natSum l g := by
  induction l with
  | nil => cases hv
  | cons x xs ih =>
    simp only [natSum]
    cases hv with
    | head =>
      have hxs := natSum_le_of_le (fun y hy => hle y (List.Mem.tail v hy))
      omega
    | tail _ hvxs =>
      have hx := hle x (List.Mem.head xs)
      have hrec := ih (fun y hy => hle y (List.Mem.tail x hy)) hvxs
      omega

theorem natSum_le_length_of_le_one {α : Type} (l : List α) (f : α → Nat)
    (h : ∀ x, x ∈ l → f x ≤ 1) : natSum l f ≤ l.length := by
  induction l with
  | nil => exact Nat.le_refl 0
  | cons x xs ih =>
    simp only [natSum, List.length_cons]
    have hx := h x (List.Mem.head xs)
    have hxs := ih (fun y hy => h y (List.Mem.tail x hy))
    omega

theorem natSum_ite_eq {α : Type} [DecidableEq α] {l : List α}
    (hnodup : l.Nodup) {a : α} (ha : a ∈ l) (f : α → Nat) :
    natSum l (fun x => if x = a then f x else 0) = f a := by
  induction l with
  | nil => cases ha
  | cons b bs ih =>
    have hnotmem : b ∉ bs := (List.nodup_cons.mp hnodup).1
    have hbs : bs.Nodup := (List.nodup_cons.mp hnodup).2
    simp only [natSum]
    by_cases hba : b = a
    · subst hba
      simp only [ite_true]
      have hz : natSum bs (fun x => if x = b then f x else 0) = 0 := by
        apply natSum_zero
        intro x hx
        have hne : x ≠ b := fun h => hnotmem (h ▸ hx)
        simp [hne]
      omega
    · simp only [hba, ite_false]
      cases ha with
      | head => exact absurd rfl hba
      | tail _ habs =>
        have hrec := ih hbs habs
        omega

theorem natSum_pos_of_mem {α : Type} {l : List α} {f : α → Nat}
    {a : α} (ha : a ∈ l) (hpos : 1 ≤ f a) : 1 ≤ natSum l f := by
  induction l with
  | nil => cases ha
  | cons x xs ih =>
    simp only [natSum]
    cases ha with
    | head => omega
    | tail _ haxs =>
      have hrec := ih haxs
      omega

theorem natSum_pair_ge_two {α : Type} {l : List α} (hnodup : l.Nodup) {f : α → Nat}
    {a b : α} (ha : a ∈ l) (hb : b ∈ l) (hab : a ≠ b)
    (hpa : 1 ≤ f a) (hpb : 1 ≤ f b) : 2 ≤ natSum l f := by
  induction l with
  | nil => cases ha
  | cons c cs ih =>
    have hcs : cs.Nodup := (List.nodup_cons.mp hnodup).2
    simp only [natSum]
    cases ha with
    | head =>
      cases hb with
      | head => exact absurd rfl hab
      | tail _ hbcs =>
        have h1 := natSum_pos_of_mem hbcs hpb
        omega
    | tail _ hacs =>
      cases hb with
      | head =>
        have h1 := natSum_pos_of_mem hacs hpa
        omega
      | tail _ hbcs =>
        have hrec := ih hcs hacs hbcs
        omega

theorem natSum_toInt {α : Type} (l : List α) (f : α → Nat) :
    (natSum l f : Int) = listSum l (fun x => (f x : Int)) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [natSum, listSum, Int.ofNat_add, ih]

/-! ## Section 2: Finite Posets and Incidence Algebra over Int -/

structure FinPoset (α : Type) [DecidableEq α] where
  elems : List α
  elems_nodup : elems.Nodup
  elems_complete : ∀ x : α, x ∈ elems
  le : α → α → Prop
  decLe : DecidableRel le
  le_refl : ∀ x : α, le x x
  le_antisymm : ∀ x y : α, le x y → le y x → x = y
  le_trans : ∀ x y z : α, le x y → le y z → le x z

attribute [instance] FinPoset.decLe

def FinPoset.lt {α : Type} [DecidableEq α] (P : FinPoset α) (x y : α) : Prop :=
  P.le x y ∧ x ≠ y

instance {α : Type} [DecidableEq α] (P : FinPoset α) : DecidableRel P.lt :=
  fun _ _ => instDecidableAnd

/-- Elements of the incidence algebra of a finite poset `P` over `Int`:
    functions `val : α → α → Int` vanishing when `¬ (x ≤ y)`. -/
structure IncidenceAlg {α : Type} [DecidableEq α] (P : FinPoset α) where
  val : α → α → Int
  zero_of_not_le : ∀ x y : α, ¬ P.le x y → val x y = 0

namespace IncidenceAlg

theorem ext {α : Type} [DecidableEq α] {P : FinPoset α}
    {f g : IncidenceAlg P} (h : ∀ x y : α, f.val x y = g.val x y) : f = g := by
  cases f with
  | mk vf hf =>
    cases g with
    | mk vg hg =>
      have hv : vf = vg := funext (fun x => funext (fun y => h x y))
      subst hv
      rfl

/-- Multiplicative identity `delta` in the incidence algebra. -/
def delta {α : Type} [DecidableEq α] (P : FinPoset α) : IncidenceAlg P where
  val x y := if x = y then 1 else 0
  zero_of_not_le x y hnot := by
    have hne : x ≠ y := fun h => hnot (h ▸ P.le_refl x)
    simp [hne]

/-- The `zeta` function of `P` in the incidence algebra: `zeta(x, y) = 1` iff `x ≤ y`. -/
def zeta {α : Type} [DecidableEq α] (P : FinPoset α) : IncidenceAlg P where
  val x y := if P.le x y then 1 else 0
  zero_of_not_le x y hnot := by simp [hnot]

/-- Convolution product `(f * g)(x, y) = ∑_{z ∈ P} f(x, z) * g(z, y)` in the incidence algebra. -/
def mul {α : Type} [DecidableEq α] {P : FinPoset α}
    (f g : IncidenceAlg P) : IncidenceAlg P where
  val x y := listSum P.elems (fun z => f.val x z * g.val z y)
  zero_of_not_le x y hnot := by
    apply listSum_zero
    intro z _
    by_cases hxz : P.le x z
    · have hnzy : ¬ P.le z y := fun hzy => hnot (P.le_trans x z y hxz hzy)
      rw [g.zero_of_not_le z y hnzy]
      simp
    · rw [f.zero_of_not_le x z hxz]
      simp

/-- Convolution restricts to the closed interval `[x, y]`. -/
theorem mul_val_interval {α : Type} [DecidableEq α] {P : FinPoset α}
    (f g : IncidenceAlg P) (x y : α) :
    (mul f g).val x y =
      listSum P.elems (fun z => if P.le x z ∧ P.le z y then f.val x z * g.val z y else 0) := by
  unfold mul
  apply listSum_congr
  intro z _
  by_cases hxz : P.le x z
  · by_cases hzy : P.le z y
    · simp [hxz, hzy]
    · simp [hxz, hzy, g.zero_of_not_le z y hzy]
  · simp [hxz, f.zero_of_not_le x z hxz]

theorem delta_mul {α : Type} [DecidableEq α] {P : FinPoset α} (f : IncidenceAlg P) :
    mul (delta P) f = f := by
  apply ext
  intro x y
  unfold mul delta
  simp only []
  have h1 : listSum P.elems (fun z => (if x = z then (1 : Int) else 0) * f.val z y) =
      listSum P.elems (fun z => if z = x then f.val z y else 0) := by
    apply listSum_congr
    intro z _
    by_cases hzx : z = x
    · subst hzx; simp
    · have hxz : x ≠ z := fun h => hzx h.symm
      simp [hzx, hxz]
  rw [h1]
  exact listSum_ite_eq P.elems_nodup (P.elems_complete x) (fun z => f.val z y)

theorem mul_delta {α : Type} [DecidableEq α] {P : FinPoset α} (f : IncidenceAlg P) :
    mul f (delta P) = f := by
  apply ext
  intro x y
  unfold mul delta
  simp only []
  have h1 : listSum P.elems (fun z => f.val x z * (if z = y then (1 : Int) else 0)) =
      listSum P.elems (fun z => if z = y then f.val x z else 0) := by
    apply listSum_congr
    intro z _
    by_cases hzy : z = y
    · subst hzy; simp
    · simp [hzy]
  rw [h1]
  exact listSum_ite_eq P.elems_nodup (P.elems_complete y) (fun z => f.val x z)

theorem mul_assoc {α : Type} [DecidableEq α] {P : FinPoset α}
    (f g h : IncidenceAlg P) : mul (mul f g) h = mul f (mul g h) := by
  apply ext
  intro x y
  unfold mul
  simp only []
  have lhs_eq :
      listSum P.elems (fun u => listSum P.elems (fun v => f.val x v * g.val v u) * h.val u y) =
      listSum P.elems (fun u => listSum P.elems (fun v => f.val x v * g.val v u * h.val u y)) := by
    apply listSum_congr
    intro u _
    exact listSum_mul_right P.elems (fun v => f.val x v * g.val v u) (h.val u y)
  have rhs_eq :
      listSum P.elems (fun v => f.val x v * listSum P.elems (fun u => g.val v u * h.val u y)) =
      listSum P.elems (fun v => listSum P.elems (fun u => f.val x v * g.val v u * h.val u y)) := by
    apply listSum_congr
    intro v _
    rw [listSum_mul_left]
    apply listSum_congr
    intro u _
    rw [Int.mul_assoc]
  rw [lhs_eq, rhs_eq, listSum_comm]

/-- Definition from SOURCE.md: `m` is the Mobius function of `P` iff `m` is the
    (two-sided) inverse of `zeta` in the incidence algebra of `P`. -/
def IsMobius {α : Type} [DecidableEq α] (P : FinPoset α) (m : IncidenceAlg P) : Prop :=
  mul m (zeta P) = delta P ∧ mul (zeta P) m = delta P

/-- Cardinality of the closed interval `[x, y]` in `P`. -/
def intervalSize {α : Type} [DecidableEq α] (P : FinPoset α) (x y : α) : Nat :=
  natSum P.elems (fun z => if P.le x z ∧ P.le z y then 1 else 0)

theorem intervalSize_le_length {α : Type} [DecidableEq α] (P : FinPoset α) (x y : α) :
    intervalSize P x y ≤ P.elems.length := by
  apply natSum_le_length_of_le_one
  intro z _
  by_cases h : P.le x z ∧ P.le z y <;> simp [h]

theorem intervalSize_lt_right {α : Type} [DecidableEq α] (P : FinPoset α)
    {x z y : α} (hxz : P.le x z) (hzy : P.le z y) (hzy_ne : z ≠ y) :
    intervalSize P x z < intervalSize P x y := by
  apply natSum_lt_of_le_of_lt
  · intro w _
    by_cases hw : P.le x w ∧ P.le w z
    · have hwy : P.le w y := P.le_trans w z y hw.2 hzy
      simp [hw, hwy]
    · simp [hw]
  · exact P.elems_complete y
  · have hxy : P.le x y := P.le_trans x z y hxz hzy
    have hyy : P.le y y := P.le_refl y
    have hnotyz : ¬ P.le y z := fun hyz => hzy_ne (P.le_antisymm z y hzy hyz)
    simp [hxy, hyy, hnotyz]

theorem intervalSize_lt_left {α : Type} [DecidableEq α] (P : FinPoset α)
    {x z y : α} (hxz : P.le x z) (hzy : P.le z y) (hxz_ne : x ≠ z) :
    intervalSize P z y < intervalSize P x y := by
  apply natSum_lt_of_le_of_lt
  · intro w _
    by_cases hw : P.le z w ∧ P.le w y
    · have hxw : P.le x w := P.le_trans x z w hxz hw.1
      simp [hw, hxw]
    · simp [hw]
  · exact P.elems_complete x
  · have hxy : P.le x y := P.le_trans x z y hxz hzy
    have hxx : P.le x x := P.le_refl x
    have hnotzx : ¬ P.le z x := fun hzx => hxz_ne (P.le_antisymm x z hxz hzx)
    simp [hxy, hxx, hnotzx]

theorem intervalSize_ge_two {α : Type} [DecidableEq α] (P : FinPoset α)
    {x y : α} (hxy : P.le x y) (hne : x ≠ y) : 2 ≤ intervalSize P x y := by
  apply natSum_pair_ge_two P.elems_nodup (P.elems_complete x) (P.elems_complete y) hne
  · simp [P.le_refl x, hxy]
  · simp [hxy, P.le_refl y]

/-- Structural-recursion left-inverse construction with fuel `k`. -/
def muLeftFuel {α : Type} [DecidableEq α] (P : FinPoset α) : Nat → α → α → Int
  | 0, x, y => if P.le x y ∧ x = y then 1 else 0
  | k + 1, x, y =>
    if ¬ P.le x y then 0
    else if x = y then 1
    else - listSum P.elems (fun z =>
      if P.le x z ∧ P.le z y ∧ z ≠ y then muLeftFuel P k x z else 0)

theorem muLeftFuel_eq_succ {α : Type} [DecidableEq α] (P : FinPoset α) :
    ∀ (k : Nat) (x y : α), intervalSize P x y ≤ k →
      muLeftFuel P k x y = muLeftFuel P (k + 1) x y
  | 0, x, y, hle => by
    by_cases hxy : P.le x y
    · by_cases heq : x = y
      · subst heq; simp [muLeftFuel, hxy]
      · have h2 := intervalSize_ge_two P hxy heq
        omega
    · simp [muLeftFuel, hxy]
  | k + 1, x, y, hle => by
    conv => lhs; unfold muLeftFuel
    conv => rhs; unfold muLeftFuel
    by_cases hxy : P.le x y
    · by_cases heq : x = y
      · subst heq; simp [hxy]
      · simp only [hxy, not_true_eq_false, ite_false, heq]
        congr 1
        apply listSum_congr
        intro z _
        by_cases hz : P.le x z ∧ P.le z y ∧ z ≠ y
        · have hlt := intervalSize_lt_right P hz.1 hz.2.1 hz.2.2
          have ih := muLeftFuel_eq_succ P k x z (by omega)
          rw [if_pos hz, if_pos hz, ih]
        · rw [if_neg hz, if_neg hz]
    · simp [hxy]

theorem muLeftFuel_unfold {α : Type} [DecidableEq α] (P : FinPoset α) (x y : α) :
    muLeftFuel P P.elems.length x y =
      if ¬ P.le x y then 0
      else if x = y then 1
      else - listSum P.elems (fun z =>
        if P.le x z ∧ P.le z y ∧ z ≠ y then muLeftFuel P P.elems.length x z else 0) := by
  have hlen := intervalSize_le_length P x y
  rw [muLeftFuel_eq_succ P P.elems.length x y hlen]
  rfl

/-- Structural-recursion right-inverse construction with fuel `k`. -/
def muRightFuel {α : Type} [DecidableEq α] (P : FinPoset α) : Nat → α → α → Int
  | 0, x, y => if P.le x y ∧ x = y then 1 else 0
  | k + 1, x, y =>
    if ¬ P.le x y then 0
    else if x = y then 1
    else - listSum P.elems (fun z =>
      if P.le x z ∧ P.le z y ∧ x ≠ z then muRightFuel P k z y else 0)

theorem muRightFuel_eq_succ {α : Type} [DecidableEq α] (P : FinPoset α) :
    ∀ (k : Nat) (x y : α), intervalSize P x y ≤ k →
      muRightFuel P k x y = muRightFuel P (k + 1) x y
  | 0, x, y, hle => by
    by_cases hxy : P.le x y
    · by_cases heq : x = y
      · subst heq; simp [muRightFuel, hxy]
      · have h2 := intervalSize_ge_two P hxy heq
        omega
    · simp [muRightFuel, hxy]
  | k + 1, x, y, hle => by
    conv => lhs; unfold muRightFuel
    conv => rhs; unfold muRightFuel
    by_cases hxy : P.le x y
    · by_cases heq : x = y
      · subst heq; simp [hxy]
      · simp only [hxy, not_true_eq_false, ite_false, heq]
        congr 1
        apply listSum_congr
        intro z _
        by_cases hz : P.le x z ∧ P.le z y ∧ x ≠ z
        · have hlt := intervalSize_lt_left P hz.1 hz.2.1 hz.2.2
          have ih := muRightFuel_eq_succ P k z y (by omega)
          rw [if_pos hz, if_pos hz, ih]
        · rw [if_neg hz, if_neg hz]
    · simp [hxy]

theorem muRightFuel_unfold {α : Type} [DecidableEq α] (P : FinPoset α) (x y : α) :
    muRightFuel P P.elems.length x y =
      if ¬ P.le x y then 0
      else if x = y then 1
      else - listSum P.elems (fun z =>
        if P.le x z ∧ P.le z y ∧ x ≠ z then muRightFuel P P.elems.length z y else 0) := by
  have hlen := intervalSize_le_length P x y
  rw [muRightFuel_eq_succ P P.elems.length x y hlen]
  rfl

/-- The canonical Mobius function of a finite poset `P`. -/
def mobius {α : Type} [DecidableEq α] (P : FinPoset α) : IncidenceAlg P where
  val x y := muLeftFuel P P.elems.length x y
  zero_of_not_le x y hnot := by
    rw [muLeftFuel_unfold]
    simp [hnot]

def mobiusRight {α : Type} [DecidableEq α] (P : FinPoset α) : IncidenceAlg P where
  val x y := muRightFuel P P.elems.length x y
  zero_of_not_le x y hnot := by
    rw [muRightFuel_unfold]
    simp [hnot]

theorem mobius_unfold {α : Type} [DecidableEq α] (P : FinPoset α) (x y : α) :
    (mobius P).val x y =
      if ¬ P.le x y then 0
      else if x = y then 1
      else - listSum P.elems (fun z =>
        if P.le x z ∧ P.le z y ∧ z ≠ y then (mobius P).val x z else 0) :=
  muLeftFuel_unfold P x y

theorem mobius_diag {α : Type} [DecidableEq α] (P : FinPoset α) (x : α) :
    (mobius P).val x x = 1 := by
  rw [mobius_unfold]
  simp [P.le_refl x]

theorem mobius_mul_zeta {α : Type} [DecidableEq α] (P : FinPoset α) :
    mul (mobius P) (zeta P) = delta P := by
  apply ext
  intro x y
  by_cases hxy : P.le x y
  · rw [mul_val_interval]
    have hsimp :
        listSum P.elems (fun z =>
          if P.le x z ∧ P.le z y then (mobius P).val x z * (zeta P).val z y else 0) =
        listSum P.elems (fun z =>
          if P.le x z ∧ P.le z y then (mobius P).val x z else 0) := by
      apply listSum_congr
      intro z _
      by_cases hz : P.le x z ∧ P.le z y
      · simp [hz, zeta]
      · simp [hz]
    rw [hsimp]
    by_cases heq : x = y
    · subst heq
      have h1 :
          listSum P.elems (fun z => if P.le x z ∧ P.le z x then (mobius P).val x z else 0) =
          listSum P.elems (fun z => if z = x then (mobius P).val x z else 0) := by
        apply listSum_congr
        intro z _
        by_cases hzx : z = x
        · subst hzx; simp [P.le_refl z]
        · have hnot : ¬ (P.le x z ∧ P.le z x) :=
            fun h => hzx (P.le_antisymm z x h.2 h.1)
          simp [hzx, hnot]
      rw [h1, listSum_ite_eq P.elems_nodup (P.elems_complete x)]
      simp [mobius_diag, delta]
    · rw [listSum_split P.elems (fun z => z = y)]
      have h_eq_y :
          listSum P.elems (fun z =>
            if z = y then (if P.le x z ∧ P.le z y then (mobius P).val x z else 0) else 0) =
          (mobius P).val x y := by
        have h1 :
            listSum P.elems (fun z =>
              if z = y then (if P.le x z ∧ P.le z y then (mobius P).val x z else 0) else 0) =
            listSum P.elems (fun z => if z = y then (mobius P).val x z else 0) := by
          apply listSum_congr
          intro z _
          by_cases hzy : z = y
          · subst hzy; simp [hxy, P.le_refl z]
          · simp [hzy]
        rw [h1]
        exact listSum_ite_eq P.elems_nodup (P.elems_complete y) (fun z => (mobius P).val x z)
      have h_ne_y :
          listSum P.elems (fun z =>
            if ¬ z = y then (if P.le x z ∧ P.le z y then (mobius P).val x z else 0) else 0) =
          listSum P.elems (fun z =>
            if P.le x z ∧ P.le z y ∧ z ≠ y then (mobius P).val x z else 0) := by
        apply listSum_congr
        intro z _
        by_cases hzy : z = y <;> by_cases hxz : P.le x z <;> by_cases hzy2 : P.le z y <;>
          simp [hzy, hxz, hzy2]
      rw [h_eq_y, h_ne_y]
      have hunf := mobius_unfold P x y
      simp only [hxy, not_true_eq_false, ite_false, heq] at hunf
      simp only [delta, heq, ite_false]
      omega
  · rw [(mul (mobius P) (zeta P)).zero_of_not_le x y hxy]
    rw [(delta P).zero_of_not_le x y hxy]

theorem zeta_mul_mobiusRight {α : Type} [DecidableEq α] (P : FinPoset α) :
    mul (zeta P) (mobiusRight P) = delta P := by
  apply ext
  intro x y
  by_cases hxy : P.le x y
  · rw [mul_val_interval]
    have hsimp :
        listSum P.elems (fun z =>
          if P.le x z ∧ P.le z y then (zeta P).val x z * (mobiusRight P).val z y else 0) =
        listSum P.elems (fun z =>
          if P.le x z ∧ P.le z y then (mobiusRight P).val z y else 0) := by
      apply listSum_congr
      intro z _
      by_cases hz : P.le x z ∧ P.le z y
      · simp [hz, zeta]
      · simp [hz]
    rw [hsimp]
    by_cases heq : x = y
    · subst heq
      have h1 :
          listSum P.elems (fun z => if P.le x z ∧ P.le z x then (mobiusRight P).val z x else 0) =
          listSum P.elems (fun z => if z = x then (mobiusRight P).val z x else 0) := by
        apply listSum_congr
        intro z _
        by_cases hzx : z = x
        · subst hzx; simp [P.le_refl z]
        · have hnot : ¬ (P.le x z ∧ P.le z x) :=
            fun h => hzx (P.le_antisymm z x h.2 h.1)
          simp [hzx, hnot]
      rw [h1, listSum_ite_eq P.elems_nodup (P.elems_complete x)]
      have hdiag : (mobiusRight P).val x x = 1 := by
        change muRightFuel P P.elems.length x x = 1
        rw [muRightFuel_unfold]
        simp [P.le_refl x]
      simp [hdiag, delta]
    · rw [listSum_split P.elems (fun z => z = x)]
      have h_eq_x :
          listSum P.elems (fun z =>
            if z = x then (if P.le x z ∧ P.le z y then (mobiusRight P).val z y else 0) else 0) =
          (mobiusRight P).val x y := by
        have h1 :
            listSum P.elems (fun z =>
              if z = x then (if P.le x z ∧ P.le z y then (mobiusRight P).val z y else 0) else 0) =
            listSum P.elems (fun z => if z = x then (mobiusRight P).val z y else 0) := by
          apply listSum_congr
          intro z _
          by_cases hzx : z = x
          · subst hzx; simp [hxy, P.le_refl z]
          · simp [hzx]
        rw [h1]
        exact listSum_ite_eq P.elems_nodup (P.elems_complete x) (fun z => (mobiusRight P).val z y)
      have h_ne_x :
          listSum P.elems (fun z =>
            if ¬ z = x then (if P.le x z ∧ P.le z y then (mobiusRight P).val z y else 0) else 0) =
          listSum P.elems (fun z =>
            if P.le x z ∧ P.le z y ∧ x ≠ z then (mobiusRight P).val z y else 0) := by
        apply listSum_congr
        intro z _
        by_cases hzx : z = x
        · subst hzx; simp
        · have hxz_ne : x ≠ z := fun h => hzx h.symm
          by_cases hxz : P.le x z <;> by_cases hzy : P.le z y <;>
            simp [hzx, hxz_ne, hxz, hzy]
      rw [h_eq_x, h_ne_x]
      have hunf : (mobiusRight P).val x y =
          if ¬ P.le x y then 0
          else if x = y then 1
          else - listSum P.elems (fun z =>
            if P.le x z ∧ P.le z y ∧ x ≠ z then (mobiusRight P).val z y else 0) :=
        muRightFuel_unfold P x y
      simp only [hxy, not_true_eq_false, ite_false, heq] at hunf
      simp only [delta, heq, ite_false]
      omega
  · rw [(mul (zeta P) (mobiusRight P)).zero_of_not_le x y hxy]
    rw [(delta P).zero_of_not_le x y hxy]

/-- Left and right inverses of `zeta` coincide by associativity. -/
theorem mobius_eq_mobiusRight {α : Type} [DecidableEq α] (P : FinPoset α) :
    mobius P = mobiusRight P := by
  calc
    mobius P = mul (mobius P) (delta P) := (mul_delta (mobius P)).symm
    _ = mul (mobius P) (mul (zeta P) (mobiusRight P)) := by rw [zeta_mul_mobiusRight]
    _ = mul (mul (mobius P) (zeta P)) (mobiusRight P) := (mul_assoc _ _ _).symm
    _ = mul (delta P) (mobiusRight P) := by rw [mobius_mul_zeta]
    _ = mobiusRight P := delta_mul (mobiusRight P)

theorem zeta_mul_mobius {α : Type} [DecidableEq α] (P : FinPoset α) :
    mul (zeta P) (mobius P) = delta P := by
  rw [mobius_eq_mobiusRight]
  exact zeta_mul_mobiusRight P

/-- `mobius P` is a genuine two-sided inverse of `zeta P` in the incidence algebra. -/
theorem mobius_is_mobius {α : Type} [DecidableEq α] (P : FinPoset α) :
    IsMobius P (mobius P) :=
  ⟨mobius_mul_zeta P, zeta_mul_mobius P⟩

/-- Uniqueness of the Mobius function in the incidence algebra. -/
theorem mobius_unique {α : Type} [DecidableEq α] (P : FinPoset α)
    (m : IncidenceAlg P) (hm : IsMobius P m) : m = mobius P := by
  calc
    m = mul m (delta P) := (mul_delta m).symm
    _ = mul m (mul (zeta P) (mobius P)) := by rw [zeta_mul_mobius]
    _ = mul (mul m (zeta P)) (mobius P) := (mul_assoc _ _ _).symm
    _ = mul (delta P) (mobius P) := by rw [hm.1]
    _ = mobius P := delta_mul (mobius P)

end IncidenceAlg

/-! ## Section 3: Finite Lattices, Geometric Lattices, Rank, and Boolean Lattices -/

def Covers {α : Type} [DecidableEq α] (P : FinPoset α) (x y : α) : Prop :=
  P.lt x y ∧ ∀ z : α, P.le x z → P.le z y → (z = x ∨ z = y)

instance {α : Type} [DecidableEq α] (P : FinPoset α) : DecidableRel (Covers P) := by
  intro x y
  unfold Covers
  have hdecAll : Decidable (∀ z : α, P.le x z → P.le z y → z = x ∨ z = y) := by
    have heqv : (∀ z : α, P.le x z → P.le z y → z = x ∨ z = y) ↔
        ∀ z, z ∈ P.elems → (P.le x z → P.le z y → z = x ∨ z = y) :=
      ⟨fun h z _ => h z, fun h z => h z (P.elems_complete z)⟩
    exact decidable_of_iff' _ heqv
  exact instDecidableAnd

theorem mobius_of_covers {α : Type} [DecidableEq α] (P : FinPoset α)
    {x y : α} (hcov : Covers P x y) : (IncidenceAlg.mobius P).val x y = -1 := by
  rw [IncidenceAlg.mobius_unfold]
  have hxy : P.le x y := hcov.1.1
  have hne : x ≠ y := hcov.1.2
  simp only [hxy, not_true_eq_false, ite_false, hne]
  have hsum :
      listSum P.elems (fun z =>
        if P.le x z ∧ P.le z y ∧ z ≠ y then (IncidenceAlg.mobius P).val x z else 0) =
      listSum P.elems (fun z => if z = x then (IncidenceAlg.mobius P).val x z else 0) := by
    apply listSum_congr
    intro z _
    by_cases hzx : z = x
    · subst hzx; simp [P.le_refl z, hxy, hne]
    · have hnot : ¬ (P.le x z ∧ P.le z y ∧ z ≠ y) := by
        intro h
        cases hcov.2 z h.1 h.2.1 with
        | inl h1 => exact hzx h1
        | inr h2 => exact h.2.2 h2
      simp [hzx, hnot]
  rw [hsum, listSum_ite_eq P.elems_nodup (P.elems_complete x), IncidenceAlg.mobius_diag]

structure FinLattice (α : Type) [DecidableEq α] extends FinPoset α where
  bot : α
  top : α
  inf : α → α → α
  sup : α → α → α
  bot_le : ∀ x : α, le bot x
  le_top : ∀ x : α, le x top
  inf_le_left : ∀ x y : α, le (inf x y) x
  inf_le_right : ∀ x y : α, le (inf x y) y
  le_inf : ∀ z x y : α, le z x → le z y → le z (inf x y)
  le_sup_left : ∀ x y : α, le x (sup x y)
  le_sup_right : ∀ x y : α, le y (sup x y)
  sup_le : ∀ x y z : α, le x z → le y z → le (sup x y) z

def IsAtom {α : Type} [DecidableEq α] (L : FinLattice α) (p : α) : Prop :=
  Covers L.toFinPoset L.bot p

instance {α : Type} [DecidableEq α] (L : FinLattice α) : DecidablePred (IsAtom L) :=
  fun p => inferInstanceAs (Decidable (Covers L.toFinPoset L.bot p))

/-- Standard textbook definition of a Boolean lattice: a bounded lattice that is
    distributive and complemented. -/
def IsBooleanLattice {α : Type} [DecidableEq α] (L : FinLattice α) : Prop :=
  (∀ x y z : α, L.inf x (L.sup y z) = L.sup (L.inf x y) (L.inf x z)) ∧
  (∀ x : α, ∃ y : α, L.inf x y = L.bot ∧ L.sup x y = L.top)

/-- Standard textbook definition of a finite geometric lattice (Birkhoff / Stanley EC1 §3.3):
    a finite lattice that is atomistic and semimodular (graded by `rk` with submodular rank). -/
structure GeometricLattice (α : Type) [DecidableEq α] extends FinLattice α where
  atomistic : ∀ x y : α, (∀ p : α, IsAtom toFinLattice p → le p x → le p y) → le x y
  rk : α → Nat
  rk_bot : rk bot = 0
  rk_cov : ∀ x y : α, Covers toFinPoset x y → rk y = rk x + 1
  rk_submod : ∀ x y : α, rk (sup x y) + rk (inf x y) ≤ rk x + rk y

def GeometricLattice.rank {α : Type} [DecidableEq α] (L : GeometricLattice α) : Nat :=
  L.rk L.top

def GeometricLattice.mu {α : Type} [DecidableEq α] (L : GeometricLattice α) (x y : α) : Int :=
  (IncidenceAlg.mobius L.toFinPoset).val x y

/-- Find an element in a non-empty list minimizing `m`. -/
def argminList {α : Type} (m : α → Nat) : (l : List α) → l ≠ [] → α
  | [x], _ => x
  | x :: y :: ys, _ =>
    let best := argminList m (y :: ys) (List.cons_ne_nil y ys)
    if m x ≤ m best then x else best

theorem argminList_mem {α : Type} (m : α → Nat) :
    ∀ (l : List α) (hne : l ≠ []), argminList m l hne ∈ l
  | [x], _ => List.Mem.head []
  | x :: y :: ys, _ => by
    unfold argminList
    by_cases h : m x ≤ m (argminList m (y :: ys) (List.cons_ne_nil y ys))
    · simp [h]
    · simp only [h, ite_false]
      exact List.Mem.tail x (argminList_mem m (y :: ys) (List.cons_ne_nil y ys))

theorem argminList_le {α : Type} (m : α → Nat) :
    ∀ (l : List α) (hne : l ≠ []) (z : α), z ∈ l → m (argminList m l hne) ≤ m z
  | [x], _, z, hz => by
    cases hz with
    | head => exact Nat.le_refl _
    | tail _ hnil => cases hnil
  | x :: y :: ys, _, z, hz => by
    unfold argminList
    have ih := argminList_le m (y :: ys) (List.cons_ne_nil y ys)
    by_cases h : m x ≤ m (argminList m (y :: ys) (List.cons_ne_nil y ys))
    · simp only [h, ite_true]
      cases hz with
      | head => exact Nat.le_refl _
      | tail _ hzys => exact Nat.le_trans h (ih z hzys)
    · simp only [h, ite_false]
      cases hz with
      | head => omega
      | tail _ hzys => exact ih z hzys

/-- Find an element in a non-empty list maximizing `m`. -/
def argmaxList {α : Type} (m : α → Nat) : (l : List α) → l ≠ [] → α
  | [x], _ => x
  | x :: y :: ys, _ =>
    let best := argmaxList m (y :: ys) (List.cons_ne_nil y ys)
    if m best ≤ m x then x else best

theorem argmaxList_mem {α : Type} (m : α → Nat) :
    ∀ (l : List α) (hne : l ≠ []), argmaxList m l hne ∈ l
  | [x], _ => List.Mem.head []
  | x :: y :: ys, _ => by
    unfold argmaxList
    by_cases h : m (argmaxList m (y :: ys) (List.cons_ne_nil y ys)) ≤ m x
    · simp [h]
    · simp only [h, ite_false]
      exact List.Mem.tail x (argmaxList_mem m (y :: ys) (List.cons_ne_nil y ys))

theorem argmaxList_ge {α : Type} (m : α → Nat) :
    ∀ (l : List α) (hne : l ≠ []) (z : α), z ∈ l → m z ≤ m (argmaxList m l hne)
  | [x], _, z, hz => by
    cases hz with
    | head => exact Nat.le_refl _
    | tail _ hnil => cases hnil
  | x :: y :: ys, _, z, hz => by
    unfold argmaxList
    have ih := argmaxList_ge m (y :: ys) (List.cons_ne_nil y ys)
    by_cases h : m (argmaxList m (y :: ys) (List.cons_ne_nil y ys)) ≤ m x
    · simp only [h, ite_true]
      cases hz with
      | head => exact Nat.le_refl _
      | tail _ hzys => exact Nat.le_trans (ih z hzys) h
    · simp only [h, ite_false]
      cases hz with
      | head => omega
      | tail _ hzys => exact ih z hzys

/-- In any finite poset, if `x < y`, there exists `z` with `x ≤ z` and `Covers P z y`. -/
theorem exists_cover_left {α : Type} [DecidableEq α] (P : FinPoset α)
    {x y : α} (hlt : P.lt x y) : ∃ z : α, P.le x z ∧ Covers P z y := by
  let cand := P.elems.filter (fun w => decide (P.le x w ∧ P.lt w y))
  have hx_mem : x ∈ cand := by
    rw [List.mem_filter]
    exact ⟨P.elems_complete x, decide_eq_true ⟨P.le_refl x, hlt⟩⟩
  have hne : cand ≠ [] := fun h => by rw [h] at hx_mem; cases hx_mem
  let z := argminList (fun w => IncidenceAlg.intervalSize P w y) cand hne
  have hz_mem : z ∈ cand := argminList_mem _ cand hne
  rw [List.mem_filter] at hz_mem
  have hz_prop : P.le x z ∧ P.lt z y := of_decide_eq_true hz_mem.2
  refine ⟨z, hz_prop.1, ⟨hz_prop.2, ?_⟩⟩
  intro u hzu huy
  by_cases hzy : u = z
  · exact Or.inl hzy
  · by_cases huy_eq : u = y
    · exact Or.inr huy_eq
    · exfalso
      have hu_mem : u ∈ cand := by
        rw [List.mem_filter]
        exact ⟨P.elems_complete u,
          decide_eq_true ⟨P.le_trans x z u hz_prop.1 hzu, ⟨huy, huy_eq⟩⟩⟩
      have hmin : IncidenceAlg.intervalSize P z y ≤ IncidenceAlg.intervalSize P u y :=
        argminList_le (fun w => IncidenceAlg.intervalSize P w y) cand hne u hu_mem
      have hstrict := IncidenceAlg.intervalSize_lt_left P hzu huy (fun h => hzy h.symm)
      omega

theorem rk_strict_mono_aux {α : Type} [DecidableEq α] (L : GeometricLattice α) :
    ∀ (k : Nat) (x y : α), IncidenceAlg.intervalSize L.toFinPoset x y ≤ k →
      L.toFinPoset.lt x y → L.rk x < L.rk y
  | 0, x, y, hle, hlt => by
    have h2 := IncidenceAlg.intervalSize_ge_two L.toFinPoset hlt.1 hlt.2
    omega
  | k + 1, x, y, hle, hlt => by
    obtain ⟨z, hxz, hcov⟩ := exists_cover_left L.toFinPoset hlt
    have hrky : L.rk y = L.rk z + 1 := L.rk_cov z y hcov
    by_cases hxz_eq : x = z
    · subst hxz_eq; omega
    · have hlt_z : IncidenceAlg.intervalSize L.toFinPoset x z <
          IncidenceAlg.intervalSize L.toFinPoset x y :=
        IncidenceAlg.intervalSize_lt_right L.toFinPoset hxz hcov.1.1 hcov.1.2
      have ih := rk_strict_mono_aux L k x z (by omega) ⟨hxz, hxz_eq⟩
      omega

theorem GeometricLattice.rk_strict_mono {α : Type} [DecidableEq α] (L : GeometricLattice α)
    {x y : α} (hlt : L.toFinPoset.lt x y) : L.rk x < L.rk y :=
  rk_strict_mono_aux L L.elems.length x y
    (IncidenceAlg.intervalSize_le_length L.toFinPoset x y) hlt

theorem GeometricLattice.rk_mono {α : Type} [DecidableEq α] (L : GeometricLattice α)
    {x y : α} (hle : L.le x y) : L.rk x ≤ L.rk y := by
  by_cases heq : x = y
  · subst heq; exact Nat.le_refl _
  · exact Nat.le_of_lt (L.rk_strict_mono ⟨hle, heq⟩)

/-- Uniqueness of the rank function on any finite geometric lattice. -/
theorem rk_unique_aux {α : Type} [DecidableEq α] (L : GeometricLattice α)
    (r : α → Nat) (hr_bot : r L.bot = 0)
    (hr_cov : ∀ x y : α, Covers L.toFinPoset x y → r y = r x + 1) :
    ∀ (k : Nat) (y : α), IncidenceAlg.intervalSize L.toFinPoset L.bot y ≤ k → r y = L.rk y
  | 0, y, hle => by
    by_cases heq : L.bot = y
    · subst heq; rw [hr_bot, L.rk_bot]
    · have h2 := IncidenceAlg.intervalSize_ge_two L.toFinPoset (L.bot_le y) heq
      omega
  | k + 1, y, hle => by
    by_cases heq : L.bot = y
    · subst heq; rw [hr_bot, L.rk_bot]
    · obtain ⟨z, hbz, hcov⟩ := exists_cover_left L.toFinPoset ⟨L.bot_le y, heq⟩
      have hlt := IncidenceAlg.intervalSize_lt_right L.toFinPoset hbz hcov.1.1 hcov.1.2
      have ih := rk_unique_aux L r hr_bot hr_cov k z (by omega)
      rw [hr_cov z y hcov, L.rk_cov z y hcov, ih]

theorem GeometricLattice.rk_unique {α : Type} [DecidableEq α] (L : GeometricLattice α)
    (r : α → Nat) (hr_bot : r L.bot = 0)
    (hr_cov : ∀ x y : α, Covers L.toFinPoset x y → r y = r x + 1) (y : α) :
    r y = L.rk y :=
  rk_unique_aux L r hr_bot hr_cov L.elems.length y
    (IncidenceAlg.intervalSize_le_length L.toFinPoset L.bot y)

theorem GeometricLattice.eq_bot_iff_rk_zero {α : Type} [DecidableEq α] (L : GeometricLattice α)
    (x : α) : x = L.bot ↔ L.rk x = 0 := by
  constructor
  · intro h; subst h; exact L.rk_bot
  · intro hrk
    by_cases h : x = L.bot
    · exact h
    · exfalso
      have hlt : L.rk L.bot < L.rk x :=
        L.rk_strict_mono ⟨L.bot_le x, fun hb => h hb.symm⟩
      rw [L.rk_bot, hrk] at hlt
      omega

theorem GeometricLattice.isAtom_iff_rk_one {α : Type} [DecidableEq α] (L : GeometricLattice α)
    (p : α) : IsAtom L.toFinLattice p ↔ L.rk p = 1 := by
  constructor
  · intro hatom
    have hcov := L.rk_cov L.bot p hatom
    rw [L.rk_bot] at hcov
    exact hcov
  · intro hrk
    refine ⟨⟨L.bot_le p, ?_⟩, ?_⟩
    · intro hbp
      subst hbp
      have hb0 := L.rk_bot
      omega
    · intro z _ hzp
      have hrz : L.rk z ≤ 1 := hrk ▸ L.rk_mono hzp
      by_cases hzb : z = L.bot
      · exact Or.inl hzb
      · right
        by_cases hzp_eq : z = p
        · exact hzp_eq
        · exfalso
          have h1 : 0 < L.rk z := by
            rw [← L.rk_bot]
            exact L.rk_strict_mono ⟨L.bot_le z, fun h => hzb h.symm⟩
          have h2 : L.rk z < L.rk p := L.rk_strict_mono ⟨hzp, hzp_eq⟩
          omega

theorem exists_elem_of_rk_le_aux {α : Type} [DecidableEq α] (L : GeometricLattice α) :
    ∀ (r m : Nat) (y : α), L.rk y = r → m ≤ r → ∃ x : α, L.le x y ∧ L.rk x = m
  | 0, m, y, hry, hm => by
    have hm0 : m = 0 := by omega
    subst hm0
    exact ⟨y, L.le_refl y, hry⟩
  | r + 1, m, y, hry, hm => by
    by_cases heq : m = r + 1
    · exact ⟨y, L.le_refl y, hry.trans heq.symm⟩
    · have hy_ne_bot : L.bot ≠ y := by
        intro h; subst h; rw [L.rk_bot] at hry; omega
      obtain ⟨z, _, hcov⟩ := exists_cover_left L.toFinPoset ⟨L.bot_le y, hy_ne_bot⟩
      have hrky : L.rk y = L.rk z + 1 := L.rk_cov z y hcov
      have hrz : L.rk z = r := by omega
      obtain ⟨x, hxz, hrkx⟩ := exists_elem_of_rk_le_aux L r m z hrz (by omega)
      exact ⟨x, L.le_trans x z y hxz hcov.1.1, hrkx⟩

theorem GeometricLattice.exists_elem_of_rk {α : Type} [DecidableEq α] (L : GeometricLattice α)
    {k : Nat} (hk : k ≤ L.rank) : ∃ x : α, L.rk x = k := by
  obtain ⟨x, _, hrk⟩ := exists_elem_of_rk_le_aux L L.rank k L.top rfl hk
  exact ⟨x, hrk⟩

/-! ## Section 4: Weisner's Theorem, Rota's Sign Theorem, and Boolean Characterization -/

/-- Weisner's Theorem for any finite lattice `L`: for any `a > bot` and any `y ∈ L`,
    `∑_{x : x ∨ a = y} mu(bot, x) = 0`. -/
theorem weisner_thm {α : Type} [DecidableEq α] (L : FinLattice α)
    {a : α} (ha : L.toFinPoset.lt L.bot a) (y : α) :
    listSum L.elems (fun x =>
      if L.sup x a = y then (IncidenceAlg.mobius L.toFinPoset).val L.bot x else 0) = 0 := by
  have houter :
      listSum L.elems (fun z =>
        if L.le a z ∧ L.le z y then
          listSum L.elems (fun x =>
            if L.le x z then (IncidenceAlg.mobius L.toFinPoset).val L.bot x else 0) *
            (IncidenceAlg.mobius L.toFinPoset).val z y
        else 0) = 0 := by
    apply listSum_zero
    intro z _
    by_cases hz : L.le a z ∧ L.le z y
    · simp only [hz, and_self, ite_true]
      have hbz_ne : L.bot ≠ z := by
        intro hbz
        subst hbz
        exact ha.2 (L.le_antisymm L.bot a ha.1 hz.1)
      have hmz :
          (IncidenceAlg.mul (IncidenceAlg.mobius L.toFinPoset)
            (IncidenceAlg.zeta L.toFinPoset)).val L.bot z = 0 := by
        rw [IncidenceAlg.mobius_mul_zeta]
        simp [IncidenceAlg.delta, hbz_ne]
      rw [IncidenceAlg.mul_val_interval] at hmz
      have hinner :
          listSum L.elems (fun x =>
            if L.le x z then (IncidenceAlg.mobius L.toFinPoset).val L.bot x else 0) =
          listSum L.toFinPoset.elems (fun x =>
            if L.toFinPoset.le L.bot x ∧ L.toFinPoset.le x z then
              (IncidenceAlg.mobius L.toFinPoset).val L.bot x *
                (IncidenceAlg.zeta L.toFinPoset).val x z
            else 0) := by
        apply listSum_congr
        intro x _
        have hbx : L.le L.bot x := L.bot_le x
        change (if L.le x z then (IncidenceAlg.mobius L.toFinPoset).val L.bot x else 0) =
          if L.le L.bot x ∧ L.le x z then
            (IncidenceAlg.mobius L.toFinPoset).val L.bot x * (if L.le x z then 1 else 0)
          else 0
        by_cases hxz : L.le x z <;> simp [hbx, hxz]
      rw [hinner, hmz]
      simp
    · simp [hz]
  have hswap :
      listSum L.elems (fun z =>
        if L.le a z ∧ L.le z y then
          listSum L.elems (fun x =>
            if L.le x z then (IncidenceAlg.mobius L.toFinPoset).val L.bot x else 0) *
            (IncidenceAlg.mobius L.toFinPoset).val z y
        else 0) =
      listSum L.elems (fun x =>
        (IncidenceAlg.mobius L.toFinPoset).val L.bot x *
          listSum L.elems (fun z =>
            if L.le (L.sup x a) z ∧ L.le z y then
              (IncidenceAlg.mobius L.toFinPoset).val z y
            else 0)) := by
    have step1 :
        listSum L.elems (fun z =>
          if L.le a z ∧ L.le z y then
            listSum L.elems (fun x =>
              if L.le x z then (IncidenceAlg.mobius L.toFinPoset).val L.bot x else 0) *
              (IncidenceAlg.mobius L.toFinPoset).val z y
          else 0) =
        listSum L.elems (fun z =>
          listSum L.elems (fun x =>
            if L.le (L.sup x a) z ∧ L.le z y then
              (IncidenceAlg.mobius L.toFinPoset).val L.bot x *
                (IncidenceAlg.mobius L.toFinPoset).val z y
            else 0)) := by
      apply listSum_congr
      intro z _
      by_cases hz : L.le a z ∧ L.le z y
      · simp only [hz, and_self, ite_true]
        rw [listSum_mul_right]
        apply listSum_congr
        intro x _
        by_cases hxz : L.le x z
        · have hsup : L.le (L.sup x a) z := L.sup_le x a z hxz hz.1
          simp [hxz, hsup, hz.2]
        · have hnsup : ¬ L.le (L.sup x a) z :=
            fun hs => hxz (L.le_trans x (L.sup x a) z (L.le_sup_left x a) hs)
          simp [hxz, hnsup]
      · simp only [hz, ite_false]
        symm
        apply listSum_zero
        intro x _
        have hnot : ¬ (L.le (L.sup x a) z ∧ L.le z y) := by
          intro hs
          exact hz ⟨L.le_trans a (L.sup x a) z (L.le_sup_right x a) hs.1, hs.2⟩
        simp [hnot]
    rw [step1, listSum_comm]
    apply listSum_congr
    intro x _
    rw [listSum_mul_left]
    apply listSum_congr
    intro z _
    by_cases hs : L.le (L.sup x a) z ∧ L.le z y <;> simp [hs]
  rw [hswap] at houter
  have heval :
      listSum L.elems (fun x =>
        (IncidenceAlg.mobius L.toFinPoset).val L.bot x *
          listSum L.elems (fun z =>
            if L.le (L.sup x a) z ∧ L.le z y then
              (IncidenceAlg.mobius L.toFinPoset).val z y
            else 0)) =
      listSum L.elems (fun x =>
        if L.sup x a = y then (IncidenceAlg.mobius L.toFinPoset).val L.bot x else 0) := by
    apply listSum_congr
    intro x _
    have hzm :
        (IncidenceAlg.mul (IncidenceAlg.zeta L.toFinPoset)
          (IncidenceAlg.mobius L.toFinPoset)).val (L.sup x a) y =
        (IncidenceAlg.delta L.toFinPoset).val (L.sup x a) y := by
      rw [IncidenceAlg.zeta_mul_mobius]
    rw [IncidenceAlg.mul_val_interval] at hzm
    have hinner :
        listSum L.elems (fun z =>
          if L.le (L.sup x a) z ∧ L.le z y then
            (IncidenceAlg.mobius L.toFinPoset).val z y
          else 0) =
        listSum L.toFinPoset.elems (fun z =>
          if L.toFinPoset.le (L.sup x a) z ∧ L.toFinPoset.le z y then
            (IncidenceAlg.zeta L.toFinPoset).val (L.sup x a) z *
              (IncidenceAlg.mobius L.toFinPoset).val z y
          else 0) := by
      apply listSum_congr
      intro z _
      change (if L.le (L.sup x a) z ∧ L.le z y then
          (IncidenceAlg.mobius L.toFinPoset).val z y else 0) =
        if L.le (L.sup x a) z ∧ L.le z y then
          (if L.le (L.sup x a) z then 1 else 0) *
            (IncidenceAlg.mobius L.toFinPoset).val z y
        else 0
      by_cases hs : L.le (L.sup x a) z ∧ L.le z y
      · simp [hs, hs.1]
      · simp [hs]
    rw [hinner, hzm]
    by_cases heq : L.sup x a = y <;> simp [IncidenceAlg.delta, heq]
  rw [← heval]
  exact houter

/-- Relative coatom complement existence in any geometric lattice. -/
theorem exists_rel_coatom_above {α : Type} [DecidableEq α] (L : GeometricLattice α)
    {p y z : α} (hp : IsAtom L.toFinLattice p) (hpy : L.le p y)
    (hzy : L.le z y) (hnpz : ¬ L.le p z) :
    ∃ x : α, L.le z x ∧ ¬ L.le p x ∧ L.sup x p = y ∧ x ≠ y := by
  let S := L.elems.filter (fun w => decide (L.le z w ∧ L.le w y ∧ ¬ L.le p w))
  have hz_mem : z ∈ S := by
    rw [List.mem_filter]
    exact ⟨L.elems_complete z, decide_eq_true ⟨L.le_refl z, hzy, hnpz⟩⟩
  have hne : S ≠ [] := fun h => by rw [h] at hz_mem; cases hz_mem
  let x := argmaxList L.rk S hne
  have hx_mem : x ∈ S := argmaxList_mem L.rk S hne
  rw [List.mem_filter] at hx_mem
  obtain ⟨hzx, hxy, hnpx⟩ := of_decide_eq_true hx_mem.2
  have hx_ne_y : x ≠ y := fun h => hnpx (h ▸ hpy)
  have hsup_eq : L.sup x p = y := by
    have hsup_le : L.le (L.sup x p) y := L.sup_le x p y hxy hpy
    by_cases hyl : L.le y (L.sup x p)
    · exact L.le_antisymm (L.sup x p) y hsup_le hyl
    · exfalso
      have hex_q : ∃ q : α, IsAtom L.toFinLattice q ∧ L.le q y ∧ ¬ L.le q (L.sup x p) := by
        by_cases hex : ∃ q : α, IsAtom L.toFinLattice q ∧ L.le q y ∧ ¬ L.le q (L.sup x p)
        · exact hex
        · exfalso
          apply hyl
          apply L.atomistic y (L.sup x p)
          intro q hq hqy
          by_cases hqs : L.le q (L.sup x p)
          · exact hqs
          · exact absurd ⟨q, hq, hqy, hqs⟩ hex
      obtain ⟨q, hq, hqy, hnq_sup⟩ := hex_q
      have hnqx : ¬ L.le q x :=
        fun hqx => hnq_sup (L.le_trans q x (L.sup x p) hqx (L.le_sup_left x p))
      have hinf_xq : L.inf x q = L.bot := by
        cases hq.2 (L.inf x q) (L.bot_le _) (L.inf_le_right x q) with
        | inl hb => exact hb
        | inr hqp => exact absurd (hqp ▸ L.inf_le_left x q) hnqx
      have hrk_xq_le : L.rk (L.sup x q) ≤ L.rk x + 1 := by
        have hsub := L.rk_submod x q
        have hrkq : L.rk q = 1 := (L.isAtom_iff_rk_one q).mp hq
        rw [hinf_xq, L.rk_bot, hrkq] at hsub
        omega
      have hx_lt_xq : L.toFinPoset.lt x (L.sup x q) := by
        refine ⟨L.le_sup_left x q, ?_⟩
        intro heq
        exact hnqx (heq ▸ L.le_sup_right x q)
      have hrk_x_lt_xq : L.rk x < L.rk (L.sup x q) := L.rk_strict_mono hx_lt_xq
      have hrk_xq : L.rk (L.sup x q) = L.rk x + 1 := by omega
      have hinf_xp : L.inf x p = L.bot := by
        cases hp.2 (L.inf x p) (L.bot_le _) (L.inf_le_right x p) with
        | inl hb => exact hb
        | inr hpp => exact absurd (hpp ▸ L.inf_le_left x p) hnpx
      have hrk_xp_le : L.rk (L.sup x p) ≤ L.rk x + 1 := by
        have hsub := L.rk_submod x p
        have hrkp : L.rk p = 1 := (L.isAtom_iff_rk_one p).mp hp
        rw [hinf_xp, L.rk_bot, hrkp] at hsub
        omega
      have hx_lt_xp : L.toFinPoset.lt x (L.sup x p) := by
        refine ⟨L.le_sup_left x p, ?_⟩
        intro heq
        exact hnpx (heq ▸ L.le_sup_right x p)
      have hrk_xp : L.rk (L.sup x p) = L.rk x + 1 := by
        have hlt := L.rk_strict_mono hx_lt_xp
        omega
      have hpxq : L.le p (L.sup x q) := by
        by_cases hpxq : L.le p (L.sup x q)
        · exact hpxq
        · exfalso
          have hxq_mem : L.sup x q ∈ S := by
            rw [List.mem_filter]
            exact ⟨L.elems_complete (L.sup x q), decide_eq_true
              ⟨L.le_trans z x (L.sup x q) hzx (L.le_sup_left x q),
               L.sup_le x q y hxy hqy, hpxq⟩⟩
          have hmax : L.rk (L.sup x q) ≤ L.rk x := argmaxList_ge L.rk S hne (L.sup x q) hxq_mem
          omega
      have hxp_le_xq : L.le (L.sup x p) (L.sup x q) :=
        L.sup_le x p (L.sup x q) (L.le_sup_left x q) hpxq
      have hxp_eq_xq : L.sup x p = L.sup x q := by
        by_cases heq : L.sup x p = L.sup x q
        · exact heq
        · exfalso
          have hlt := L.rk_strict_mono ⟨hxp_le_xq, heq⟩
          omega
      exact hnq_sup (hxp_eq_xq ▸ L.le_sup_right x q)
  exact ⟨x, hzx, hnpx, hsup_eq, hx_ne_y⟩

theorem rk_of_sup_atom_eq {α : Type} [DecidableEq α] (L : GeometricLattice α)
    {p x y : α} (hp : IsAtom L.toFinLattice p) (hsup : L.sup x p = y) (hne : x ≠ y) :
    L.rk y = L.rk x + 1 := by
  have hnpx : ¬ L.le p x := by
    intro hpx
    have hyx : L.le y x := hsup ▸ L.sup_le x p x (L.le_refl x) hpx
    have hxy : L.le x y := hsup ▸ L.le_sup_left x p
    exact hne (L.le_antisymm x y hxy hyx)
  have hinf : L.inf x p = L.bot := by
    cases hp.2 (L.inf x p) (L.bot_le _) (L.inf_le_right x p) with
    | inl hb => exact hb
    | inr hpp => exact absurd (hpp ▸ L.inf_le_left x p) hnpx
  have hsub := L.rk_submod x p
  have hrkp : L.rk p = 1 := (L.isAtom_iff_rk_one p).mp hp
  rw [hsup, hinf, L.rk_bot, hrkp] at hsub
  have hlt : L.rk x < L.rk y := L.rk_strict_mono ⟨hsup ▸ L.le_sup_left x p, hne⟩
  omega

theorem exists_atom_le_of_ne_bot {α : Type} [DecidableEq α] (L : GeometricLattice α)
    {y : α} (hy : y ≠ L.bot) : ∃ p : α, IsAtom L.toFinLattice p ∧ L.le p y := by
  by_cases hex : ∃ p : α, IsAtom L.toFinLattice p ∧ L.le p y
  · exact hex
  · exfalso
    have hyb : L.le y L.bot := L.atomistic y L.bot (fun p hp hpy => absurd ⟨p, hp, hpy⟩ hex)
    exact hy (L.le_antisymm y L.bot hyb (L.bot_le y))

def signPow (k : Nat) : Int := (-1 : Int) ^ k

theorem signPow_succ (k : Nat) : signPow (k + 1) = - signPow k := by
  unfold signPow
  rw [Int.pow_succ]
  omega

/-- Weisner's recurrence in signed form for any atom `p ≤ y`. -/
theorem signed_weisner_atom {α : Type} [DecidableEq α] (L : GeometricLattice α)
    {p y : α} (hp : IsAtom L.toFinLattice p) (hpy : L.le p y) :
    signPow (L.rk y) * L.mu L.bot y =
      listSum L.elems (fun x =>
        if L.sup x p = y ∧ x ≠ y then signPow (L.rk x) * L.mu L.bot x else 0) := by
  have hw := weisner_thm L.toFinLattice hp.1 y
  rw [listSum_split L.elems (fun x => x = y)] at hw
  have h_eq_y :
      listSum L.elems (fun x =>
        if x = y then (if L.sup x p = y then L.mu L.bot x else 0) else 0) =
      L.mu L.bot y := by
    have hsup_y : L.sup y p = y :=
      L.le_antisymm (L.sup y p) y (L.sup_le y p y (L.le_refl y) hpy) (L.le_sup_left y p)
    have h1 :
        listSum L.elems (fun x =>
          if x = y then (if L.sup x p = y then L.mu L.bot x else 0) else 0) =
        listSum L.elems (fun x => if x = y then L.mu L.bot x else 0) := by
      apply listSum_congr
      intro x _
      by_cases hxy : x = y
      · subst hxy; simp [hsup_y]
      · simp [hxy]
    rw [h1]
    exact listSum_ite_eq L.elems_nodup (L.elems_complete y) (fun x => L.mu L.bot x)
  have h_ne_y :
      listSum L.elems (fun x =>
        if ¬ x = y then (if L.sup x p = y then L.mu L.bot x else 0) else 0) =
      listSum L.elems (fun x => if L.sup x p = y ∧ x ≠ y then L.mu L.bot x else 0) := by
    apply listSum_congr
    intro x _
    by_cases hxy : x = y <;> by_cases hs : L.sup x p = y <;> simp [hxy, hs]
  change (listSum L.elems (fun x =>
      if x = y then (if L.sup x p = y then L.mu L.bot x else 0) else 0) +
    listSum L.elems (fun x =>
      if ¬ x = y then (if L.sup x p = y then L.mu L.bot x else 0) else 0)) = 0 at hw
  rw [h_eq_y, h_ne_y] at hw
  have hmu_y : L.mu L.bot y =
      - listSum L.elems (fun x => if L.sup x p = y ∧ x ≠ y then L.mu L.bot x else 0) := by
    omega
  rw [hmu_y]
  have hmul :
      signPow (L.rk y) *
        (- listSum L.elems (fun x => if L.sup x p = y ∧ x ≠ y then L.mu L.bot x else 0)) =
      listSum L.elems (fun x =>
        if L.sup x p = y ∧ x ≠ y then (- signPow (L.rk y)) * L.mu L.bot x else 0) := by
    rw [Int.mul_neg, listSum_mul_left, ← listSum_neg]
    apply listSum_congr
    intro x _
    by_cases hs : L.sup x p = y ∧ x ≠ y
    · rw [if_pos hs, if_pos hs, Int.neg_mul]
    · rw [if_neg hs, if_neg hs]
      simp
  rw [hmul]
  apply listSum_congr
  intro x _
  by_cases hs : L.sup x p = y ∧ x ≠ y
  · rw [if_pos hs, if_pos hs]
    have hrk := rk_of_sup_atom_eq L hp hs.1 hs.2
    rw [hrk, signPow_succ, Int.neg_neg]
  · rw [if_neg hs, if_neg hs]

/-- Rota's Strict Sign Theorem (1964) for arbitrary finite geometric lattices:
    `(-1)^rk(y) * mu(bot, y) ≥ 1` for every `y ∈ L`. -/
theorem rota_sign_thm_aux {α : Type} [DecidableEq α] (L : GeometricLattice α) :
    ∀ (m : Nat) (y : α), L.rk y ≤ m → 1 ≤ signPow (L.rk y) * L.mu L.bot y
  | 0, y, hle => by
    have hyb : y = L.bot := (L.eq_bot_iff_rk_zero y).mpr (by omega)
    subst hyb
    rw [L.rk_bot]
    have hd : L.mu L.bot L.bot = 1 := IncidenceAlg.mobius_diag L.toFinPoset L.bot
    simp [signPow, hd]
  | m + 1, y, hle => by
    by_cases hyb : y = L.bot
    · subst hyb
      rw [L.rk_bot]
      have hd : L.mu L.bot L.bot = 1 := IncidenceAlg.mobius_diag L.toFinPoset L.bot
      simp [signPow, hd]
    · obtain ⟨p, hp, hpy⟩ := exists_atom_le_of_ne_bot L hyb
      rw [signed_weisner_atom L hp hpy]
      have hnpb : ¬ L.le p L.bot :=
        fun hpb => hp.1.2 (L.le_antisymm L.bot p (L.bot_le p) hpb)
      obtain ⟨x0, _, _, hsup0, hne0⟩ := exists_rel_coatom_above L hp hpy (L.bot_le y) hnpb
      let f : α → Int := fun x =>
        if L.sup x p = y ∧ x ≠ y then signPow (L.rk x) * L.mu L.bot x else 0
      have hnonneg : ∀ x, x ∈ L.elems → 0 ≤ f x := by
        intro x _
        dsimp only [f]
        by_cases hs : L.sup x p = y ∧ x ≠ y
        · rw [if_pos hs]
          have hrk := rk_of_sup_atom_eq L hp hs.1 hs.2
          have ih := rota_sign_thm_aux L m x (by omega)
          omega
        · rw [if_neg hs]
          exact Int.le_refl 0
      have hle0 := listSum_mem_le hnonneg (L.elems_complete x0)
      have hfx0 : 1 ≤ f x0 := by
        dsimp only [f]
        rw [if_pos ⟨hsup0, hne0⟩]
        have hrk0 := rk_of_sup_atom_eq L hp hsup0 hne0
        exact rota_sign_thm_aux L m x0 (by omega)
      change 1 ≤ listSum L.elems f
      omega

theorem rota_sign_thm {α : Type} [DecidableEq α] (L : GeometricLattice α) (y : α) :
    1 ≤ signPow (L.rk y) * L.mu L.bot y :=
  rota_sign_thm_aux L (L.rk y) y (Nat.le_refl _)

theorem abs_mu_eq_signed {α : Type} [DecidableEq α] (L : GeometricLattice α) (y : α) :
    ((L.mu L.bot y).natAbs : Int) = signPow (L.rk y) * L.mu L.bot y := by
  have hpos := rota_sign_thm L y
  have hsp : signPow (L.rk y) = 1 ∨ signPow (L.rk y) = -1 := by
    unfold signPow
    induction (L.rk y) with
    | zero => exact Or.inl rfl
    | succ k ih =>
      rw [Int.pow_succ]
      cases ih with
      | inl h1 => rw [h1]; exact Or.inr rfl
      | inr h2 => rw [h2]; exact Or.inl rfl
  cases hsp with
  | inl h1 =>
    rw [h1] at hpos ⊢
    omega
  | inr h2 =>
    rw [h2] at hpos ⊢
    omega

theorem natAbs_mu_ge_one {α : Type} [DecidableEq α] (L : GeometricLattice α) (y : α) :
    1 ≤ (L.mu L.bot y).natAbs := by
  have h1 := rota_sign_thm L y
  rw [← abs_mu_eq_signed L y] at h1
  omega

/-- Every geometric lattice of rank `≤ 1` is a Boolean lattice (`B_0` or `B_1`). -/
theorem geom_rk_le_one_isBoolean {α : Type} [DecidableEq α] (L : GeometricLattice α)
    (hrk : L.rank ≤ 1) : IsBooleanLattice L.toFinLattice := by
  have hbot_or_top : ∀ x : α, x = L.bot ∨ x = L.top := by
    intro x
    have hxle : L.rk x ≤ 1 := Nat.le_trans (L.rk_mono (L.le_top x)) hrk
    by_cases hxb : x = L.bot
    · exact Or.inl hxb
    · right
      have hxpos : 1 ≤ L.rk x := by
        have hlt : L.rk L.bot < L.rk x :=
          L.rk_strict_mono ⟨L.bot_le x, fun h => hxb h.symm⟩
        rw [L.rk_bot] at hlt
        omega
      by_cases hxt : x = L.top
      · exact hxt
      · exfalso
        have hlt : L.rk x < L.rank := L.rk_strict_mono ⟨L.le_top x, hxt⟩
        omega
  have hinf_bot_l : ∀ z : α, L.inf L.bot z = L.bot := fun z =>
    L.le_antisymm _ _ (L.inf_le_left L.bot z) (L.bot_le _)
  have hinf_bot_r : ∀ z : α, L.inf z L.bot = L.bot := fun z =>
    L.le_antisymm _ _ (L.inf_le_right z L.bot) (L.bot_le _)
  have hinf_top_l : ∀ z : α, L.inf L.top z = z := fun z =>
    L.le_antisymm _ _ (L.inf_le_right L.top z) (L.le_inf z L.top z (L.le_top z) (L.le_refl z))
  have hinf_top_r : ∀ z : α, L.inf z L.top = z := fun z =>
    L.le_antisymm _ _ (L.inf_le_left z L.top) (L.le_inf z z L.top (L.le_refl z) (L.le_top z))
  have hsup_bot_l : ∀ z : α, L.sup L.bot z = z := fun z =>
    L.le_antisymm _ _ (L.sup_le L.bot z z (L.bot_le z) (L.le_refl z)) (L.le_sup_right L.bot z)
  have hsup_bot_r : ∀ z : α, L.sup z L.bot = z := fun z =>
    L.le_antisymm _ _ (L.sup_le z L.bot z (L.le_refl z) (L.bot_le z)) (L.le_sup_left z L.bot)
  have hsup_top_l : ∀ z : α, L.sup L.top z = L.top := fun z =>
    L.le_antisymm _ _ (L.le_top _) (L.le_sup_left L.top z)
  have hsup_top_r : ∀ z : α, L.sup z L.top = L.top := fun z =>
    L.le_antisymm _ _ (L.le_top _) (L.le_sup_right z L.top)
  constructor
  · intro x y z
    rcases hbot_or_top x with rfl | rfl <;>
      rcases hbot_or_top y with rfl | rfl <;>
      rcases hbot_or_top z with rfl | rfl <;>
      simp [hinf_bot_l, hinf_bot_r, hinf_top_l, hinf_top_r,
            hsup_bot_l, hsup_bot_r, hsup_top_l, hsup_top_r]
  · intro x
    rcases hbot_or_top x with rfl | rfl
    · exact ⟨L.top, hinf_bot_l L.top, hsup_bot_l L.top⟩
    · exact ⟨L.bot, hinf_bot_r L.top, hsup_bot_r L.top⟩

/-- Finite join over a list in `FinLattice`. -/
def listSup {α : Type} [DecidableEq α] (L : FinLattice α) : List α → α
  | [] => L.bot
  | x :: xs => L.sup x (listSup L xs)

theorem le_listSup_of_mem {α : Type} [DecidableEq α] (L : FinLattice α) :
    ∀ {l : List α} {x : α}, x ∈ l → L.le x (listSup L l)
  | [], _, hx => by cases hx
  | y :: ys, _, hx => by
    simp only [listSup]
    cases hx with
    | head => exact L.le_sup_left _ (listSup L ys)
    | tail _ hys =>
      exact L.le_trans _ (listSup L ys) (L.sup y (listSup L ys))
        (le_listSup_of_mem L hys) (L.le_sup_right y (listSup L ys))

theorem listSup_le_of_forall {α : Type} [DecidableEq α] (L : FinLattice α) :
    ∀ {l : List α} {u : α}, (∀ x, x ∈ l → L.le x u) → L.le (listSup L l) u
  | [], u, _ => L.bot_le u
  | y :: ys, u, h => by
    simp only [listSup]
    exact L.sup_le y (listSup L ys) u
      (h y (List.Mem.head ys))
      (listSup_le_of_forall L (fun x hx => h x (List.Mem.tail y hx)))

/-- In any Boolean geometric lattice `L`, `(-1)^rk(y) * mu(bot, y) = 1` for EVERY `y ∈ L`. -/
theorem boolean_signed_mu_eq_one_aux {α : Type} [DecidableEq α] (L : GeometricLattice α)
    (hbool : IsBooleanLattice L.toFinLattice) :
    ∀ (m : Nat) (y : α), L.rk y ≤ m → signPow (L.rk y) * L.mu L.bot y = 1
  | 0, y, hle => by
    have hyb : y = L.bot := (L.eq_bot_iff_rk_zero y).mpr (by omega)
    subst hyb
    rw [L.rk_bot]
    have hd : L.mu L.bot L.bot = 1 := IncidenceAlg.mobius_diag L.toFinPoset L.bot
    simp [signPow, hd]
  | m + 1, y, hle => by
    by_cases hyb : y = L.bot
    · subst hyb
      rw [L.rk_bot]
      have hd : L.mu L.bot L.bot = 1 := IncidenceAlg.mobius_diag L.toFinPoset L.bot
      simp [signPow, hd]
    · obtain ⟨p, hp, hpy⟩ := exists_atom_le_of_ne_bot L hyb
      rw [signed_weisner_atom L hp hpy]
      have hnpb : ¬ L.le p L.bot :=
        fun hpb => hp.1.2 (L.le_antisymm L.bot p (L.bot_le p) hpb)
      obtain ⟨x0, _, _, hsup0, hne0⟩ := exists_rel_coatom_above L hp hpy (L.bot_le y) hnpb
      have huniq : ∀ x : α, (L.sup x p = y ∧ x ≠ y) → x = x0 := by
        intro x ⟨hsupx, hnex⟩
        have hinfx : L.inf x p = L.bot := by
          have hnpx : ¬ L.le p x := by
            intro hpx
            exact hnex (L.le_antisymm x y (hsupx ▸ L.le_sup_left x p)
              (hsupx ▸ L.sup_le x p x (L.le_refl x) hpx))
          cases hp.2 (L.inf x p) (L.bot_le _) (L.inf_le_right x p) with
          | inl hb => exact hb
          | inr hpp => exact absurd (hpp ▸ L.inf_le_left x p) hnpx
        have hinf0 : L.inf x0 p = L.bot := by
          have hnpx0 : ¬ L.le p x0 := by
            intro hpx0
            exact hne0 (L.le_antisymm x0 y (hsup0 ▸ L.le_sup_left x0 p)
              (hsup0 ▸ L.sup_le x0 p x0 (L.le_refl x0) hpx0))
          cases hp.2 (L.inf x0 p) (L.bot_le _) (L.inf_le_right x0 p) with
          | inl hb => exact hb
          | inr hpp => exact absurd (hpp ▸ L.inf_le_left x0 p) hnpx0
        have hsup_bot : ∀ u : α, L.sup u L.bot = u := fun u =>
          L.le_antisymm _ _ (L.sup_le u L.bot u (L.le_refl u) (L.bot_le u)) (L.le_sup_left u L.bot)
        have hinf_comm : ∀ u v : α, L.inf u v = L.inf v u := fun u v =>
          L.le_antisymm _ _
            (L.le_inf _ v u (L.inf_le_right u v) (L.inf_le_left u v))
            (L.le_inf _ u v (L.inf_le_right v u) (L.inf_le_left v u))
        have hx_eq : x = L.inf x x0 := by
          have hxy : L.le x y := hsupx ▸ L.le_sup_left x p
          calc
            x = L.inf x y :=
              L.le_antisymm _ _ (L.le_inf x x y (L.le_refl x) hxy) (L.inf_le_left x y)
            _ = L.inf x (L.sup x0 p) := by rw [← hsup0]
            _ = L.sup (L.inf x x0) (L.inf x p) := hbool.1 x x0 p
            _ = L.sup (L.inf x x0) L.bot := by rw [hinfx]
            _ = L.inf x x0 := hsup_bot _
        have hx0_eq : x0 = L.inf x0 x := by
          have hx0y : L.le x0 y := hsup0 ▸ L.le_sup_left x0 p
          calc
            x0 = L.inf x0 y :=
              L.le_antisymm _ _ (L.le_inf x0 x0 y (L.le_refl x0) hx0y) (L.inf_le_left x0 y)
            _ = L.inf x0 (L.sup x p) := by rw [← hsupx]
            _ = L.sup (L.inf x0 x) (L.inf x0 p) := hbool.1 x0 x p
            _ = L.sup (L.inf x0 x) L.bot := by rw [hinf0]
            _ = L.inf x0 x := hsup_bot _
        exact Eq.trans hx_eq (Eq.trans (hinf_comm x x0) hx0_eq.symm)
      have hsum :
          listSum L.elems (fun x =>
            if L.sup x p = y ∧ x ≠ y then signPow (L.rk x) * L.mu L.bot x else 0) =
          listSum L.elems (fun x =>
            if x = x0 then signPow (L.rk x) * L.mu L.bot x else 0) := by
        apply listSum_congr
        intro x _
        by_cases hxx0 : x = x0
        · subst hxx0; simp [hsup0, hne0]
        · have hnot : ¬ (L.sup x p = y ∧ x ≠ y) := fun hs => hxx0 (huniq x hs)
          simp [hxx0, hnot]
      rw [hsum, listSum_ite_eq L.elems_nodup (L.elems_complete x0)]
      have hrk0 := rk_of_sup_atom_eq L hp hsup0 hne0
      exact boolean_signed_mu_eq_one_aux L hbool m x0 (by omega)

theorem boolean_signed_mu_eq_one {α : Type} [DecidableEq α] (L : GeometricLattice α)
    (hbool : IsBooleanLattice L.toFinLattice) (y : α) :
    signPow (L.rk y) * L.mu L.bot y = 1 :=
  boolean_signed_mu_eq_one_aux L hbool (L.rk y) y (Nat.le_refl _)

theorem boolean_natAbs_mu_eq_one {α : Type} [DecidableEq α] (L : GeometricLattice α)
    (hbool : IsBooleanLattice L.toFinLattice) (y : α) :
    (L.mu L.bot y).natAbs = 1 := by
  have h1 := abs_mu_eq_signed L y
  rw [boolean_signed_mu_eq_one L hbool y] at h1
  omega

/-- Exact Mobius Characterization of Boolean Geometric Lattices:
    A finite geometric lattice `L` is Boolean if and only if `|mu(bot, top)| = 1`. -/
theorem isBoolean_iff_natAbs_mu_top_eq_one {α : Type} [DecidableEq α] (L : GeometricLattice α) :
    IsBooleanLattice L.toFinLattice ↔ (L.mu L.bot L.top).natAbs = 1 := by
  constructor
  · intro hbool
    exact boolean_natAbs_mu_eq_one L hbool L.top
  · intro habs
    have hsigned : signPow (L.rk L.top) * L.mu L.bot L.top = 1 := by
      rw [← abs_mu_eq_signed L L.top, habs]
      rfl
    have hcoatom : ∀ p : α, IsAtom L.toFinLattice p →
        ∃ cp : α, ∀ z : α, ¬ L.le p z ↔ L.le z cp := by
      intro p hp
      have hpt : L.le p L.top := L.le_top p
      have hnpb : ¬ L.le p L.bot :=
        fun hpb => hp.1.2 (L.le_antisymm L.bot p (L.bot_le p) hpb)
      obtain ⟨cp, _, hnp_cp, hsup_cp, hne_cp⟩ :=
        exists_rel_coatom_above L hp hpt (L.bot_le L.top) hnpb
      have hw := signed_weisner_atom L hp hpt
      rw [hsigned] at hw
      have huniq : ∀ x : α, L.sup x p = L.top ∧ x ≠ L.top → x = cp := by
        intro x hx
        by_cases hxeq : x = cp
        · exact hxeq
        · exfalso
          let f : α → Int := fun u =>
            if L.sup u p = L.top ∧ u ≠ L.top then signPow (L.rk u) * L.mu L.bot u else 0
          have hfnonneg : ∀ u, u ∈ L.elems → 0 ≤ f u := by
            intro u _
            dsimp only [f]
            by_cases hs : L.sup u p = L.top ∧ u ≠ L.top
            · rw [if_pos hs]
              have hr := rota_sign_thm L u
              omega
            · rw [if_neg hs]
              exact Int.le_refl 0
          have hpair := listSum_pair_le L.elems_nodup hfnonneg
            (L.elems_complete x) (L.elems_complete cp) hxeq
          have hfx : 1 ≤ f x := by
            dsimp only [f]
            rw [if_pos hx]
            exact rota_sign_thm L x
          have hfcp : 1 ≤ f cp := by
            dsimp only [f]
            rw [if_pos ⟨hsup_cp, hne_cp⟩]
            exact rota_sign_thm L cp
          change 1 = listSum L.elems f at hw
          omega
      refine ⟨cp, ?_⟩
      intro z
      constructor
      · intro hnpz
        obtain ⟨x, hzx, _, hsupx, hnex⟩ := exists_rel_coatom_above L hp hpt (L.le_top z) hnpz
        have hxcp := huniq x ⟨hsupx, hnex⟩
        subst hxcp
        exact hzx
      · intro hzcp hpz
        exact hnp_cp (L.le_trans p z cp hpz hzcp)
    constructor
    · intro x y z
      apply L.le_antisymm
      · apply L.atomistic
        intro p hp hp_lhs
        have hpx : L.le p x := L.le_trans p _ x hp_lhs (L.inf_le_left x (L.sup y z))
        have hpyz : L.le p (L.sup y z) :=
          L.le_trans p _ (L.sup y z) hp_lhs (L.inf_le_right x (L.sup y z))
        obtain ⟨cp, hcp⟩ := hcoatom p hp
        by_cases hpy : L.le p y
        · exact L.le_trans p (L.inf x y) _
            (L.le_inf p x y hpx hpy) (L.le_sup_left (L.inf x y) (L.inf x z))
        · have hpz : L.le p z := by
            by_cases hpz : L.le p z
            · exact hpz
            · exfalso
              have hycp : L.le y cp := (hcp y).mp hpy
              have hzcp : L.le z cp := (hcp z).mp hpz
              have hyzcp : L.le (L.sup y z) cp := L.sup_le y z cp hycp hzcp
              exact ((hcp (L.sup y z)).mpr hyzcp) hpyz
          exact L.le_trans p (L.inf x z) _
            (L.le_inf p x z hpx hpz) (L.le_sup_right (L.inf x y) (L.inf x z))
      · exact L.sup_le _ _ _
          (L.le_inf _ x (L.sup y z) (L.inf_le_left x y)
            (L.le_trans _ y _ (L.inf_le_right x y) (L.le_sup_left y z)))
          (L.le_inf _ x (L.sup y z) (L.inf_le_left x z)
            (L.le_trans _ z _ (L.inf_le_right x z) (L.le_sup_right y z)))
    · intro x
      let compAtoms := L.elems.filter (fun p => decide (IsAtom L.toFinLattice p ∧ ¬ L.le p x))
      let y := listSup L.toFinLattice compAtoms
      refine ⟨y, ?_, ?_⟩
      · apply L.le_antisymm
        · apply L.atomistic
          intro q hq hq_inf
          exfalso
          have hqx : L.le q x := L.le_trans q _ x hq_inf (L.inf_le_left x y)
          have hqy : L.le q y := L.le_trans q _ y hq_inf (L.inf_le_right x y)
          obtain ⟨cq, hcq⟩ := hcoatom q hq
          have hy_cq : L.le y cq := by
            apply listSup_le_of_forall
            intro p hp_mem
            rw [List.mem_filter] at hp_mem
            obtain ⟨hp_atom, hnpx⟩ := of_decide_eq_true hp_mem.2
            have hnqp : ¬ L.le q p := by
              intro hqp
              cases hp_atom.2 q (L.bot_le q) hqp with
              | inl hqb => exact hq.1.2 hqb.symm
              | inr hqp_eq => exact hnpx (hqp_eq ▸ hqx)
            exact (hcq p).mp hnqp
          exact ((hcq y).mpr hy_cq) hqy
        · exact L.bot_le (L.inf x y)
      · apply L.le_antisymm
        · exact L.le_top (L.sup x y)
        · apply L.atomistic
          intro p hp _
          by_cases hpx : L.le p x
          · exact L.le_trans p x (L.sup x y) hpx (L.le_sup_left x y)
          · have hp_mem : p ∈ compAtoms := by
              rw [List.mem_filter]
              exact ⟨L.elems_complete p, decide_eq_true ⟨hp, hpx⟩⟩
            have hpy : L.le p y := le_listSup_of_mem L.toFinLattice hp_mem
            exact L.le_trans p y (L.sup x y) hpy (L.le_sup_right x y)

/-! ## Section 5: Log-Concavity Predicates and All Natural Sequence Conventions -/

def HasFirstTermOne (a : Nat → Nat) : Prop :=
  a 0 = 1

def IsStrictlyPosSeq (n : Nat) (a : Nat → Nat) : Prop :=
  ∀ k : Nat, k ≤ n → 1 ≤ a k

/-- Standard log-concavity on `{0, ..., n}` (`a_k^2 ≥ a_{k-1} a_{k+1}` for all `1 ≤ k ≤ n - 1`).
    For strictly positive sequences (`IsStrictlyPosSeq`), internal zeros never occur. -/
def IsLogConcave (n : Nat) (a : Nat → Nat) : Prop :=
  ∀ k : Nat, 1 ≤ k → k + 1 ≤ n → a (k - 1) * a (k + 1) ≤ a k * a k

/-- Global log-concavity equality (`a_k^2 = a_{k-1} a_{k+1}` for all `1 ≤ k ≤ n - 1`). -/
def GlobalLogConcaveEq (n : Nat) (a : Nat → Nat) : Prop :=
  ∀ k : Nat, 1 ≤ k → k + 1 ≤ n → a k * a k = a (k - 1) * a (k + 1)

/-- Exact cross-multiplied predicates for positive rational sequences `num k / den k`. -/
def HasFirstTermOneRat (num den : Nat → Nat) : Prop :=
  num 0 = den 0 ∧ 1 ≤ den 0

def IsLogConcaveRat (n : Nat) (num den : Nat → Nat) : Prop :=
  ∀ k : Nat, 1 ≤ k → k + 1 ≤ n →
    num (k - 1) * num (k + 1) * (den k * den k) ≤
      num k * num k * (den (k - 1) * den (k + 1))

def GlobalLogConcaveEqRat (n : Nat) (num den : Nat → Nat) : Prop :=
  ∀ k : Nat, 1 ≤ k → k + 1 ≤ n →
    num k * num k * (den (k - 1) * den (k + 1)) =
      num (k - 1) * num (k + 1) * (den k * den k)

/-- Convention I: Unsigned Whitney numbers of the first kind
    `w_k^+(L) = ∑_{x ∈ L, rk(x) = k} |mu(bot, x)|`. -/
def whitney1Abs {α : Type} [DecidableEq α] (L : GeometricLattice α) (k : Nat) : Nat :=
  natSum L.elems (fun x => if L.rk x = k then (L.mu L.bot x).natAbs else 0)

/-- Whitney numbers of the second kind `W_k(L) = |{x ∈ L : rk(x) = k}|`. -/
def whitney2 {α : Type} [DecidableEq α] (L : GeometricLattice α) (k : Nat) : Nat :=
  natSum L.elems (fun x => if L.rk x = k then 1 else 0)

/-- Maximal chains `bot = c 0 ⋖ c 1 ⋖ ... ⋖ c n = top` and rank-selectors `rk(s k) = k`. -/
def IsMaximalChain {α : Type} [DecidableEq α] (L : GeometricLattice α) (c : Nat → α) : Prop :=
  c 0 = L.bot ∧ c L.rank = L.top ∧ ∀ k : Nat, k < L.rank → Covers L.toFinPoset (c k) (c (k + 1))

def IsRankSelector {α : Type} [DecidableEq α] (L : GeometricLattice α) (s : Nat → α) : Prop :=
  ∀ k : Nat, k ≤ L.rank → L.rk (s k) = k

theorem maximalChain_is_rankSelector {α : Type} [DecidableEq α] (L : GeometricLattice α)
    {c : Nat → α} (hc : IsMaximalChain L c) : IsRankSelector L c := by
  intro k hk
  induction k with
  | zero => rw [hc.1, L.rk_bot]
  | succ j ih =>
    have hj : j < L.rank := by omega
    rw [L.rk_cov (c j) (c (j + 1)) (hc.2.2 j hj), ih (by omega)]

/-- Convention IIA: Elementwise `|mu(bot, s k)|` along a maximal chain or rank-selector `s`. -/
def elemMobiusAbs {α : Type} [DecidableEq α] (L : GeometricLattice α)
    (s : Nat → α) (k : Nat) : Nat :=
  (L.mu L.bot (s k)).natAbs

/-- Standard binomial coefficients `C(n, k)` for Convention III (ultra-log-concavity). -/
def binom : Nat → Nat → Nat
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 1
  | n + 1, k + 1 => binom n k + binom n (k + 1)

theorem binom_pos : ∀ (n k : Nat), k ≤ n → 1 ≤ binom n k
  | 0, 0, _ => Nat.le_refl 1
  | 0, _ + 1, hk => by omega
  | _ + 1, 0, _ => Nat.le_refl 1
  | n + 1, k + 1, hk => by
    unfold binom
    have h1 := binom_pos n k (by omega)
    omega

/-! ## Section 6: General Structural Theorems Across All Conventions -/

/-- First term of `w_k^+(L)` is always `1`, and every `w_k^+(L) ≥ 1` (`0 ≤ k ≤ rank`). -/
theorem whitney1Abs_zero {α : Type} [DecidableEq α] (L : GeometricLattice α) :
    whitney1Abs L 0 = 1 := by
  unfold whitney1Abs
  have h1 :
      natSum L.elems (fun x => if L.rk x = 0 then (L.mu L.bot x).natAbs else 0) =
      natSum L.elems (fun x => if x = L.bot then (L.mu L.bot x).natAbs else 0) := by
    apply natSum_congr
    intro x _
    by_cases hx : x = L.bot
    · subst hx; simp [L.rk_bot]
    · have hnr : L.rk x ≠ 0 := fun hr => hx ((L.eq_bot_iff_rk_zero x).mpr hr)
      simp [hx, hnr]
  rw [h1, natSum_ite_eq L.elems_nodup (L.elems_complete L.bot)]
  have hd : L.mu L.bot L.bot = 1 := IncidenceAlg.mobius_diag L.toFinPoset L.bot
  rw [hd]
  rfl

theorem whitney1Abs_pos {α : Type} [DecidableEq α] (L : GeometricLattice α)
    {k : Nat} (hk : k ≤ L.rank) : 1 ≤ whitney1Abs L k := by
  obtain ⟨x, hrkx⟩ := L.exists_elem_of_rk hk
  unfold whitney1Abs
  apply natSum_pos_of_mem (L.elems_complete x)
  rw [if_pos hrkx]
  exact natAbs_mu_ge_one L x

theorem whitney2_pos {α : Type} [DecidableEq α] (L : GeometricLattice α)
    {k : Nat} (hk : k ≤ L.rank) : 1 ≤ whitney2 L k := by
  obtain ⟨x, hrkx⟩ := L.exists_elem_of_rk hk
  unfold whitney2
  apply natSum_pos_of_mem (L.elems_complete x)
  simp [hrkx]

/-- Every geometric lattice of rank `≥ 2` has at least `2` distinct atoms, so `w_1^+(L) ≥ 2`. -/
theorem whitney1Abs_one_ge_two {α : Type} [DecidableEq α] (L : GeometricLattice α)
    (hrk : 2 ≤ L.rank) : 2 ≤ whitney1Abs L 1 := by
  have htop_ne_bot : L.top ≠ L.bot := by
    intro h
    have hr := L.rk_bot
    have htr : L.rk L.top = L.rank := rfl
    rw [h, hr] at htr
    omega
  obtain ⟨p1, hp1, _⟩ := exists_atom_le_of_ne_bot L htop_ne_bot
  have hnot_top_le_p1 : ¬ L.le L.top p1 := by
    intro hle
    have hr1 : L.rk p1 = 1 := (L.isAtom_iff_rk_one p1).mp hp1
    have hm := L.rk_mono hle
    change L.rank ≤ L.rk p1 at hm
    omega
  have hex_p2 : ∃ p2 : α, IsAtom L.toFinLattice p2 ∧ ¬ L.le p2 p1 := by
    by_cases hex : ∃ p2 : α, IsAtom L.toFinLattice p2 ∧ ¬ L.le p2 p1
    · exact hex
    · exfalso
      apply hnot_top_le_p1
      apply L.atomistic L.top p1
      intro q hq _
      by_cases hqp1 : L.le q p1
      · exact hqp1
      · exact absurd ⟨q, hq, hqp1⟩ hex
  obtain ⟨p2, hp2, hnp2p1⟩ := hex_p2
  have hp1_ne_p2 : p1 ≠ p2 := fun h => hnp2p1 (h ▸ L.le_refl p1)
  have hrp1 : L.rk p1 = 1 := (L.isAtom_iff_rk_one p1).mp hp1
  have hrp2 : L.rk p2 = 1 := (L.isAtom_iff_rk_one p2).mp hp2
  unfold whitney1Abs
  apply natSum_pair_ge_two L.elems_nodup (L.elems_complete p1) (L.elems_complete p2) hp1_ne_p2
  · rw [if_pos hrp1]; exact natAbs_mu_ge_one L p1
  · rw [if_pos hrp2]; exact natAbs_mu_ge_one L p2

/-- Partitioning `∑_{x ∈ L} mu(bot, x) = 0` (`rank ≥ 1`) by rank yields
    `∑_{k=0}^{rank} (-1)^k w_k^+(L) = 0`. -/
def rangeList : Nat → List Nat
  | 0 => []
  | m + 1 => m :: rangeList m

theorem mem_rangeList {m k : Nat} : k ∈ rangeList m ↔ k < m := by
  induction m with
  | zero => simp [rangeList]
  | succ n ih =>
    simp only [rangeList, List.mem_cons, ih]
    omega

theorem nodup_rangeList : ∀ m : Nat, (rangeList m).Nodup
  | 0 => by decide
  | n + 1 => by
    simp only [rangeList, List.nodup_cons, mem_rangeList]
    exact ⟨by omega, nodup_rangeList n⟩

theorem alternating_whitney1Abs_sum_eq_zero {α : Type} [DecidableEq α] (L : GeometricLattice α)
    (hrk : 1 ≤ L.rank) :
    listSum (rangeList (L.rank + 1)) (fun k => signPow k * (whitney1Abs L k : Int)) = 0 := by
  have hbot_ne_top : L.bot ≠ L.top := by
    intro h
    have hr0 := L.rk_bot
    have hrt : L.rk L.top = L.rank := rfl
    rw [← h, hr0] at hrt
    omega
  have htot : listSum L.elems (fun x => L.mu L.bot x) = 0 := by
    have hmz : (IncidenceAlg.mul (IncidenceAlg.mobius L.toFinPoset)
        (IncidenceAlg.zeta L.toFinPoset)).val L.bot L.top = 0 := by
      rw [IncidenceAlg.mobius_mul_zeta]
      simp [IncidenceAlg.delta, hbot_ne_top]
    rw [IncidenceAlg.mul_val_interval] at hmz
    have hsimp :
        listSum L.elems (fun x => L.mu L.bot x) =
        listSum L.toFinPoset.elems (fun x =>
          if L.toFinPoset.le L.bot x ∧ L.toFinPoset.le x L.top then
            (IncidenceAlg.mobius L.toFinPoset).val L.bot x *
              (IncidenceAlg.zeta L.toFinPoset).val x L.top
          else 0) := by
      apply listSum_congr
      intro x _
      have hbx : L.le L.bot x := L.bot_le x
      have hxt : L.le x L.top := L.le_top x
      change L.mu L.bot x =
        if L.le L.bot x ∧ L.le x L.top then
          L.mu L.bot x * (if L.le x L.top then 1 else 0)
        else 0
      simp [hbx, hxt]
    rw [hsimp, hmz]
  -- Expand `whitney1Abs L k` and swap the sums over `k` and `x`.
  have hpart :
      listSum (rangeList (L.rank + 1)) (fun k => signPow k * (whitney1Abs L k : Int)) =
      listSum L.elems (fun x => L.mu L.bot x) := by
    have step1 :
        listSum (rangeList (L.rank + 1)) (fun k => signPow k * (whitney1Abs L k : Int)) =
        listSum (rangeList (L.rank + 1)) (fun k =>
          listSum L.elems (fun x =>
            if k = L.rk x then signPow (L.rk x) * ((L.mu L.bot x).natAbs : Int) else 0)) := by
      apply listSum_congr
      intro k _
      unfold whitney1Abs
      rw [natSum_toInt, listSum_mul_left]
      apply listSum_congr
      intro x _
      by_cases hkx : L.rk x = k
      · subst hkx; simp
      · have hxk : k ≠ L.rk x := fun h => hkx h.symm
        simp [hkx, hxk]
    rw [step1, listSum_comm]
    apply listSum_congr
    intro x _
    have hx_le : L.rk x < L.rank + 1 := by
      have hm := L.rk_mono (L.le_top x)
      change L.rk x ≤ L.rank at hm
      omega
    have hx_mem : L.rk x ∈ rangeList (L.rank + 1) := mem_rangeList.mpr hx_le
    rw [listSum_ite_eq (nodup_rangeList (L.rank + 1)) hx_mem]
    rw [abs_mu_eq_signed L x]
    have hsp2 : ∀ (k : Nat) (v : Int), signPow k * (signPow k * v) = v := by
      intro k v
      induction k with
      | zero => simp [signPow]
      | succ j ih =>
        rw [signPow_succ, Int.neg_mul, Int.neg_mul, Int.mul_neg, Int.neg_neg, ih]
    exact hsp2 (L.rk x) (L.mu L.bot x)
  rw [hpart, htot]

/-- Pure sequence lemma: if `w 0 = 1`, `w 1 = a ≥ 1`, and global equality holds on `{0..n}`,
    then `w k = a ^ k` for all `k ≤ n`. -/
theorem geom_prog_of_global_eq {n a : Nat} {w : Nat → Nat}
    (hw0 : w 0 = 1) (hw1 : w 1 = a) (ha : 1 ≤ a)
    (heq : GlobalLogConcaveEq n w) :
    ∀ k : Nat, k ≤ n → w k = a ^ k := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro hkn
    match k with
    | 0 => simp [hw0]
    | 1 => simp [hw1]
    | j + 2 =>
      have hj1_eq : w (j + 1) = a ^ (j + 1) := ih (j + 1) (by omega) (by omega)
      have hj_eq : w j = a ^ j := ih j (by omega) (by omega)
      have hglob := heq (j + 1) (by omega) (by omega)
      simp only [Nat.add_sub_cancel] at hglob
      -- `w (j + 1) * w (j + 1) = w j * w (j + 2)`
      rw [hj1_eq, hj_eq] at hglob
      have hpow_pos : 0 < a ^ j := by
        clear hglob hj1_eq hj_eq ih heq hw0 hw1 hkn
        induction j with
        | zero => simp
        | succ m ihm =>
          rw [Nat.pow_succ]
          exact Nat.mul_pos ihm ha
      have hrhs : a ^ (j + 1) * a ^ (j + 1) = a ^ j * a ^ (j + 2) := by
        rw [Nat.pow_succ a (j + 1), Nat.pow_succ a j]
        calc
          (a ^ j * a) * (a ^ j * a) = a ^ j * (a * (a ^ j * a)) := by
            rw [Nat.mul_assoc]
          _ = a ^ j * ((a ^ j * a) * a) := by
            rw [Nat.mul_comm a (a ^ j * a)]
      rw [hrhs] at hglob
      exact (Nat.eq_of_mul_eq_mul_left hpow_pos hglob).symm

/-- Telescoping geometric sum identity: `(1 + a) * ∑_{k=0}^{m} (-a)^k = 1 - (-a)^{m+1}`. -/
theorem geom_alt_sum_telescope (a : Int) :
    ∀ m : Nat,
      (1 + a) * listSum (rangeList (m + 1)) (fun k => (-a) ^ k) = 1 - (-a) ^ (m + 1)
  | 0 => by
    simp only [rangeList, listSum, Int.pow_zero, Int.pow_succ]
    omega
  | m + 1 => by
    have ih := geom_alt_sum_telescope a m
    have hcons : rangeList (m + 2) = (m + 1) :: rangeList (m + 1) := rfl
    rw [hcons, listSum, Int.mul_add, ih]
    have hp : (-a) ^ (m + 2) = (-a) ^ (m + 1) * (-a) := Int.pow_succ (-a) (m + 1)
    have h1 : (1 + a) * (-a) ^ (m + 1) = (-a) ^ (m + 1) + ((-a) ^ (m + 1)) * a := by
      rw [Int.add_mul, Int.one_mul, Int.mul_comm a ((-a) ^ (m + 1))]
    have h2 : (-a) ^ (m + 1) * (-a) = - (((-a) ^ (m + 1)) * a) := Int.mul_neg _ _
    rw [h1, hp, h2]
    omega

theorem signPow_mul_pow (a k : Nat) :
    signPow k * ((a ^ k : Nat) : Int) = (- (a : Int)) ^ k := by
  unfold signPow
  induction k with
  | zero => simp
  | succ j ih =>
    rw [Int.pow_succ, Nat.pow_succ, Int.ofNat_mul, Int.pow_succ]
    calc
      ((-1 : Int) ^ j * -1) * ((a ^ j : Nat) * (a : Int))
          = ((-1 : Int) ^ j * (a ^ j : Nat)) * (-1 * (a : Int)) := by
            rw [Int.mul_assoc, Int.mul_left_comm (-1 : Int) ((a ^ j : Nat) : Int) (a : Int),
                ← Int.mul_assoc]
      _ = (- (a : Int)) ^ j * (- (a : Int)) := by
            rw [ih]
            have : (-1 : Int) * (a : Int) = - (a : Int) := by omega
            rw [this]

/-- Main Structural Theorem I.1: NO finite geometric lattice of rank `≥ 2` (including
    all Boolean lattices `B_n` with `n ≥ 2`) ever attains global log-concavity equality
    for unsigned Whitney numbers of the first kind `w_k^+(L)`. -/
theorem whitney1Abs_no_global_eq_of_rank_ge_two {α : Type} [DecidableEq α]
    (L : GeometricLattice α) (hrk : 2 ≤ L.rank) :
    ¬ GlobalLogConcaveEq L.rank (whitney1Abs L) := by
  intro hglob
  let a := whitney1Abs L 1
  have ha2 : 2 ≤ a := whitney1Abs_one_ge_two L hrk
  have hw_pow : ∀ k : Nat, k ≤ L.rank → whitney1Abs L k = a ^ k :=
    geom_prog_of_global_eq (whitney1Abs_zero L) rfl (by omega) hglob
  have halt := alternating_whitney1Abs_sum_eq_zero L (by omega)
  have hrewrite :
      listSum (rangeList (L.rank + 1)) (fun k => signPow k * (whitney1Abs L k : Int)) =
      listSum (rangeList (L.rank + 1)) (fun k => (- (a : Int)) ^ k) := by
    apply listSum_congr
    intro k hk
    have hkle : k ≤ L.rank := by
      have hklt := mem_rangeList.mp hk
      omega
    rw [hw_pow k hkle, signPow_mul_pow]
  rw [hrewrite] at halt
  have htele := geom_alt_sum_telescope (a : Int) L.rank
  rw [halt, Int.mul_zero] at htele
  -- `0 = 1 - (-a)^(L.rank + 1)`, so `((-a)^(L.rank + 1)).natAbs = 1`, i.e., `a^(L.rank + 1) = 1`.
  have hpow_eq_one : (- (a : Int)) ^ (L.rank + 1) = 1 := by omega
  have habs_pow : ∀ m : Nat, ((- (a : Int)) ^ m).natAbs = a ^ m := by
    intro m
    induction m with
    | zero => rfl
    | succ j ih =>
      rw [Int.pow_succ, Int.natAbs_mul, ih, Nat.pow_succ]
      have ha_abs : (- (a : Int)).natAbs = a := by omega
      rw [ha_abs]
  have ha_pow_one : a ^ (L.rank + 1) = 1 := by
    have h1 := habs_pow (L.rank + 1)
    rw [hpow_eq_one] at h1
    exact h1.symm
  have ha_pow_ge : 2 ≤ a ^ (L.rank + 1) := by
    have : ∀ m : Nat, a ≤ a ^ (m + 1) := by
      intro m
      induction m with
      | zero => simp
      | succ j ih =>
        rw [Nat.pow_succ]
        have : a * 1 ≤ a ^ (j + 1) * a := by
          rw [Nat.mul_comm a 1, Nat.one_mul]
          exact Nat.le_trans ih (Nat.le_mul_of_pos_right _ (by omega))
        omega
    exact Nat.le_trans ha2 (this L.rank)
  omega

/-- Main Structural Theorem I.2: Complete Classification of Global Equality for `w_k^+(L)`.
    Global log-concavity equality holds if and only if `L.rank ≤ 1` (vacuous index set). -/
theorem whitney1Abs_global_eq_iff_rank_le_one {α : Type} [DecidableEq α]
    (L : GeometricLattice α) :
    GlobalLogConcaveEq L.rank (whitney1Abs L) ↔ L.rank ≤ 1 := by
  constructor
  · intro hglob
    by_cases hrk : L.rank ≤ 1
    · exact hrk
    · exfalso
      exact whitney1Abs_no_global_eq_of_rank_ge_two L (by omega) hglob
  · intro hrk k hk1 hk2
    omega

/-- Degenerate one-way material implication: `GlobalLogConcaveEq → IsBooleanLattice` holds
    for all geometric lattices solely because `GlobalLogConcaveEq` collapses to `L.rank ≤ 1`. -/
theorem whitney1Abs_global_eq_imp_boolean {α : Type} [DecidableEq α]
    (L : GeometricLattice α)
    (hglob : GlobalLogConcaveEq L.rank (whitney1Abs L)) :
    IsBooleanLattice L.toFinLattice :=
  geom_rk_le_one_isBoolean L ((whitney1Abs_global_eq_iff_rank_le_one L).mp hglob)

/-- Pure sequence lemma for Convention II: any positive log-concave sequence starting `1, 1, ...`
    must equal `1` everywhere. -/
theorem pos_logConcave_ones_eq_one {n : Nat} {a : Nat → Nat}
    (hpos : IsStrictlyPosSeq n a) (ha0 : a 0 = 1) (ha1 : 1 ≤ n → a 1 = 1)
    (hlc : IsLogConcave n a) :
    ∀ k : Nat, k ≤ n → a k = 1 := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro hkn
    match k with
    | 0 => exact ha0
    | 1 => exact ha1 hkn
    | j + 2 =>
      have hj : a j = 1 := ih j (by omega) (by omega)
      have hj1 : a (j + 1) = 1 := ih (j + 1) (by omega) (by omega)
      have hstep := hlc (j + 1) (by omega) (by omega)
      simp only [Nat.add_sub_cancel] at hstep
      rw [hj, hj1] at hstep
      change 1 * a (j + 2) ≤ 1 * 1 at hstep
      have hge1 : 1 ≤ a (j + 2) := hpos (j + 2) hkn
      omega

/-- Pure rational sequence lemma for Convention IIB (rank-averages). -/
theorem rat_logConcave_ones_eq_den {n : Nat} {num den : Nat → Nat}
    (hdpos : ∀ k : Nat, k ≤ n → 1 ≤ den k)
    (hge : ∀ k : Nat, k ≤ n → den k ≤ num k)
    (h0 : num 0 = den 0)
    (h1 : 1 ≤ n → num 1 = den 1)
    (hlc : IsLogConcaveRat n num den) :
    ∀ k : Nat, k ≤ n → num k = den k := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro hkn
    match k with
    | 0 => exact h0
    | 1 => exact h1 hkn
    | j + 2 =>
      have hj : num j = den j := ih j (by omega) (by omega)
      have hj1 : num (j + 1) = den (j + 1) := ih (j + 1) (by omega) (by omega)
      have hstep := hlc (j + 1) (by omega) (by omega)
      simp only [Nat.add_sub_cancel] at hstep
      rw [hj, hj1] at hstep
      -- `den j * num (j + 2) * (den (j + 1) * den (j + 1)) ≤
      --  den (j + 1) * den (j + 1) * (den j * den (j + 2))`
      let c := den j * (den (j + 1) * den (j + 1))
      have hc_pos : 0 < c := by
        dsimp only [c]
        have hdj := hdpos j (by omega)
        have hdj1 := hdpos (j + 1) (by omega)
        exact Nat.mul_pos hdj (Nat.mul_pos hdj1 hdj1)
      have hlhs : den j * num (j + 2) * (den (j + 1) * den (j + 1)) = c * num (j + 2) := by
        dsimp only [c]
        rw [Nat.mul_right_comm (den j) (num (j + 2)) _, Nat.mul_comm (c) _, Nat.mul_comm]
      have hrhs : den (j + 1) * den (j + 1) * (den j * den (j + 2)) = c * den (j + 2) := by
        dsimp only [c]
        rw [← Nat.mul_assoc, Nat.mul_comm (den (j + 1) * den (j + 1)) (den j)]
      rw [hlhs, hrhs] at hstep
      have hle_den : num (j + 2) ≤ den (j + 2) := Nat.le_of_mul_le_mul_left hstep hc_pos
      have hge_den : den (j + 2) ≤ num (j + 2) := hge (j + 2) hkn
      omega

/-- On EVERY Boolean geometric lattice, elementwise `|mu(bot, s k)|` equals `(1, 1, ..., 1)`,
    hence satisfies `HasFirstTermOne`, `IsLogConcave`, AND `GlobalLogConcaveEq` for ALL ranks! -/
theorem boolean_rankSelector_props {α : Type} [DecidableEq α] (L : GeometricLattice α)
    (hbool : IsBooleanLattice L.toFinLattice) (s : Nat → α) :
    HasFirstTermOne (elemMobiusAbs L s) ∧
      IsLogConcave L.rank (elemMobiusAbs L s) ∧
      GlobalLogConcaveEq L.rank (elemMobiusAbs L s) := by
  have hall : ∀ k : Nat, elemMobiusAbs L s k = 1 :=
    fun k => boolean_natAbs_mu_eq_one L hbool (s k)
  refine ⟨hall 0, ?_, ?_⟩
  · intro k _ _
    simp [hall]
  · intro k _ _
    simp [hall]

/-- Main Structural Theorem II.1: On EVERY non-Boolean geometric lattice `L`,
    elementwise `|mu(bot, s k)|` FAILS log-concavity along EVERY rank-selector `s`
    (in particular, along EVERY maximal chain of `L`)! -/
theorem nonBoolean_rankSelector_not_logConcave {α : Type} [DecidableEq α]
    (L : GeometricLattice α) (hnot : ¬ IsBooleanLattice L.toFinLattice)
    {s : Nat → α} (hs : IsRankSelector L s) :
    ¬ IsLogConcave L.rank (elemMobiusAbs L s) := by
  intro hlc
  have hrk2 : 2 ≤ L.rank := by
    by_cases h1 : L.rank ≤ 1
    · exact absurd (geom_rk_le_one_isBoolean L h1) hnot
    · omega
  have hs0 : s 0 = L.bot := (L.eq_bot_iff_rk_zero (s 0)).mpr (hs 0 (by omega))
  have hs_top : s L.rank = L.top := by
    have hrk_s : L.rk (s L.rank) = L.rank := hs L.rank (Nat.le_refl _)
    by_cases heq : s L.rank = L.top
    · exact heq
    · exfalso
      have hlt : L.rk (s L.rank) < L.rank := L.rk_strict_mono ⟨L.le_top (s L.rank), heq⟩
      omega
  have ha0 : elemMobiusAbs L s 0 = 1 := by
    unfold elemMobiusAbs
    have hd : L.mu L.bot L.bot = 1 := IncidenceAlg.mobius_diag L.toFinPoset L.bot
    rw [hs0, hd]
    rfl
  have ha1 : 1 ≤ L.rank → elemMobiusAbs L s 1 = 1 := by
    intro h1
    unfold elemMobiusAbs
    have hatom : IsAtom L.toFinLattice (s 1) := (L.isAtom_iff_rk_one (s 1)).mpr (hs 1 h1)
    have hmu : L.mu L.bot (s 1) = -1 := mobius_of_covers L.toFinPoset hatom
    rw [hmu]
    rfl
  have hpos : IsStrictlyPosSeq L.rank (elemMobiusAbs L s) :=
    fun k _ => natAbs_mu_ge_one L (s k)
  have htop_one : elemMobiusAbs L s L.rank = 1 :=
    pos_logConcave_ones_eq_one hpos ha0 ha1 hlc L.rank (Nat.le_refl _)
  unfold elemMobiusAbs at htop_one
  rw [hs_top] at htop_one
  exact hnot ((isBoolean_iff_natAbs_mu_top_eq_one L).mpr htop_one)

/-- Exact equivalence for Convention IIA: along ANY rank-selector `s` (or maximal chain),
    `elemMobiusAbs L s` is log-concave if and only if `L` is a Boolean lattice! -/
theorem rankSelector_logConcave_iff_boolean {α : Type} [DecidableEq α]
    (L : GeometricLattice α) {s : Nat → α} (hs : IsRankSelector L s) :
    IsLogConcave L.rank (elemMobiusAbs L s) ↔ IsBooleanLattice L.toFinLattice := by
  constructor
  · intro hlc
    by_cases hb : IsBooleanLattice L.toFinLattice
    · exact hb
    · exact absurd hlc (nonBoolean_rankSelector_not_logConcave L hb hs)
  · intro hb
    exact (boolean_rankSelector_props L hb s).2.1

/-- Main Structural Theorem II.2: On EVERY non-Boolean geometric lattice `L`,
    the rank-averaged sequence `w_k^+(L) / W_k(L)` ALSO fails log-concavity! -/
theorem nonBoolean_avg_not_logConcave {α : Type} [DecidableEq α]
    (L : GeometricLattice α) (hnot : ¬ IsBooleanLattice L.toFinLattice) :
    ¬ IsLogConcaveRat L.rank (whitney1Abs L) (whitney2 L) := by
  intro hlc
  have hrk2 : 2 ≤ L.rank := by
    by_cases h1 : L.rank ≤ 1
    · exact absurd (geom_rk_le_one_isBoolean L h1) hnot
    · omega
  have hw2_zero : whitney2 L 0 = 1 := by
    unfold whitney2
    have h1 :
        natSum L.elems (fun x => if L.rk x = 0 then 1 else 0) =
        natSum L.elems (fun x => if x = L.bot then 1 else 0) := by
      apply natSum_congr
      intro x _
      by_cases hx : x = L.bot
      · subst hx; simp [L.rk_bot]
      · have hnr : L.rk x ≠ 0 := fun hr => hx ((L.eq_bot_iff_rk_zero x).mpr hr)
        simp [hx, hnr]
    rw [h1, natSum_ite_eq L.elems_nodup (L.elems_complete L.bot)]
  have hw1_eq_w2_at_one : 1 ≤ L.rank → whitney1Abs L 1 = whitney2 L 1 := by
    intro _
    unfold whitney1Abs whitney2
    apply natSum_congr
    intro x _
    by_cases hrx : L.rk x = 1
    · rw [if_pos hrx, if_pos hrx]
      have hatom : IsAtom L.toFinLattice x := (L.isAtom_iff_rk_one x).mpr hrx
      have hmu : L.mu L.bot x = -1 := mobius_of_covers L.toFinPoset hatom
      rw [hmu]
      rfl
    · simp [hrx]
  have hdpos : ∀ k : Nat, k ≤ L.rank → 1 ≤ whitney2 L k := fun _ hk => whitney2_pos L hk
  have hge : ∀ k : Nat, k ≤ L.rank → whitney2 L k ≤ whitney1Abs L k := by
    intro k _
    unfold whitney2 whitney1Abs
    apply natSum_le_of_le
    intro x _
    by_cases hrx : L.rk x = k
    · rw [if_pos hrx, if_pos hrx]
      exact natAbs_mu_ge_one L x
    · simp [hrx]
  have h0 : whitney1Abs L 0 = whitney2 L 0 := by rw [whitney1Abs_zero, hw2_zero]
  have htop_eq := rat_logConcave_ones_eq_den hdpos hge h0 hw1_eq_w2_at_one hlc L.rank (Nat.le_refl _)
  -- At `k = L.rank`, `top` is the unique element of rank `L.rank`.
  have huniq_top : ∀ x : α, L.rk x = L.rank ↔ x = L.top := by
    intro x
    constructor
    · intro hrx
      by_cases hx : x = L.top
      · exact hx
      · exfalso
        have hlt : L.rk x < L.rank := L.rk_strict_mono ⟨L.le_top x, hx⟩
        omega
    · intro hx; subst hx; rfl
  have hw1_top : whitney1Abs L L.rank = (L.mu L.bot L.top).natAbs := by
    unfold whitney1Abs
    have h1 :
        natSum L.elems (fun x => if L.rk x = L.rank then (L.mu L.bot x).natAbs else 0) =
        natSum L.elems (fun x => if x = L.top then (L.mu L.bot x).natAbs else 0) := by
      apply natSum_congr
      intro x _
      by_cases hx : x = L.top
      · subst hx; simp [huniq_top]
      · have hnr : L.rk x ≠ L.rank := fun hr => hx ((huniq_top x).mp hr)
        simp [hx, hnr]
    rw [h1, natSum_ite_eq L.elems_nodup (L.elems_complete L.top)]
  have hw2_top : whitney2 L L.rank = 1 := by
    unfold whitney2
    have h1 :
        natSum L.elems (fun x => if L.rk x = L.rank then 1 else 0) =
        natSum L.elems (fun x => if x = L.top then 1 else 0) := by
      apply natSum_congr
      intro x _
      by_cases hx : x = L.top
      · subst hx; simp [huniq_top]
      · have hnr : L.rk x ≠ L.rank := fun hr => hx ((huniq_top x).mp hr)
        simp [hx, hnr]
    rw [h1, natSum_ite_eq L.elems_nodup (L.elems_complete L.top)]
  rw [hw1_top, hw2_top] at htop_eq
  exact hnot ((isBoolean_iff_natAbs_mu_top_eq_one L).mpr htop_eq)

/-! ## Section 7: Concrete Geometric Lattice Models (`B_2`, `M_3`, `U_{3,4}`) -/

/-! ### Model 1: Rank-2 Boolean Geometric Lattice `B_2` on `Fin 4` -/

def b2Elems : List (Fin 4) := [0, 1, 2, 3]

def b2Le (x y : Fin 4) : Prop := (x.val &&& y.val) = x.val

instance : DecidableRel b2Le := fun _ _ => inferInstanceAs (Decidable (_ = _))

def b2FromMask : Nat → Fin 4
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 3

def b2Inf (x y : Fin 4) : Fin 4 := b2FromMask (x.val &&& y.val)

def b2Sup (x y : Fin 4) : Fin 4 := b2FromMask (x.val ||| y.val)

def b2Comp : Fin 4 → Fin 4
  | ⟨0, _⟩ => 3
  | ⟨1, _⟩ => 2
  | ⟨2, _⟩ => 1
  | ⟨3, _⟩ => 0

def b2Rk : Fin 4 → Nat
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 1
  | ⟨3, _⟩ => 2

def B2FinLattice : FinLattice (Fin 4) where
  elems := b2Elems
  elems_nodup := by decide
  elems_complete := by intro x; revert x; decide
  le := b2Le
  decLe := inferInstance
  le_refl := by decide
  le_antisymm := by decide
  le_trans := by decide
  bot := 0
  top := 3
  inf := b2Inf
  sup := b2Sup
  bot_le := by decide
  le_top := by decide
  inf_le_left := by decide
  inf_le_right := by decide
  le_inf := by decide
  le_sup_left := by decide
  le_sup_right := by decide
  sup_le := by decide

def B2GeomLattice : GeometricLattice (Fin 4) where
  toFinLattice := B2FinLattice
  atomistic := by decide
  rk := b2Rk
  rk_bot := rfl
  rk_cov := by decide
  rk_submod := by decide

theorem B2_isBoolean : IsBooleanLattice B2GeomLattice.toFinLattice := by
  constructor
  · decide
  · intro x
    refine ⟨b2Comp x, ?_⟩
    revert x
    decide

theorem B2_whitney1_vals :
    whitney1Abs B2GeomLattice 0 = 1 ∧
      whitney1Abs B2GeomLattice 1 = 2 ∧
      whitney1Abs B2GeomLattice 2 = 1 := by
  decide

theorem B2_whitney1_logConcave :
    IsLogConcave B2GeomLattice.rank (whitney1Abs B2GeomLattice) := by
  intro k hk1 hk2
  have hr : B2GeomLattice.rank = 2 := rfl
  have hk_eq : k = 1 := by omega
  subst hk_eq
  decide

theorem B2_whitney1_not_globalEq :
    ¬ GlobalLogConcaveEq B2GeomLattice.rank (whitney1Abs B2GeomLattice) := by
  intro hglob
  have h1 := hglob 1 (Nat.le_refl 1) (Nat.le_refl 2)
  revert h1
  decide

/-! ### Model 2: Rank-2 Non-Boolean Diamond Geometric Lattice `M_3` on `Fin 5` -/

def m3Elems : List (Fin 5) := [0, 1, 2, 3, 4]

def m3Le (x y : Fin 5) : Prop := x = 0 ∨ y = 4 ∨ x = y

instance : DecidableRel m3Le := fun _ _ => instDecidableOr

def m3Inf (x y : Fin 5) : Fin 5 :=
  if x = y then x else if x = 4 then y else if y = 4 then x else 0

def m3Sup (x y : Fin 5) : Fin 5 :=
  if x = y then x else if x = 0 then y else if y = 0 then x else 4

def m3Rk : Fin 5 → Nat
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 1
  | ⟨3, _⟩ => 1
  | ⟨4, _⟩ => 2

def M3FinLattice : FinLattice (Fin 5) where
  elems := m3Elems
  elems_nodup := by decide
  elems_complete := by intro x; revert x; decide
  le := m3Le
  decLe := inferInstance
  le_refl := by decide
  le_antisymm := by decide
  le_trans := by decide
  bot := 0
  top := 4
  inf := m3Inf
  sup := m3Sup
  bot_le := by decide
  le_top := by decide
  inf_le_left := by decide
  inf_le_right := by decide
  le_inf := by decide
  le_sup_left := by decide
  le_sup_right := by decide
  sup_le := by decide

def M3GeomLattice : GeometricLattice (Fin 5) where
  toFinLattice := M3FinLattice
  atomistic := by decide
  rk := m3Rk
  rk_bot := rfl
  rk_cov := by decide
  rk_submod := by decide

theorem M3_not_isBoolean : ¬ IsBooleanLattice M3GeomLattice.toFinLattice := by
  intro hb
  have hd := hb.1 1 2 3
  revert hd
  decide

theorem M3_mobius_vals :
    M3GeomLattice.mu 0 0 = 1 ∧
      M3GeomLattice.mu 0 1 = -1 ∧
      M3GeomLattice.mu 0 2 = -1 ∧
      M3GeomLattice.mu 0 3 = -1 ∧
      M3GeomLattice.mu 0 4 = 2 := by
  decide

theorem M3_whitney1_vals :
    whitney1Abs M3GeomLattice 0 = 1 ∧
      whitney1Abs M3GeomLattice 1 = 3 ∧
      whitney1Abs M3GeomLattice 2 = 2 := by
  decide

theorem M3_whitney1_logConcave :
    IsLogConcave M3GeomLattice.rank (whitney1Abs M3GeomLattice) := by
  intro k hk1 hk2
  have hr : M3GeomLattice.rank = 2 := rfl
  have hk_eq : k = 1 := by omega
  subst hk_eq
  decide

def m3Chain : Nat → Fin 5
  | 0 => 0
  | 1 => 1
  | _ + 2 => 4

theorem m3Chain_isMaximalChain : IsMaximalChain M3GeomLattice m3Chain := by
  refine ⟨rfl, rfl, ?_⟩
  intro k hk
  have hr : M3GeomLattice.rank = 2 := rfl
  match k with
  | 0 => decide
  | 1 => decide
  | _ + 2 => omega

theorem m3Chain_not_logConcave :
    ¬ IsLogConcave M3GeomLattice.rank (elemMobiusAbs M3GeomLattice m3Chain) := by
  intro hlc
  have h1 := hlc 1 (Nat.le_refl 1) (Nat.le_refl 2)
  revert h1
  decide

/-! ### Model 3: Rank-3 Uniform Geometric Lattice `U_{3,4}` on `Fin 12` -/

def u34Mask : Fin 12 → Nat
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 2
  | ⟨3, _⟩ => 4
  | ⟨4, _⟩ => 8
  | ⟨5, _⟩ => 3
  | ⟨6, _⟩ => 5
  | ⟨7, _⟩ => 6
  | ⟨8, _⟩ => 9
  | ⟨9, _⟩ => 10
  | ⟨10, _⟩ => 12
  | ⟨11, _⟩ => 15

def u34FromMask : Nat → Fin 12
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 4 => 3
  | 8 => 4
  | 3 => 5
  | 5 => 6
  | 6 => 7
  | 9 => 8
  | 10 => 9
  | 12 => 10
  | _ => 11

def u34Rk : Fin 12 → Nat
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ | ⟨4, _⟩ => 1
  | ⟨5, _⟩ | ⟨6, _⟩ | ⟨7, _⟩ | ⟨8, _⟩ | ⟨9, _⟩ | ⟨10, _⟩ => 2
  | ⟨11, _⟩ => 3

def u34Elems : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

def u34Le (x y : Fin 12) : Prop := (u34Mask x &&& u34Mask y) = u34Mask x

instance : DecidableRel u34Le := fun _ _ => inferInstanceAs (Decidable (_ = _))

def u34Inf (x y : Fin 12) : Fin 12 := u34FromMask (u34Mask x &&& u34Mask y)

def u34Sup (x y : Fin 12) : Fin 12 := u34FromMask (u34Mask x ||| u34Mask y)

def U34FinLattice : FinLattice (Fin 12) where
  elems := u34Elems
  elems_nodup := by decide
  elems_complete := by intro x; revert x; decide
  le := u34Le
  decLe := inferInstance
  le_refl := by decide
  le_antisymm := by decide
  le_trans := by decide
  bot := 0
  top := 11
  inf := u34Inf
  sup := u34Sup
  bot_le := by decide
  le_top := by decide
  inf_le_left := by decide
  inf_le_right := by decide
  le_inf := by decide
  le_sup_left := by decide
  le_sup_right := by decide
  sup_le := by decide

theorem u34_atoms_iff (p : Fin 12) :
    IsAtom U34FinLattice p ↔ (p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 4) := by
  revert p
  decide

def U34GeomLattice : GeometricLattice (Fin 12) where
  toFinLattice := U34FinLattice
  atomistic := by
    intro x y h
    have h4 : (u34Le 1 x → u34Le 1 y) ∧ (u34Le 2 x → u34Le 2 y) ∧
        (u34Le 3 x → u34Le 3 y) ∧ (u34Le 4 x → u34Le 4 y) :=
      ⟨h 1 ((u34_atoms_iff 1).mpr (Or.inl rfl)),
       h 2 ((u34_atoms_iff 2).mpr (Or.inr (Or.inl rfl))),
       h 3 ((u34_atoms_iff 3).mpr (Or.inr (Or.inr (Or.inl rfl)))),
       h 4 ((u34_atoms_iff 4).mpr (Or.inr (Or.inr (Or.inr rfl))))⟩
    revert x y h4
    decide
  rk := u34Rk
  rk_bot := rfl
  rk_cov := by decide
  rk_submod := by decide

theorem U34_whitney1_vals :
    whitney1Abs U34GeomLattice 0 = 1 ∧
      whitney1Abs U34GeomLattice 1 = 4 ∧
      whitney1Abs U34GeomLattice 2 = 6 ∧
      whitney1Abs U34GeomLattice 3 = 3 := by
  decide

theorem U34_not_ultraLogConcave :
    ¬ IsLogConcaveRat U34GeomLattice.rank
        (whitney1Abs U34GeomLattice) (binom U34GeomLattice.rank) := by
  intro hulc
  have h1 := hulc 1 (Nat.le_refl 1) (by decide)
  revert h1
  decide

/-! ## Section 8: Top-Level Formal Disproofs of Conjecture 00000008539 & Non-Vacuity Witnesses -/

/-- Formal statement of Conjecture 00000008539 under Convention I (unsigned Whitney numbers
    of the first kind `w_k^+(L)`, with standard equality-case characterization:
    `GlobalLogConcaveEq ↔ IsBooleanLattice`). -/
def Conjecture_Convention_I_WhitneyIff : Prop :=
  ∀ (α : Type) [DecidableEq α] (L : GeometricLattice α),
    HasFirstTermOne (whitney1Abs L) ∧
      IsLogConcave L.rank (whitney1Abs L) ∧
      (GlobalLogConcaveEq L.rank (whitney1Abs L) ↔ IsBooleanLattice L.toFinLattice)

/-- DISPROOF under Convention I: `B_2` is a Boolean geometric lattice, yet
    `w^+(B_2) = (1, 2, 1)` fails global log-concavity equality (`2^2 = 4 ≠ 1`). -/
theorem disproof_convention_I_whitney_iff : ¬ Conjecture_Convention_I_WhitneyIff := by
  intro hconj
  have hb2 := (hconj (Fin 4) B2GeomLattice).2.2
  exact B2_whitney1_not_globalEq (hb2.mpr B2_isBoolean)

/-- Formal statement of Conjecture 00000008539 under Convention IIA (elementwise `|mu(0, c_k)|`
    along maximal chains `c` of `L`). -/
def Conjecture_Convention_IIA_MaximalChain : Prop :=
  ∀ (α : Type) [DecidableEq α] (L : GeometricLattice α) (c : Nat → α),
    IsMaximalChain L c →
      HasFirstTermOne (elemMobiusAbs L c) ∧
        IsLogConcave L.rank (elemMobiusAbs L c) ∧
        (GlobalLogConcaveEq L.rank (elemMobiusAbs L c) ↔ IsBooleanLattice L.toFinLattice)

/-- DISPROOF under Convention IIA: `M_3` is a geometric lattice with maximal chain
    `0 ⋖ 1 ⋖ 4`, yet `(|mu(0,0)|, |mu(0,1)|, |mu(0,4)|) = (1, 1, 2)` fails log-concavity. -/
theorem disproof_convention_IIA_chain : ¬ Conjecture_Convention_IIA_MaximalChain := by
  intro hconj
  have hm3 := hconj (Fin 5) M3GeomLattice m3Chain m3Chain_isMaximalChain
  exact m3Chain_not_logConcave hm3.2.1

/-- Formal statement of Conjecture 00000008539 under Convention IIB (rank-averaged `|mu|`:
    `w_k^+(L) / W_k(L)`). -/
def Conjecture_Convention_IIB_RankAverage : Prop :=
  ∀ (α : Type) [DecidableEq α] (L : GeometricLattice α),
    HasFirstTermOneRat (whitney1Abs L) (whitney2 L) ∧
      IsLogConcaveRat L.rank (whitney1Abs L) (whitney2 L) ∧
      (GlobalLogConcaveEqRat L.rank (whitney1Abs L) (whitney2 L) ↔
        IsBooleanLattice L.toFinLattice)

/-- DISPROOF under Convention IIB: `M_3` (and indeed every non-Boolean geometric lattice)
    fails rank-averaged log-concavity. -/
theorem disproof_convention_IIB_avg : ¬ Conjecture_Convention_IIB_RankAverage := by
  intro hconj
  exact nonBoolean_avg_not_logConcave M3GeomLattice M3_not_isBoolean
    (hconj (Fin 5) M3GeomLattice).2.1

/-- Formal statement of Conjecture 00000008539 under Convention III (binomial-normalized
    Whitney numbers `w_k^+(L) / C(rank, k)`, i.e., ultra-log-concavity of `w_k^+(L)`). -/
def Conjecture_Convention_III_UltraLogConcave : Prop :=
  ∀ (α : Type) [DecidableEq α] (L : GeometricLattice α),
    HasFirstTermOneRat (whitney1Abs L) (binom L.rank) ∧
      IsLogConcaveRat L.rank (whitney1Abs L) (binom L.rank) ∧
      (GlobalLogConcaveEqRat L.rank (whitney1Abs L) (binom L.rank) ↔
        IsBooleanLattice L.toFinLattice)

/-- DISPROOF under Convention III: `U_{3,4}` fails ultra-log-concavity at `k = 1`
    (`(4/3)^2 = 16/9 < 2 = 1 * 2`). -/
theorem disproof_convention_III_ultra : ¬ Conjecture_Convention_III_UltraLogConcave := by
  intro hconj
  exact U34_not_ultraLogConcave (hconj (Fin 12) U34GeomLattice).2.1

/-- Positive Non-Vacuity Witness Bundle:
    Explicitly verifies that our definitions of `GeometricLattice`, `IsBooleanLattice`,
    `¬ IsBooleanLattice`, `IsMobius`, `IsLogConcave`, and `GlobalLogConcaveEq` are all
    simultaneously inhabited and non-vacuous at rank `≥ 2`. -/
theorem positive_non_vacuity_witnesses :
    -- 1. Rank-2 Boolean geometric lattice witness (`B_2`):
    (B2GeomLattice.rank = 2 ∧
      IsBooleanLattice B2GeomLattice.toFinLattice ∧
      IncidenceAlg.IsMobius B2GeomLattice.toFinPoset
        (IncidenceAlg.mobius B2GeomLattice.toFinPoset) ∧
      HasFirstTermOne (whitney1Abs B2GeomLattice) ∧
      IsLogConcave B2GeomLattice.rank (whitney1Abs B2GeomLattice)) ∧
    -- 2. Non-vacuous rank-2 witness for `GlobalLogConcaveEq` (elementwise on `B_2`):
    (∃ s : Nat → Fin 4,
      IsRankSelector B2GeomLattice s ∧
      HasFirstTermOne (elemMobiusAbs B2GeomLattice s) ∧
      IsLogConcave B2GeomLattice.rank (elemMobiusAbs B2GeomLattice s) ∧
      GlobalLogConcaveEq B2GeomLattice.rank (elemMobiusAbs B2GeomLattice s)) ∧
    -- 3. Rank-2 non-Boolean geometric lattice witness (`M_3`) with `|mu(0, 1)| = 2 > 1`:
    (M3GeomLattice.rank = 2 ∧
      ¬ IsBooleanLattice M3GeomLattice.toFinLattice ∧
      (M3GeomLattice.mu 0 4).natAbs = 2 ∧
      HasFirstTermOne (whitney1Abs M3GeomLattice) ∧
      IsLogConcave M3GeomLattice.rank (whitney1Abs M3GeomLattice)) ∧
    -- 4. Rank-3 non-Boolean geometric lattice witness (`U_{3,4}`):
    (U34GeomLattice.rank = 3 ∧
      ¬ IsBooleanLattice U34GeomLattice.toFinLattice ∧
      whitney1Abs U34GeomLattice 3 = 3) := by
  refine ⟨⟨rfl, B2_isBoolean, IncidenceAlg.mobius_is_mobius _,
           whitney1Abs_zero B2GeomLattice, B2_whitney1_logConcave⟩,
          ⟨fun k => match k with | 0 => 0 | 1 => 1 | _ + 2 => 3, ?_⟩,
          ⟨rfl, M3_not_isBoolean, by decide,
           whitney1Abs_zero M3GeomLattice, M3_whitney1_logConcave⟩,
          ⟨rfl, ?_, U34_whitney1_vals.2.2.2⟩⟩
  · refine ⟨?_, boolean_rankSelector_props B2GeomLattice B2_isBoolean _⟩
    intro k hk
    have hr : B2GeomLattice.rank = 2 := rfl
    match k with
    | 0 => rfl
    | 1 => rfl
    | 2 => rfl
    | _ + 3 => omega
  · intro hb
    have h1 := (isBoolean_iff_natAbs_mu_top_eq_one U34GeomLattice).mp hb
    revert h1
    decide

end Conjecture00000008539

/-! ## Section 9: Axiom Footprint Verification -/

#print axioms Conjecture00000008539.IncidenceAlg.mobius_is_mobius
#print axioms Conjecture00000008539.IncidenceAlg.mobius_unique
#print axioms Conjecture00000008539.weisner_thm
#print axioms Conjecture00000008539.rota_sign_thm
#print axioms Conjecture00000008539.isBoolean_iff_natAbs_mu_top_eq_one
#print axioms Conjecture00000008539.whitney1Abs_no_global_eq_of_rank_ge_two
#print axioms Conjecture00000008539.whitney1Abs_global_eq_iff_rank_le_one
#print axioms Conjecture00000008539.whitney1Abs_global_eq_imp_boolean
#print axioms Conjecture00000008539.nonBoolean_rankSelector_not_logConcave
#print axioms Conjecture00000008539.rankSelector_logConcave_iff_boolean
#print axioms Conjecture00000008539.nonBoolean_avg_not_logConcave
#print axioms Conjecture00000008539.disproof_convention_I_whitney_iff
#print axioms Conjecture00000008539.disproof_convention_IIA_chain
#print axioms Conjecture00000008539.disproof_convention_IIB_avg
#print axioms Conjecture00000008539.disproof_convention_III_ultra
#print axioms Conjecture00000008539.positive_non_vacuity_witnesses
