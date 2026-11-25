/-
  OrbitSperner/Foundations.lean
  Core Lean 4.19.0 formalization of posets, finite-order automorphisms,
  pigeonhole principle on Fin n, symmetric group Perm n, orbit antichain theorem,
  and quotient poset structure.
-/

namespace OrbitSperner

/-- A partial order (poset) on a type `α`. -/
structure Poset (α : Type) where
  le : α → α → Prop
  le_refl : ∀ x, le x x
  le_antisymm : ∀ {x y}, le x y → le y x → x = y
  le_trans : ∀ {x y z}, le x y → le y z → le x z

/-- Strict order induced by a poset. -/
def Poset.lt {α : Type} (P : Poset α) (x y : α) : Prop :=
  P.le x y ∧ x ≠ y

/-- Two elements are incomparable in `P` if neither `x ≤ y` nor `y ≤ x`. -/
def Poset.Incomp {α : Type} (P : Poset α) (x y : α) : Prop :=
  ¬ P.le x y ∧ ¬ P.le y x

/-- A predicate `S : α → Prop` is an antichain in `P` if comparable elements in `S` are equal. -/
def Poset.IsAntichainPred {α : Type} (P : Poset α) (S : α → Prop) : Prop :=
  ∀ ⦃x y⦄, S x → S y → P.le x y → x = y

/-- Function iteration `g^[k] x`. -/
def iterFun {α : Type} (g : α → α) : Nat → α → α
  | 0, x => x
  | k + 1, x => g (iterFun g k x)

theorem iterFun_succ_right {α : Type} (g : α → α) (k : Nat) (x : α) :
    iterFun g (k + 1) x = iterFun g k (g x) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    have h1 : iterFun g (k + 1 + 1) x = g (iterFun g (k + 1) x) := rfl
    have h2 : iterFun g (k + 1) (g x) = g (iterFun g k (g x)) := rfl
    rw [h1, ih x, h2]

theorem iterFun_add {α : Type} (g : α → α) (a b : Nat) (x : α) :
    iterFun g (a + b) x = iterFun g a (iterFun g b x) := by
  induction a with
  | zero =>
    have h0 : 0 + b = b := Nat.zero_add b
    rw [h0]
    rfl
  | succ a ih =>
    have h : a + 1 + b = (a + b) + 1 := by omega
    rw [h]
    simp only [iterFun, ih]

/-- If `g` is order-preserving and `x ≤ g x`, then `g x ≤ g^[k+1] x` for all `k`. -/
theorem le_iterFun_of_le {α : Type} (P : Poset α) (g : α → α)
    (hg : ∀ ⦃u v⦄, P.le u v → P.le (g u) (g v))
    {x : α} (hx : P.le x (g x)) :
    ∀ k : Nat, P.le (g x) (iterFun g (k + 1) x)
  | 0 => P.le_refl (g x)
  | k + 1 => by
    have ih := le_iterFun_of_le P g hg hx k
    have step : P.le (iterFun g (k + 1) x) (iterFun g (k + 2) x) := by
      clear ih
      induction k with
      | zero => exact hg hx
      | succ m ihm => exact hg ihm
    exact P.le_trans ih step

/-- **Harper-Stanley Orbit-Antichain Lemma**:
    In any poset `P`, if `g` is order-preserving and has positive period `m > 0` at `x`
    (`g^[m] x = x`), then `x` and `g x` cannot be strictly comparable: `x ≤ g x → x = g x`
    and `g x ≤ x → x = g x`. -/
theorem eq_of_le_of_finite_period {α : Type} (P : Poset α) (g : α → α)
    (hg : ∀ ⦃u v⦄, P.le u v → P.le (g u) (g v))
    {x : α} {m : Nat} (hm : 0 < m) (hper : iterFun g m x = x)
    (hle : P.le x (g x)) : x = g x := by
  cases m with
  | zero => omega
  | succ k =>
    have hback : P.le (g x) (iterFun g (k + 1) x) := le_iterFun_of_le P g hg hle k
    rw [hper] at hback
    exact P.le_antisymm hle hback

theorem eq_of_ge_of_finite_period {α : Type} (P : Poset α) (g : α → α)
    (hg : ∀ ⦃u v⦄, P.le u v → P.le (g u) (g v))
    {x : α} {m : Nat} (hm : 0 < m) (hper : iterFun g m x = x)
    (hge : P.le (g x) x) : x = g x := by
  let Pdual : Poset α := {
    le := fun u v => P.le v u
    le_refl := P.le_refl
    le_antisymm := fun h1 h2 => P.le_antisymm h2 h1
    le_trans := fun h1 h2 => P.le_trans h2 h1
  }
  exact eq_of_le_of_finite_period Pdual g (fun _ _ h => hg h) hm hper hge

/-! ### Constructive Pigeonhole Principle on `Fin n` -/

/-- Order-preserving embedding `Fin m → Fin (m + 1)` that skips index `b`. -/
def skipIdx {m : Nat} (b : Fin (m + 1)) (i : Fin m) : Fin (m + 1) :=
  if i.val < b.val then ⟨i.val, by omega⟩ else ⟨i.val + 1, by omega⟩

theorem skipIdx_ne {m : Nat} (b : Fin (m + 1)) (i : Fin m) : skipIdx b i ≠ b := by
  unfold skipIdx
  split <;> intro h <;> have hv := congrArg Fin.val h <;> dsimp at hv <;> omega

theorem skipIdx_injective {m : Nat} (b : Fin (m + 1)) :
    ∀ ⦃i j : Fin m⦄, skipIdx b i = skipIdx b j → i = j := by
  intro i j h
  have hv := congrArg Fin.val h
  unfold skipIdx at hv
  by_cases hi : i.val < b.val <;> by_cases hj : j.val < b.val <;>
    simp [hi, hj] at hv <;> exact Fin.ext (by omega)

/-- Partial inverse of `skipIdx b` for elements distinct from `b`. -/
def unskipIdx {m : Nat} (b : Fin (m + 1)) (k : Fin (m + 1)) (hk : k ≠ b) : Fin m :=
  if hlt : k.val < b.val then
    ⟨k.val, by omega⟩
  else
    have _hgt : b.val < k.val := by
      have hne : k.val ≠ b.val := fun heq => hk (Fin.ext heq)
      omega
    ⟨k.val - 1, by omega⟩

theorem skipIdx_unskipIdx {m : Nat} (b k : Fin (m + 1)) (hk : k ≠ b) :
    skipIdx b (unskipIdx b k hk) = k := by
  have hne : k.val ≠ b.val := fun heq => hk (Fin.ext heq)
  by_cases hlt : k.val < b.val
  · unfold unskipIdx skipIdx
    simp [hlt]
  · have hgt : b.val < k.val := by omega
    have hnot : ¬ (k.val - 1 < b.val) := by omega
    unfold unskipIdx
    simp [hlt]
    unfold skipIdx
    simp [hnot]
    exact Fin.ext (by dsimp; omega)

theorem unskipIdx_injective {m : Nat} (b : Fin (m + 1))
    {k₁ k₂ : Fin (m + 1)} (h₁ : k₁ ≠ b) (h₂ : k₂ ≠ b)
    (heq : unskipIdx b k₁ h₁ = unskipIdx b k₂ h₂) : k₁ = k₂ := by
  have h := congrArg (skipIdx b) heq
  rw [skipIdx_unskipIdx, skipIdx_unskipIdx] at h
  exact h

/-- **Pigeonhole Principle on `Fin`**: No function `Fin (n + 1) → Fin n` is injective. -/
theorem not_injective_fin_succ :
    ∀ (n : Nat) (f : Fin (n + 1) → Fin n), ¬ (∀ i j, f i = f j → i = j)
  | 0, f, _ => Fin.elim0 (f ⟨0, by omega⟩)
  | n + 1, f, hinj => by
    let top : Fin (n + 2) := Fin.last (n + 1)
    let b : Fin (n + 1) := f top
    have hne : ∀ i : Fin (n + 1), f i.castSucc ≠ b := by
      intro i heq
      have h := hinj i.castSucc top heq
      have hv : (i.castSucc).val = top.val := congrArg Fin.val h
      have hi_lt : i.val < n + 1 := i.isLt
      have hcs : (i.castSucc).val = i.val := rfl
      have htop : top.val = n + 1 := rfl
      omega
    let f' : Fin (n + 1) → Fin n := fun i => unskipIdx b (f i.castSucc) (hne i)
    have hinj' : ∀ i j : Fin (n + 1), f' i = f' j → i = j := by
      intro i j heq
      have h1 : f i.castSucc = f j.castSucc := unskipIdx_injective b (hne i) (hne j) heq
      have h2 : i.castSucc = j.castSucc := hinj i.castSucc j.castSucc h1
      have hv : (i.castSucc).val = (j.castSucc).val := congrArg Fin.val h2
      exact Fin.ext hv
    exact not_injective_fin_succ n f' hinj'

/-- Constructive collision finder on `Fin m → α` when injectivity fails (for `DecidableEq α`). -/
theorem exists_ne_map_eq_of_not_injective {m : Nat} {α : Type} [DecidableEq α]
    (f : Fin m → α) (hnot : ¬ (∀ i j, f i = f j → i = j)) :
    ∃ i j : Fin m, i.val < j.val ∧ f i = f j := by
  induction m with
  | zero =>
    exfalso
    apply hnot
    intro i
    exact Fin.elim0 i
  | succ m ih =>
    let last : Fin (m + 1) := Fin.last m
    have hdec : (∃ i : Fin m, f i.castSucc = f last) ∨ (∀ i : Fin m, f i.castSucc ≠ f last) := by
      clear hnot ih
      suffices ∀ k (_hk : k ≤ m),
          (∃ i : Fin m, i.val < k ∧ f i.castSucc = f last) ∨
          (∀ i : Fin m, i.val < k → f i.castSucc ≠ f last) by
        cases this m (Nat.le_refl m) with
        | inl h =>
          rcases h with ⟨i, _, hi⟩
          exact Or.inl ⟨i, hi⟩
        | inr h =>
          exact Or.inr (fun i => h i i.isLt)
      intro k hk
      induction k with
      | zero =>
        exact Or.inr (fun i hi => by omega)
      | succ k ihk =>
        cases ihk (by omega) with
        | inl h =>
          rcases h with ⟨i, hik, hi⟩
          exact Or.inl ⟨i, by omega, hi⟩
        | inr h =>
          let idx : Fin m := ⟨k, by omega⟩
          if heq : f idx.castSucc = f last then
            exact Or.inl ⟨idx, by dsimp [idx]; omega, heq⟩
          else
            apply Or.inr
            intro i hik
            if hik' : i.val < k then
              exact h i hik'
            else
              have hieq : i = idx := Fin.ext (by dsimp [idx]; omega)
              rw [hieq]
              exact heq
    cases hdec with
    | inl hhit =>
      rcases hhit with ⟨i, hi⟩
      exact ⟨i.castSucc, last, i.isLt, hi⟩
    | inr hmiss =>
      let f' : Fin m → α := fun i => f i.castSucc
      have hnot' : ¬ (∀ i j : Fin m, f' i = f' j → i = j) := by
        intro hinj'
        apply hnot
        intro a b hab
        if ha : a.val < m then
          if hb : b.val < m then
            let ia : Fin m := ⟨a.val, ha⟩
            let ib : Fin m := ⟨b.val, hb⟩
            have hcasta : ia.castSucc = a := Fin.ext rfl
            have hcastb : ib.castSucc = b := Fin.ext rfl
            have h' : f' ia = f' ib := by
              dsimp [f']
              rw [hcasta, hcastb, hab]
            have hij : ia = ib := hinj' ia ib h'
            have hv : ia.val = ib.val := congrArg Fin.val hij
            exact Fin.ext hv
          else
            have hblast : b = last := Fin.ext (by
              have hblt : b.val < m + 1 := b.isLt
              have hlastv : last.val = m := rfl
              omega)
            let ia : Fin m := ⟨a.val, ha⟩
            have hcasta : ia.castSucc = a := Fin.ext rfl
            rw [← hcasta, hblast] at hab
            exact False.elim (hmiss ia hab)
        else
          if hb : b.val < m then
            have halast : a = last := Fin.ext (by
              have halt : a.val < m + 1 := a.isLt
              have hlastv : last.val = m := rfl
              omega)
            let ib : Fin m := ⟨b.val, hb⟩
            have hcastb : ib.castSucc = b := Fin.ext rfl
            rw [halast, ← hcastb] at hab
            exact False.elim (hmiss ib hab.symm)
          else
            have halt : a.val < m + 1 := a.isLt
            have hblt : b.val < m + 1 := b.isLt
            exact Fin.ext (by omega)
      rcases ih f' hnot' with ⟨i, j, hij, heq⟩
      exact ⟨i.castSucc, j.castSucc, hij, heq⟩

theorem iterFun_cancel_inj {α : Type} {g : α → α}
    (hinj : ∀ u v, g u = g v → u = v) :
    ∀ (k d : Nat) (x : α), iterFun g (d + k) x = iterFun g k x → iterFun g d x = x
  | 0, d, x, h => by
    have hd : d + 0 = d := by omega
    rw [hd] at h
    exact h
  | k + 1, d, x, h => by
    have hd : d + (k + 1) = (d + k) + 1 := by omega
    rw [hd] at h
    simp only [iterFun] at h
    exact iterFun_cancel_inj hinj k d x (hinj _ _ h)

/-- Every injective self-map on `Fin n` has a positive period at every point `x : Fin n`. -/
theorem exists_pos_period_fin {n : Nat} (g : Fin n → Fin n)
    (hinj : ∀ u v, g u = g v → u = v) (x : Fin n) :
    ∃ m : Nat, 0 < m ∧ iterFun g m x = x := by
  let seq : Fin (n + 1) → Fin n := fun i => iterFun g i.val x
  have hnot := not_injective_fin_succ n seq
  rcases exists_ne_map_eq_of_not_injective seq hnot with ⟨i, j, hij, heq⟩
  dsimp [seq] at heq
  refine ⟨j.val - i.val, by omega, ?_⟩
  have hsum : (j.val - i.val) + i.val = j.val := by omega
  rw [← hsum] at heq
  exact iterFun_cancel_inj hinj i.val (j.val - i.val) x heq.symm

/-! ### Symmetric Group `Perm n` and Group Actions on Posets -/

/-- The symmetric group `S_n` of permutations on `Fin n`. -/
structure Perm (n : Nat) where
  toFun : Fin n → Fin n
  invFun : Fin n → Fin n
  left_inv : ∀ i, invFun (toFun i) = i
  right_inv : ∀ i, toFun (invFun i) = i

namespace Perm

def id (n : Nat) : Perm n where
  toFun := fun i => i
  invFun := fun i => i
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

def inv {n : Nat} (σ : Perm n) : Perm n where
  toFun := σ.invFun
  invFun := σ.toFun
  left_inv := σ.right_inv
  right_inv := σ.left_inv

def comp {n : Nat} (σ τ : Perm n) : Perm n where
  toFun := fun i => σ.toFun (τ.toFun i)
  invFun := fun i => τ.invFun (σ.invFun i)
  left_inv := fun i => by rw [σ.left_inv, τ.left_inv]
  right_inv := fun i => by rw [τ.right_inv, σ.right_inv]

theorem injective {n : Nat} (σ : Perm n) : ∀ ⦃i j⦄, σ.toFun i = σ.toFun j → i = j := by
  intro i j h
  have h' := congrArg σ.invFun h
  rw [σ.left_inv, σ.left_inv] at h'
  exact h'

theorem ext {n : Nat} {σ τ : Perm n} (h : ∀ i, σ.toFun i = τ.toFun i) : σ = τ := by
  cases σ with
  | mk f₁ g₁ l₁ r₁ =>
    cases τ with
    | mk f₂ g₂ l₂ r₂ =>
      have hf : f₁ = f₂ := funext h
      subst hf
      have hg : g₁ = g₂ := by
        funext j
        have h1 : g₁ (f₁ (g₂ j)) = g₁ j := congrArg g₁ (r₂ j)
        rw [l₁ (g₂ j)] at h1
        exact h1.symm
      subst hg
      rfl

/-- Transposition swapping `a` and `b` in `Fin n`. -/
def swap {n : Nat} (a b : Fin n) : Perm n where
  toFun := fun i => if i = a then b else if i = b then a else i
  invFun := fun i => if i = a then b else if i = b then a else i
  left_inv := by
    intro i
    by_cases ha : i = a
    · subst ha; simp
    · by_cases hb : i = b
      · subst hb; simp
      · simp [ha, hb]
  right_inv := by
    intro i
    by_cases ha : i = a
    · subst ha; simp
    · by_cases hb : i = b
      · subst hb; simp
      · simp [ha, hb]

end Perm

/-- A finite-period group action on a poset `P`. -/
structure PosetGroupAction {α : Type} (P : Poset α) (G : Type) where
  one : G
  mul : G → G → G
  inv : G → G
  act : G → α → α
  act_one : ∀ x, act one x = x
  act_mul : ∀ g h x, act (mul g h) x = act g (act h x)
  act_inv_left : ∀ g x, act (inv g) (act g x) = x
  act_inv_right : ∀ g x, act g (act (inv g) x) = x
  act_le : ∀ g {x y}, P.le x y → P.le (act g x) (act g y)
  finite_period : ∀ g x, ∃ m, 0 < m ∧ iterFun (act g) m x = x

namespace PosetGroupAction

/-- Two elements lie in the same `G`-orbit. -/
def OrbitEq {α G : Type} {P : Poset α} (A : PosetGroupAction P G) (x y : α) : Prop :=
  ∃ g : G, A.act g x = y

/-- Quotient poset order on `G`-orbits: `[x] ≤ [y]` iff `∃ g, x ≤ g · y`. -/
def OrbitLe {α G : Type} {P : Poset α} (A : PosetGroupAction P G) (x y : α) : Prop :=
  ∃ g : G, P.le x (A.act g y)

theorem orbitEq_refl {α G : Type} {P : Poset α} (A : PosetGroupAction P G) (x : α) :
    A.OrbitEq x x :=
  ⟨A.one, A.act_one x⟩

theorem orbitEq_symm {α G : Type} {P : Poset α} (A : PosetGroupAction P G)
    {x y : α} (h : A.OrbitEq x y) : A.OrbitEq y x := by
  rcases h with ⟨g, rfl⟩
  exact ⟨A.inv g, A.act_inv_left g x⟩

theorem orbitEq_trans {α G : Type} {P : Poset α} (A : PosetGroupAction P G)
    {x y z : α} (h₁ : A.OrbitEq x y) (h₂ : A.OrbitEq y z) : A.OrbitEq x z := by
  rcases h₁ with ⟨g, rfl⟩
  rcases h₂ with ⟨h, rfl⟩
  exact ⟨A.mul h g, A.act_mul h g x⟩

/-- **Every single `G`-orbit is an antichain in `P`.** -/
theorem orbit_isAntichain {α G : Type} {P : Poset α} (A : PosetGroupAction P G)
    {x y : α} (horb : A.OrbitEq x y) (hle : P.le x y) : x = y := by
  rcases horb with ⟨g, rfl⟩
  rcases A.finite_period g x with ⟨m, hm, hper⟩
  exact eq_of_le_of_finite_period P (A.act g) (fun _ _ h => A.act_le g h) hm hper hle

theorem orbitLe_refl {α G : Type} {P : Poset α} (A : PosetGroupAction P G) (x : α) :
    A.OrbitLe x x :=
  ⟨A.one, by rw [A.act_one]; exact P.le_refl x⟩

theorem orbitLe_of_orbitEq {α G : Type} {P : Poset α} (A : PosetGroupAction P G)
    {x y : α} (h : A.OrbitEq x y) : A.OrbitLe x y := by
  rcases A.orbitEq_symm h with ⟨g, rfl⟩
  exact ⟨g, P.le_refl _⟩

theorem orbitLe_trans {α G : Type} {P : Poset α} (A : PosetGroupAction P G)
    {x y z : α} (h₁ : A.OrbitLe x y) (h₂ : A.OrbitLe y z) : A.OrbitLe x z := by
  rcases h₁ with ⟨g₁, hle₁⟩
  rcases h₂ with ⟨g₂, hle₂⟩
  refine ⟨A.mul g₁ g₂, ?_⟩
  rw [A.act_mul]
  exact P.le_trans hle₁ (A.act_le g₁ hle₂)

/-- **Quotient Poset Antisymmetry**: `[x] ≤ [y]` and `[y] ≤ [x]` imply `[x] = [y]`. -/
theorem orbitLe_antisymm {α G : Type} {P : Poset α} (A : PosetGroupAction P G)
    {x y : α} (h₁ : A.OrbitLe x y) (h₂ : A.OrbitLe y x) : A.OrbitEq x y := by
  rcases h₁ with ⟨g₁, hle₁⟩
  rcases h₂ with ⟨g₂, hle₂⟩
  have hchain : P.le x (A.act (A.mul g₁ g₂) x) := by
    rw [A.act_mul]
    exact P.le_trans hle₁ (A.act_le g₁ hle₂)
  have heq : x = A.act (A.mul g₁ g₂) x :=
    A.orbit_isAntichain ⟨A.mul g₁ g₂, rfl⟩ hchain
  rw [A.act_mul] at heq
  have hgy_le_x : P.le (A.act g₁ y) x := by
    have hstep : P.le (A.act g₁ y) (A.act g₁ (A.act g₂ x)) := A.act_le g₁ hle₂
    rw [← heq] at hstep
    exact hstep
  have hx_eq_gy : x = A.act g₁ y := P.le_antisymm hle₁ hgy_le_x
  exact ⟨A.inv g₁, by rw [hx_eq_gy, A.act_inv_left]⟩

/-- A predicate `S : α → Prop` is `G`-invariant. -/
def IsInvariantPred {α G : Type} {P : Poset α} (A : PosetGroupAction P G) (S : α → Prop) : Prop :=
  ∀ g x, S x → S (A.act g x)

/-- **Fundamental Invariant-Antichain ↔ Orbit-Antichain Equivalence**:
    A `G`-invariant subset `S` of `P` is an antichain in `P` if and only if
    any two elements of `S` related in the quotient poset `P/G` lie in the same `G`-orbit. -/
theorem invariant_antichain_iff_orbit_antichain {α G : Type} {P : Poset α}
    (A : PosetGroupAction P G) {S : α → Prop} (hinv : A.IsInvariantPred S) :
    P.IsAntichainPred S ↔ (∀ ⦃x y⦄, S x → S y → A.OrbitLe x y → A.OrbitEq x y) := by
  constructor
  · intro hant x y hsx hsy horble
    rcases horble with ⟨g, hle⟩
    have hgy : S (A.act g y) := hinv g y hsy
    have heq : x = A.act g y := hant hsx hgy hle
    exact ⟨A.inv g, by rw [heq, A.act_inv_left]⟩
  · intro horb x y hsx hsy hle
    have hle_orb : A.OrbitLe x y := ⟨A.one, by rw [A.act_one]; exact hle⟩
    have heq_orb : A.OrbitEq x y := horb hsx hsy hle_orb
    exact A.orbit_isAntichain heq_orb hle

end PosetGroupAction

end OrbitSperner
