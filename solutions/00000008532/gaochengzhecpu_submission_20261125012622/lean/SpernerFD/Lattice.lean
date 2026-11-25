/-
  SpernerFD/Lattice.lean
  The bounded free distributive lattice `FD n` (monotone Boolean functions on `{0,1}^n`)
  and the unbounded free distributive lattice `FD0 n` (non-constant monotone functions
  preserving `0...0 ↦ false` and `1...1 ↦ true`), together with:
    * Partial order, meet/join, distributivity, and free generators;
    * Proof of the universal property of `FD n` (and `FD0 n`) as the free
      bounded (resp. unbounded) distributive lattice on `n` generators;
    * Constructive duplicate-free enumerations `allFD n` and `allFD0 n`.
-/

import SpernerFD.Basic

namespace SpernerFD

/-! ## 1. Bounded Free Distributive Lattice `FD n` -/

/-- A Boolean function on `Cube n` is monotone if `x ≤ y` and `f x = true` imply `f y = true`. -/
def IsMonotone {n : Nat} (f : Cube n → Bool) : Prop :=
  ∀ x y : Cube n, CubeLe x y → f x = true → f y = true

instance instDecidableIsMonotone {n : Nat} (f : Cube n → Bool) : Decidable (IsMonotone f) :=
  match inferInstanceAs
    (Decidable (∀ x ∈ allCubes n, ∀ y ∈ allCubes n, CubeLe x y → f x = true → f y = true)) with
  | isTrue h => isTrue (fun x y hxy hfx => h x (mem_allCubes x) y (mem_allCubes y) hxy hfx)
  | isFalse h => isFalse (fun hm => h (fun x _ y _ hxy hfx => hm x y hxy hfx))

/-- The bounded free distributive lattice `FD(n)` on `n` generators, modeled as
    monotone Boolean functions `Cube n → Bool`. -/
def FD (n : Nat) : Type := { f : Cube n → Bool // IsMonotone f }

theorem fd_ext {n : Nat} {f g : FD n} (h : ∀ x : Cube n, f.val x = g.val x) : f = g :=
  Subtype.ext (funext h)

instance instDecidableEqFD {n : Nat} : DecidableEq (FD n) := fun f g =>
  match inferInstanceAs (Decidable (∀ x ∈ allCubes n, f.val x = g.val x)) with
  | isTrue h => isTrue (fd_ext fun x => h x (mem_allCubes x))
  | isFalse h => isFalse (fun heq => h (fun x _ => by rw [heq]))

/-- Pointwise partial order on `FD n`. -/
def FDLe {n : Nat} (f g : FD n) : Prop :=
  ∀ x : Cube n, f.val x = true → g.val x = true

instance instDecidableFDLe {n : Nat} (f g : FD n) : Decidable (FDLe f g) :=
  match inferInstanceAs (Decidable (∀ x ∈ allCubes n, f.val x = true → g.val x = true)) with
  | isTrue h => isTrue (fun x hfx => h x (mem_allCubes x) hfx)
  | isFalse h => isFalse (fun hle => h (fun x _ hfx => hle x hfx))

theorem fdLe_refl {n : Nat} (f : FD n) : FDLe f f :=
  fun _ h => h

theorem fdLe_trans {n : Nat} {f g h : FD n} (hfg : FDLe f g) (hgh : FDLe g h) : FDLe f h :=
  fun x hx => hgh x (hfg x hx)

theorem fdLe_antisymm {n : Nat} {f g : FD n} (hfg : FDLe f g) (hgf : FDLe g f) : f = g := by
  apply fd_ext
  intro x
  cases hfx : f.val x <;> cases hgx : g.val x
  · rfl
  · have := hgf x hgx; rw [hfx] at this; nomatch this
  · have := hfg x hfx; rw [hgx] at this; nomatch this
  · rfl

/-- Lattice operations and free generators on `FD n`. -/
def botFD (n : Nat) : FD n := ⟨(fun _ => false), fun _ _ _ h => nomatch h⟩
def topFD (n : Nat) : FD n := ⟨(fun _ => true), fun _ _ _ _ => rfl⟩

def joinFD {n : Nat} (f g : FD n) : FD n :=
  ⟨fun x => f.val x || g.val x, fun x y hxy h => by
    dsimp only at h ⊢
    cases hfx : f.val x with
    | true =>
      rw [f.property x y hxy hfx]; rfl
    | false =>
      rw [hfx, Bool.false_or] at h
      rw [g.property x y hxy h, Bool.or_true]⟩

def meetFD {n : Nat} (f g : FD n) : FD n :=
  ⟨fun x => f.val x && g.val x, fun x y hxy h => by
    dsimp only at h ⊢
    cases hfx : f.val x with
    | false => rw [hfx] at h; nomatch h
    | true =>
      rw [hfx, Bool.true_and] at h
      rw [f.property x y hxy hfx, g.property x y hxy h]; rfl⟩

/-- The `i`-th free generator `x_i` of `FD n`. -/
def genFD {n : Nat} (i : Fin n) : FD n :=
  ⟨fun x => x i, fun _ _ hxy hx => hxy i hx⟩

theorem botFD_le {n : Nat} (f : FD n) : FDLe (botFD n) f :=
  fun _ h => nomatch h

theorem le_topFD {n : Nat} (f : FD n) : FDLe f (topFD n) :=
  fun _ _ => rfl

theorem le_joinFD_left {n : Nat} (f g : FD n) : FDLe f (joinFD f g) :=
  fun x hx => by change (f.val x || g.val x) = true; rw [hx]; rfl

theorem le_joinFD_right {n : Nat} (f g : FD n) : FDLe g (joinFD f g) :=
  fun x hx => by change (f.val x || g.val x) = true; rw [hx, Bool.or_true]

theorem joinFD_le {n : Nat} {f g h : FD n} (hf : FDLe f h) (hg : FDLe g h) :
    FDLe (joinFD f g) h :=
  fun x hx => by
    change (f.val x || g.val x) = true at hx
    cases hfx : f.val x with
    | true => exact hf x hfx
    | false => rw [hfx, Bool.false_or] at hx; exact hg x hx

theorem meetFD_le_left {n : Nat} (f g : FD n) : FDLe (meetFD f g) f :=
  fun x hx => by
    change (f.val x && g.val x) = true at hx
    cases hfx : f.val x with
    | true => rfl
    | false => rw [hfx] at hx; nomatch hx

theorem meetFD_le_right {n : Nat} (f g : FD n) : FDLe (meetFD f g) g :=
  fun x hx => by
    change (f.val x && g.val x) = true at hx
    cases hgx : g.val x with
    | true => rfl
    | false => rw [hgx, Bool.and_false] at hx; nomatch hx

theorem le_meetFD {n : Nat} {f g h : FD n} (hg : FDLe f g) (hh : FDLe f h) :
    FDLe f (meetFD g h) :=
  fun x hx => by
    change (g.val x && h.val x) = true
    rw [hg x hx, hh x hx]; rfl

/-- Distributivity of meet over join in `FD n`. -/
theorem meetFD_joinFD_distrib_left {n : Nat} (f g h : FD n) :
    meetFD f (joinFD g h) = joinFD (meetFD f g) (meetFD f h) := by
  apply fd_ext
  intro x
  change (f.val x && (g.val x || h.val x)) = ((f.val x && g.val x) || (f.val x && h.val x))
  cases f.val x <;> cases g.val x <;> cases h.val x <;> rfl

/-- Distributivity of join over meet in `FD n`. -/
theorem joinFD_meetFD_distrib_left {n : Nat} (f g h : FD n) :
    joinFD f (meetFD g h) = meetFD (joinFD f g) (joinFD f h) := by
  apply fd_ext
  intro x
  change (f.val x || (g.val x && h.val x)) = ((f.val x || g.val x) && (f.val x || h.val x))
  cases f.val x <;> cases g.val x <;> cases h.val x <;> rfl

/-! ## 2. Shannon Decomposition and Universal Property of `FD n` -/

/-- Lower cofactor `f(false, ·)` of `f : FD (n + 1)`. -/
def lowFD {n : Nat} (f : FD (n + 1)) : FD n :=
  ⟨fun x => f.val (consCube false x), fun x y hxy hx =>
    f.property (consCube false x) (consCube false y)
      (cubeLe_succ_iff.mpr ⟨(fun h => nomatch h), by simpa using hxy⟩) hx⟩

/-- Upper cofactor `f(true, ·)` of `f : FD (n + 1)`. -/
def highFD {n : Nat} (f : FD (n + 1)) : FD n :=
  ⟨fun x => f.val (consCube true x), fun x y hxy hx =>
    f.property (consCube true x) (consCube true y)
      (cubeLe_succ_iff.mpr ⟨(fun _ => rfl), by simpa using hxy⟩) hx⟩

/-- Embed `FD n` into `FD (n + 1)` by ignoring coordinate `0`. -/
def liftFD {n : Nat} (g : FD n) : FD (n + 1) :=
  ⟨fun y => g.val (tailCube y), fun x y hxy hx =>
    g.property (tailCube x) (tailCube y) (cubeLe_succ_iff.mp hxy).2 hx⟩

theorem lowFD_le_highFD {n : Nat} (f : FD (n + 1)) : FDLe (lowFD f) (highFD f) := by
  intro x hx
  exact f.property (consCube false x) (consCube true x)
    (cubeLe_succ_iff.mpr ⟨(fun h => nomatch h), by simp [cubeLe_refl]⟩) hx

/-- Combine any pair `f₀ ≤ f₁` in `FD n` into an element of `FD (n + 1)`. -/
def mergeFD {n : Nat} (f₀ f₁ : FD n) (hle : FDLe f₀ f₁) : FD (n + 1) :=
  ⟨fun y => if headCube y then f₁.val (tailCube y) else f₀.val (tailCube y),
   fun x y hxy hx => by
     obtain ⟨h0, ht⟩ := cubeLe_succ_iff.mp hxy
     cases hhx : headCube x <;> cases hhy : headCube y
     · simp only [hhx, Bool.false_eq_true, ↓reduceIte, hhy] at hx ⊢
       exact f₀.property (tailCube x) (tailCube y) ht hx
     · simp only [hhx, Bool.false_eq_true, ↓reduceIte, hhy] at hx ⊢
       exact hle (tailCube y) (f₀.property (tailCube x) (tailCube y) ht hx)
     · rw [hhx] at h0; have := h0 rfl; rw [hhy] at this; nomatch this
     · simp only [hhx, ↓reduceIte, hhy] at hx ⊢
       exact f₁.property (tailCube x) (tailCube y) ht hx⟩

theorem lowFD_mergeFD {n : Nat} (f₀ f₁ : FD n) (hle : FDLe f₀ f₁) :
    lowFD (mergeFD f₀ f₁ hle) = f₀ := by
  apply fd_ext; intro x; simp [lowFD, mergeFD]

theorem highFD_mergeFD {n : Nat} (f₀ f₁ : FD n) (hle : FDLe f₀ f₁) :
    highFD (mergeFD f₀ f₁ hle) = f₁ := by
  apply fd_ext; intro x; simp [highFD, mergeFD]

theorem mergeFD_low_high {n : Nat} (f : FD (n + 1)) :
    mergeFD (lowFD f) (highFD f) (lowFD_le_highFD f) = f := by
  apply fd_ext
  intro y
  simp only [mergeFD, lowFD, highFD]
  cases hy : headCube y with
  | false =>
    have hc : consCube false (tailCube y) = y := by rw [← hy, consCube_head_tail]
    rw [hc]; simp [hy]
  | true =>
    have hc : consCube true (tailCube y) = y := by rw [← hy, consCube_head_tail]
    rw [hc]; simp [hy]

/-- Canonical Shannon expansion in `FD (n + 1)`:
    `f = lift(low f) ⊔ (x_0 ⊓ lift(high f))`. -/
theorem shannon_decomp_FD {n : Nat} (f : FD (n + 1)) :
    f = joinFD (liftFD (lowFD f)) (meetFD (genFD ⟨0, Nat.zero_lt_succ n⟩) (liftFD (highFD f))) := by
  apply fd_ext
  intro y
  change f.val y = (f.val (consCube false (tailCube y)) ||
    (headCube y && f.val (consCube true (tailCube y))))
  cases hy : headCube y with
  | false =>
    have hc : consCube false (tailCube y) = y := by rw [← hy, consCube_head_tail]
    rw [hc]; simp
  | true =>
    have hc : consCube true (tailCube y) = y := by rw [← hy, consCube_head_tail]
    rw [hc]
    simp only [Bool.true_and]
    cases hlow : f.val (consCube false (tailCube y)) with
    | false => simp
    | true =>
      have hhi := lowFD_le_highFD f (tailCube y) hlow
      change f.val (consCube true (tailCube y)) = true at hhi
      rw [hc] at hhi
      rw [hhi]; rfl

/-- Axiomatization of an arbitrary bounded distributive lattice `(L, ≤, ⊔, ⊓, ⊥, ⊤)`. -/
structure BoundedDistLattice (L : Type u) where
  le : L → L → Prop
  join : L → L → L
  meet : L → L → L
  bot : L
  top : L
  le_refl : ∀ a, le a a
  le_trans : ∀ {a b c}, le a b → le b c → le a c
  le_antisymm : ∀ {a b}, le a b → le b a → a = b
  bot_le : ∀ a, le bot a
  le_top : ∀ a, le a top
  le_join_left : ∀ a b, le a (join a b)
  le_join_right : ∀ a b, le b (join a b)
  join_le : ∀ {a b c}, le a c → le b c → le (join a b) c
  meet_le_left : ∀ a b, le (meet a b) a
  meet_le_right : ∀ a b, le (meet a b) b
  le_meet : ∀ {a b c}, le a b → le a c → le a (meet b c)
  meet_join_distrib_left : ∀ a b c, meet a (join b c) = join (meet a b) (meet a c)

/-- `FD n` itself forms a `BoundedDistLattice`. -/
def fdBoundedDistLattice (n : Nat) : BoundedDistLattice (FD n) where
  le := FDLe
  join := joinFD
  meet := meetFD
  bot := botFD n
  top := topFD n
  le_refl := fdLe_refl
  le_trans := fdLe_trans
  le_antisymm := fdLe_antisymm
  bot_le := botFD_le
  le_top := le_topFD
  le_join_left := le_joinFD_left
  le_join_right := le_joinFD_right
  join_le := joinFD_le
  meet_le_left := meetFD_le_left
  meet_le_right := meetFD_le_right
  le_meet := le_meetFD
  meet_join_distrib_left := meetFD_joinFD_distrib_left

namespace BoundedDistLattice

variable {L : Type u} (B : BoundedDistLattice L)

theorem join_comm (a b : L) : B.join a b = B.join b a :=
  B.le_antisymm (B.join_le (B.le_join_right b a) (B.le_join_left b a))
    (B.join_le (B.le_join_right a b) (B.le_join_left a b))

theorem meet_comm (a b : L) : B.meet a b = B.meet b a :=
  B.le_antisymm (B.le_meet (B.meet_le_right a b) (B.meet_le_left a b))
    (B.le_meet (B.meet_le_right b a) (B.meet_le_left b a))

theorem join_assoc (a b c : L) : B.join (B.join a b) c = B.join a (B.join b c) :=
  B.le_antisymm
    (B.join_le
      (B.join_le (B.le_join_left a _)
        (B.le_trans (B.le_join_left b c) (B.le_join_right a _)))
      (B.le_trans (B.le_join_right b c) (B.le_join_right a _)))
    (B.join_le
      (B.le_trans (B.le_join_left a b) (B.le_join_left _ c))
      (B.join_le (B.le_trans (B.le_join_right a b) (B.le_join_left _ c))
        (B.le_join_right _ c)))

theorem meet_assoc (a b c : L) : B.meet (B.meet a b) c = B.meet a (B.meet b c) :=
  B.le_antisymm
    (B.le_meet (B.le_trans (B.meet_le_left _ c) (B.meet_le_left a b))
      (B.le_meet (B.le_trans (B.meet_le_left _ c) (B.meet_le_right a b))
        (B.meet_le_right _ c)))
    (B.le_meet
      (B.le_meet (B.meet_le_left a _)
        (B.le_trans (B.meet_le_right a _) (B.meet_le_left b c)))
      (B.le_trans (B.meet_le_right a _) (B.meet_le_right b c)))

theorem join_bot (a : L) : B.join a B.bot = a :=
  B.le_antisymm (B.join_le (B.le_refl a) (B.bot_le a)) (B.le_join_left a B.bot)

theorem bot_join (a : L) : B.join B.bot a = a := by
  rw [B.join_comm, B.join_bot]

theorem join_top (a : L) : B.join a B.top = B.top :=
  B.le_antisymm (B.le_top _) (B.le_join_right a B.top)

theorem top_join (a : L) : B.join B.top a = B.top := by
  rw [B.join_comm, B.join_top]

theorem meet_bot (a : L) : B.meet a B.bot = B.bot :=
  B.le_antisymm (B.meet_le_right a B.bot) (B.bot_le _)

theorem meet_top (a : L) : B.meet a B.top = a :=
  B.le_antisymm (B.meet_le_left a B.top) (B.le_meet (B.le_refl a) (B.le_top a))

theorem meet_idem (a : L) : B.meet a a = a :=
  B.le_antisymm (B.meet_le_left a a) (B.le_meet (B.le_refl a) (B.le_refl a))

theorem join_eq_right_of_le {a b : L} (h : B.le a b) : B.join a b = b :=
  B.le_antisymm (B.join_le h (B.le_refl b)) (B.le_join_right a b)

theorem join_eq_left_of_le {a b : L} (h : B.le b a) : B.join a b = a :=
  B.le_antisymm (B.join_le (B.le_refl a) h) (B.le_join_left a b)

theorem join_mono {a₁ a₂ b₁ b₂ : L} (ha : B.le a₁ a₂) (hb : B.le b₁ b₂) :
    B.le (B.join a₁ b₁) (B.join a₂ b₂) :=
  B.join_le (B.le_trans ha (B.le_join_left a₂ b₂)) (B.le_trans hb (B.le_join_right a₂ b₂))

theorem meet_mono {a₁ a₂ b₁ b₂ : L} (ha : B.le a₁ a₂) (hb : B.le b₁ b₂) :
    B.le (B.meet a₁ b₁) (B.meet a₂ b₂) :=
  B.le_meet (B.le_trans (B.meet_le_left a₁ b₁) ha) (B.le_trans (B.meet_le_right a₁ b₁) hb)

theorem meet_join_distrib_right (a b c : L) :
    B.meet (B.join a b) c = B.join (B.meet a c) (B.meet b c) := by
  rw [B.meet_comm (B.join a b) c, B.meet_join_distrib_left, B.meet_comm c a, B.meet_comm c b]

/-- Key algebraic identity for Shannon meet preservation when `a₀ ≤ a₁` and `b₀ ≤ b₁`. -/
theorem shannon_meet_identity {a₀ a₁ b₀ b₁ x : L}
    (ha : B.le a₀ a₁) (hb : B.le b₀ b₁) :
    B.meet (B.join a₀ (B.meet x a₁)) (B.join b₀ (B.meet x b₁)) =
      B.join (B.meet a₀ b₀) (B.meet x (B.meet a₁ b₁)) := by
  rw [B.meet_join_distrib_left, B.meet_join_distrib_right, B.meet_join_distrib_right]
  -- Four terms: `(a₀ ⊓ b₀)`, `(x ⊓ a₁) ⊓ b₀`, `a₀ ⊓ (x ⊓ b₁)`, `(x ⊓ a₁) ⊓ (x ⊓ b₁)`
  have ht4 : B.meet (B.meet x a₁) (B.meet x b₁) = B.meet x (B.meet a₁ b₁) := by
    apply B.le_antisymm
    · exact B.le_meet (B.le_trans (B.meet_le_left _ _) (B.meet_le_left x a₁))
        (B.le_meet (B.le_trans (B.meet_le_left _ _) (B.meet_le_right x a₁))
          (B.le_trans (B.meet_le_right _ _) (B.meet_le_right x b₁)))
    · exact B.le_meet
        (B.le_meet (B.meet_le_left x _)
          (B.le_trans (B.meet_le_right x _) (B.meet_le_left a₁ b₁)))
        (B.le_meet (B.meet_le_left x _)
          (B.le_trans (B.meet_le_right x _) (B.meet_le_right a₁ b₁)))
  rw [ht4]
  have hle2 : B.le (B.meet (B.meet x a₁) b₀) (B.meet x (B.meet a₁ b₁)) := by
    rw [B.meet_assoc]
    exact B.meet_mono (B.le_refl x) (B.meet_mono (B.le_refl a₁) hb)
  have hle3 : B.le (B.meet a₀ (B.meet x b₁)) (B.meet x (B.meet a₁ b₁)) := by
    have : B.le (B.meet a₀ (B.meet x b₁)) (B.meet a₁ (B.meet x b₁)) :=
      B.meet_mono ha (B.le_refl _)
    apply B.le_trans this
    exact B.le_meet (B.le_trans (B.meet_le_right a₁ _) (B.meet_le_left x b₁))
      (B.le_meet (B.meet_le_left a₁ _) (B.le_trans (B.meet_le_right a₁ _) (B.meet_le_right x b₁)))
  rw [B.join_eq_right_of_le hle3]
  rw [B.join_assoc, B.join_eq_right_of_le hle2]

end BoundedDistLattice

/-- Predicate stating that `φ : FD n → L` is a bounded lattice homomorphism. -/
structure IsBoundedHom {L : Type u} (B : BoundedDistLattice L) {n : Nat} (φ : FD n → L) : Prop where
  map_bot : φ (botFD n) = B.bot
  map_top : φ (topFD n) = B.top
  map_join : ∀ f g, φ (joinFD f g) = B.join (φ f) (φ g)
  map_meet : ∀ f g, φ (meetFD f g) = B.meet (φ f) (φ g)

/-- Canonical evaluation of `FD n` into any bounded distributive lattice `L`. -/
def evalBounded {L : Type u} (B : BoundedDistLattice L) :
    {n : Nat} → (Fin n → L) → FD n → L
  | 0, _, f => if f.val (botCube 0) then B.top else B.bot
  | n + 1, v, f =>
    let v' : Fin n → L := fun i => v i.succ
    B.join (evalBounded B v' (lowFD f))
      (B.meet (v ⟨0, Nat.zero_lt_succ n⟩) (evalBounded B v' (highFD f)))

theorem evalBounded_mono {L : Type u} (B : BoundedDistLattice L) :
    {n : Nat} → (v : Fin n → L) → {f g : FD n} → FDLe f g →
      B.le (evalBounded B v f) (evalBounded B v g)
  | 0, _, f, g, hfg => by
    simp only [evalBounded]
    cases hfx : f.val (botCube 0) <;> cases hgx : g.val (botCube 0)
    · exact B.le_refl B.bot
    · exact B.bot_le B.top
    · have := hfg (botCube 0) hfx; rw [hgx] at this; nomatch this
    · exact B.le_refl B.top
  | _ + 1, v, f, g, hfg => by
    simp only [evalBounded]
    have hlow : FDLe (lowFD f) (lowFD g) := fun x hx => hfg (consCube false x) hx
    have hhigh : FDLe (highFD f) (highFD g) := fun x hx => hfg (consCube true x) hx
    exact B.join_mono (evalBounded_mono B _ hlow)
      (B.meet_mono (B.le_refl _) (evalBounded_mono B _ hhigh))

theorem evalBounded_isHom {L : Type u} (B : BoundedDistLattice L) :
    {n : Nat} → (v : Fin n → L) → IsBoundedHom B (evalBounded B v)
  | 0, _ =>
    { map_bot := rfl
      map_top := rfl
      map_join := fun f g => by
        simp only [evalBounded]
        change (if (f.val (botCube 0) || g.val (botCube 0)) then B.top else B.bot) = _
        cases f.val (botCube 0) <;> cases g.val (botCube 0)
        · exact (B.bot_join B.bot).symm
        · exact (B.bot_join B.top).symm
        · exact (B.join_bot B.top).symm
        · exact (B.top_join B.top).symm
      map_meet := fun f g => by
        simp only [evalBounded]
        change (if (f.val (botCube 0) && g.val (botCube 0)) then B.top else B.bot) = _
        cases f.val (botCube 0) <;> cases g.val (botCube 0) <;> simp only [Bool.false_and, Bool.true_and, Bool.false_eq_true, ↓reduceIte]
        · exact (B.meet_bot B.bot).symm
        · rw [B.meet_comm]; exact (B.meet_bot B.top).symm
        · exact (B.meet_bot B.top).symm
        · exact (B.meet_top B.top).symm }
  | n + 1, v =>
    let v' : Fin n → L := fun i => v i.succ
    let ih := evalBounded_isHom B v'
    { map_bot := by
        simp only [evalBounded]
        have hl : lowFD (botFD (n + 1)) = botFD n := rfl
        have hh : highFD (botFD (n + 1)) = botFD n := rfl
        change B.join (evalBounded B v' (lowFD (botFD (n + 1))))
          (B.meet (v ⟨0, Nat.zero_lt_succ n⟩) (evalBounded B v' (highFD (botFD (n + 1))))) = B.bot
        rw [hl, hh, ih.map_bot, B.meet_bot, B.bot_join]
      map_top := by
        simp only [evalBounded]
        have hl : lowFD (topFD (n + 1)) = topFD n := rfl
        have hh : highFD (topFD (n + 1)) = topFD n := rfl
        change B.join (evalBounded B v' (lowFD (topFD (n + 1))))
          (B.meet (v ⟨0, Nat.zero_lt_succ n⟩) (evalBounded B v' (highFD (topFD (n + 1))))) = B.top
        rw [hl, hh, ih.map_top, B.meet_top, B.top_join]
      map_join := fun f g => by
        simp only [evalBounded]
        have hl : lowFD (joinFD f g) = joinFD (lowFD f) (lowFD g) := rfl
        have hh : highFD (joinFD f g) = joinFD (highFD f) (highFD g) := rfl
        rw [hl, hh, ih.map_join, ih.map_join, B.meet_join_distrib_left]
        -- Rearrange `(a₀ ⊔ b₀) ⊔ ((x ⊓ a₁) ⊔ (x ⊓ b₁)) = (a₀ ⊔ (x ⊓ a₁)) ⊔ (b₀ ⊔ (x ⊓ b₁))`
        rw [B.join_assoc (evalBounded B v' (lowFD f)),
            ← B.join_assoc (evalBounded B v' (lowFD g)),
            B.join_comm (evalBounded B v' (lowFD g)) (B.meet _ (evalBounded B v' (highFD f))),
            B.join_assoc (B.meet _ _),
            ← B.join_assoc]
      map_meet := fun f g => by
        simp only [evalBounded]
        have hl : lowFD (meetFD f g) = meetFD (lowFD f) (lowFD g) := rfl
        have hh : highFD (meetFD f g) = meetFD (highFD f) (highFD g) := rfl
        rw [hl, hh, ih.map_meet, ih.map_meet]
        exact (B.shannon_meet_identity
          (evalBounded_mono B v' (lowFD_le_highFD f))
          (evalBounded_mono B v' (lowFD_le_highFD g))).symm }

theorem evalBounded_gen {L : Type u} (B : BoundedDistLattice L) :
    {n : Nat} → (v : Fin n → L) → (i : Fin n) → evalBounded B v (genFD i) = v i
  | 0, _, i => Fin.elim0 i
  | n + 1, v, i => by
    let v' : Fin n → L := fun j => v j.succ
    by_cases hiz : i.val = 0
    · have hi0 : i = ⟨0, Nat.zero_lt_succ n⟩ := Fin.ext hiz
      subst hi0
      simp only [evalBounded]
      have hl : lowFD (genFD ⟨0, Nat.zero_lt_succ n⟩) = botFD n := by
        apply fd_ext; intro x; rfl
      have hh : highFD (genFD ⟨0, Nat.zero_lt_succ n⟩) = topFD n := by
        apply fd_ext; intro x; rfl
      rw [hl, hh, (evalBounded_isHom B v').map_bot, (evalBounded_isHom B v').map_top,
          B.meet_top, B.bot_join]
    · let j : Fin n := ⟨i.val - 1, by omega⟩
      have hj : j.succ = i := by
        apply Fin.ext; simp only [Fin.val_succ, j]; omega
      rw [← hj]
      simp only [evalBounded]
      have hl : lowFD (genFD j.succ) = genFD j := by
        apply fd_ext; intro x; simp [lowFD, genFD, consCube]
      have hh : highFD (genFD j.succ) = genFD j := by
        apply fd_ext; intro x; simp [highFD, genFD, consCube]
      change B.join (evalBounded B v' (lowFD (genFD j.succ)))
        (B.meet (v ⟨0, Nat.zero_lt_succ n⟩) (evalBounded B v' (highFD (genFD j.succ)))) = v j.succ
      rw [hl, hh, evalBounded_gen B v' j]
      exact B.join_eq_left_of_le (B.meet_le_right _ _)

/-- **Universal Property of `FD n`:** For every bounded distributive lattice `L` and
    every valuation `v : Fin n → L`, `evalBounded B v` is the *unique* bounded lattice
    homomorphism `FD n → L` mapping `genFD i ↦ v i`. -/
theorem evalBounded_unique {L : Type u} (B : BoundedDistLattice L) :
    {n : Nat} → (v : Fin n → L) → (φ : FD n → L) →
    IsBoundedHom B φ → (∀ i : Fin n, φ (genFD i) = v i) →
    ∀ f : FD n, φ f = evalBounded B v f
  | 0, _, φ, hφ, _, f => by
    simp only [evalBounded]
    cases hf : f.val (botCube 0) with
    | false =>
      have hfb : f = botFD 0 := by
        apply fd_ext; intro x
        have hx : x = botCube 0 := funext fun i => Fin.elim0 i
        rw [hx, hf]; rfl
      rw [hfb, hφ.map_bot]; rfl
    | true =>
      have hft : f = topFD 0 := by
        apply fd_ext; intro x
        have hx : x = botCube 0 := funext fun i => Fin.elim0 i
        rw [hx, hf]; rfl
      rw [hft, hφ.map_top]; rfl
  | n + 1, v, φ, hφ, hgen, f => by
    let v' : Fin n → L := fun j => v j.succ
    let ψ : FD n → L := fun g => φ (liftFD g)
    have hψ : IsBoundedHom B ψ :=
      { map_bot := hφ.map_bot
        map_top := hφ.map_top
        map_join := fun g₁ g₂ => hφ.map_join (liftFD g₁) (liftFD g₂)
        map_meet := fun g₁ g₂ => hφ.map_meet (liftFD g₁) (liftFD g₂) }
    have hψgen : ∀ j : Fin n, ψ (genFD j) = v' j := by
      intro j
      have hlift : liftFD (genFD j) = genFD j.succ := rfl
      change φ (liftFD (genFD j)) = v j.succ
      rw [hlift, hgen j.succ]
    have ih := evalBounded_unique B v' ψ hψ hψgen
    have hdecomp := shannon_decomp_FD f
    conv => lhs; rw [hdecomp]
    rw [hφ.map_join, hφ.map_meet, hgen ⟨0, Nat.zero_lt_succ n⟩]
    change B.join (ψ (lowFD f)) (B.meet (v ⟨0, Nat.zero_lt_succ n⟩) (ψ (highFD f))) = _
    rw [ih (lowFD f), ih (highFD f)]
    rfl

/-! ## 3. Unbounded Free Distributive Lattice `FD0 n` -/

/-- The unbounded free distributive lattice `FD_0(n)` on `n` generators (without empty
    join or empty meet): monotone Boolean functions sending `0...0 ↦ false` and `1...1 ↦ true`. -/
def FD0 (n : Nat) : Type :=
  { f : FD n // f.val (botCube n) = false ∧ f.val (topCube n) = true }

theorem fd0_ext {n : Nat} {f g : FD0 n} (h : f.val = g.val) : f = g :=
  Subtype.ext h

instance instDecidableEqFD0 {n : Nat} : DecidableEq (FD0 n) := fun f g =>
  match inferInstanceAs (Decidable (f.val = g.val)) with
  | isTrue h => isTrue (fd0_ext h)
  | isFalse h => isFalse (fun heq => h (by rw [heq]))

/-- Pointwise partial order on `FD0 n` induced from `FD n`. -/
def FD0Le {n : Nat} (f g : FD0 n) : Prop :=
  FDLe f.val g.val

instance instDecidableFD0Le {n : Nat} (f g : FD0 n) : Decidable (FD0Le f g) :=
  instDecidableFDLe f.val g.val

theorem fd0Le_refl {n : Nat} (f : FD0 n) : FD0Le f f := fdLe_refl f.val

theorem fd0Le_trans {n : Nat} {f g h : FD0 n} (hfg : FD0Le f g) (hgh : FD0Le g h) :
    FD0Le f h := fdLe_trans hfg hgh

theorem fd0Le_antisymm {n : Nat} {f g : FD0 n} (hfg : FD0Le f g) (hgf : FD0Le g f) :
    f = g := fd0_ext (fdLe_antisymm hfg hgf)

def joinFD0 {n : Nat} (f g : FD0 n) : FD0 n :=
  ⟨joinFD f.val g.val, by
    constructor
    · change (f.val.val (botCube n) || g.val.val (botCube n)) = false
      rw [f.property.1, g.property.1]; rfl
    · change (f.val.val (topCube n) || g.val.val (topCube n)) = true
      rw [f.property.2]; rfl⟩

def meetFD0 {n : Nat} (f g : FD0 n) : FD0 n :=
  ⟨meetFD f.val g.val, by
    constructor
    · change (f.val.val (botCube n) && g.val.val (botCube n)) = false
      rw [f.property.1]; rfl
    · change (f.val.val (topCube n) && g.val.val (topCube n)) = true
      rw [f.property.2, g.property.2]; rfl⟩

/-- The `i`-th free generator of `FD0 (n + 1)` (`n + 1 ≥ 1`). -/
def genFD0 {n : Nat} (i : Fin (n + 1)) : FD0 (n + 1) :=
  ⟨genFD i, ⟨rfl, rfl⟩⟩

theorem meetFD0_joinFD0_distrib_left {n : Nat} (f g h : FD0 n) :
    meetFD0 f (joinFD0 g h) = joinFD0 (meetFD0 f g) (meetFD0 f h) :=
  fd0_ext (meetFD_joinFD_distrib_left f.val g.val h.val)

theorem joinFD0_meetFD0_distrib_left {n : Nat} (f g h : FD0 n) :
    joinFD0 f (meetFD0 g h) = meetFD0 (joinFD0 f g) (joinFD0 f h) :=
  fd0_ext (joinFD_meetFD_distrib_left f.val g.val h.val)

/-- Every element of `FD n` is either `botFD n`, `topFD n`, or lies in `FD0 n`. -/
theorem fd_trichotomy {n : Nat} (f : FD n) :
    f = botFD n ∨ f = topFD n ∨ (f.val (botCube n) = false ∧ f.val (topCube n) = true) := by
  cases hb : f.val (botCube n) <;> cases ht : f.val (topCube n)
  · left
    apply fd_ext; intro x
    cases hx : f.val x with
    | false => rfl
    | true =>
      have := f.property x (topCube n) (le_topCube x) hx
      rw [ht] at this; nomatch this
  · right; right; exact ⟨rfl, rfl⟩
  · have := f.property (botCube n) (topCube n) (botCube_le (topCube n)) hb
    rw [ht] at this; nomatch this
  · right; left
    apply fd_ext; intro x
    exact f.property (botCube n) x (botCube_le x) hb

theorem botFD_ne_topFD_of_pos {n : Nat} (hn : 1 ≤ n) : botFD n ≠ topFD n := by
  intro heq
  cases n with
  | zero => omega
  | succ m =>
    have h : (botFD (m + 1)).val (botCube (m + 1)) = (topFD (m + 1)).val (botCube (m + 1)) := by
      rw [heq]
    nomatch h

/-! ## 4. Constructive Enumerations `allFD` and `allFD0` -/

/-- Helper flatMap over lists. -/
def flatMapList {α : Type u} {β : Type v} (f : α → List β) : List α → List β
  | [] => []
  | a :: t => f a ++ flatMapList f t

theorem mem_flatMapList_iff {α : Type u} {β : Type v} {f : α → List β} {l : List α} {y : β} :
    y ∈ flatMapList f l ↔ ∃ x ∈ l, y ∈ f x := by
  induction l with
  | nil => simp [flatMapList]
  | cons a t ih =>
    simp only [flatMapList, List.mem_append, ih, List.mem_cons]
    constructor
    · rintro (hya | ⟨x, hxt, hyx⟩)
      · exact ⟨a, Or.inl rfl, hya⟩
      · exact ⟨x, Or.inr hxt, hyx⟩
    · rintro ⟨x, rfl | hxt, hyx⟩
      · exact Or.inl hyx
      · exact Or.inr ⟨x, hxt, hyx⟩

theorem noDup_flatMapList {α : Type u} {β : Type v} {f : α → List β} {l : List α}
    (hl : NoDup l) (hf : ∀ x ∈ l, NoDup (f x))
    (hdisj : ∀ x ∈ l, ∀ y ∈ l, ∀ z, z ∈ f x → z ∈ f y → x = y) :
    NoDup (flatMapList f l) := by
  induction l with
  | nil => exact trivial
  | cons a t ih =>
    obtain ⟨hat, ht⟩ := hl
    apply noDup_append (hf a (List.mem_cons_self ..))
    · exact ih ht (fun x hx => hf x (List.mem_cons_of_mem a hx))
        (fun x hx y hy z hzx hzy =>
          hdisj x (List.mem_cons_of_mem a hx) y (List.mem_cons_of_mem a hy) z hzx hzy)
    · intro z hza hzt
      rcases mem_flatMapList_iff.mp hzt with ⟨b, hbt, hzb⟩
      have hab : a = b := hdisj a (List.mem_cons_self ..) b (List.mem_cons_of_mem a hbt) z hza hzb
      exact hat (hab ▸ hbt)

/-- Constructive duplicate-free enumeration of `FD n` via Dedekind cofactor recursion. -/
def allFD : (n : Nat) → List (FD n)
  | 0 => [botFD 0, topFD 0]
  | n + 1 =>
    flatMapList (fun f₀ =>
      flatMapList (fun f₁ =>
        if h : FDLe f₀ f₁ then [mergeFD f₀ f₁ h] else [])
      (allFD n))
    (allFD n)

theorem mem_allFD : {n : Nat} → (f : FD n) → f ∈ allFD n
  | 0, f => by
    cases hf : f.val (botCube 0) with
    | false =>
      have : f = botFD 0 := by
        apply fd_ext; intro x
        have hx : x = botCube 0 := funext fun i => Fin.elim0 i
        rw [hx, hf]; rfl
      rw [this]; exact List.mem_cons_self ..
    | true =>
      have : f = topFD 0 := by
        apply fd_ext; intro x
        have hx : x = botCube 0 := funext fun i => Fin.elim0 i
        rw [hx, hf]; rfl
      rw [this]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
  | _ + 1, f => by
    simp only [allFD]
    rw [mem_flatMapList_iff]
    refine ⟨lowFD f, mem_allFD (lowFD f), ?_⟩
    rw [mem_flatMapList_iff]
    refine ⟨highFD f, mem_allFD (highFD f), ?_⟩
    have hle := lowFD_le_highFD f
    simp only [hle, ↓reduceDIte, List.mem_singleton]
    exact (mergeFD_low_high f).symm

theorem noDup_allFD : (n : Nat) → NoDup (allFD n)
  | 0 => noDup_pair (fun h => by
      have : (botFD 0).val (botCube 0) = (topFD 0).val (botCube 0) := by rw [h]
      nomatch this)
  | n + 1 => by
    have ih := noDup_allFD n
    simp only [allFD]
    apply noDup_flatMapList ih
    · intro f₀ _
      apply noDup_flatMapList ih
      · intro f₁ _
        split
        · exact noDup_singleton _
        · exact noDup_nil
      · intro f₁ _ g₁ _ z hz₁ hz₂
        split at hz₁ <;> split at hz₂
        · rcases List.mem_singleton.mp hz₁ with rfl
          rcases List.mem_singleton.mp hz₂ with heq
          have hhi : highFD (mergeFD f₀ f₁ ‹_›) = highFD (mergeFD f₀ g₁ ‹_›) := by rw [heq]
          rw [highFD_mergeFD, highFD_mergeFD] at hhi
          exact hhi
        · nomatch hz₂
        · nomatch hz₁
        · nomatch hz₁
    · intro f₀ _ g₀ _ z hz₁ hz₂
      rcases mem_flatMapList_iff.mp hz₁ with ⟨f₁, _, hzf₁⟩
      rcases mem_flatMapList_iff.mp hz₂ with ⟨g₁, _, hzg₁⟩
      split at hzf₁ <;> split at hzg₁
      · rcases List.mem_singleton.mp hzf₁ with rfl
        rcases List.mem_singleton.mp hzg₁ with heq
        have hlo : lowFD (mergeFD f₀ f₁ ‹_›) = lowFD (mergeFD g₀ g₁ ‹_›) := by rw [heq]
        rw [lowFD_mergeFD, lowFD_mergeFD] at hlo
        exact hlo
      · nomatch hzg₁
      · nomatch hzf₁
      · nomatch hzf₁

/-- Constructive duplicate-free enumeration of `FD0 n`. -/
def allFD0 (n : Nat) : List (FD0 n) :=
  flatMapList (fun f =>
    if h : f.val (botCube n) = false ∧ f.val (topCube n) = true then [⟨f, h⟩] else [])
  (allFD n)

theorem mem_allFD0 {n : Nat} (f : FD0 n) : f ∈ allFD0 n := by
  unfold allFD0
  rw [mem_flatMapList_iff]
  refine ⟨f.val, mem_allFD f.val, ?_⟩
  simp only [f.property, and_self, ↓reduceDIte, List.mem_singleton]
  exact fd0_ext rfl

theorem noDup_allFD0 (n : Nat) : NoDup (allFD0 n) := by
  unfold allFD0
  apply noDup_flatMapList (noDup_allFD n)
  · intro f _
    split
    · exact noDup_singleton _
    · exact noDup_nil
  · intro f _ g _ z hzf hzg
    split at hzf <;> split at hzg
    · rcases List.mem_singleton.mp hzf with rfl
      rcases List.mem_singleton.mp hzg with heq
      exact congrArg Subtype.val heq
    · nomatch hzg
    · nomatch hzf
    · nomatch hzf

/-- First five Dedekind numbers verified directly from `allFD`. -/
theorem card_FD_zero : (allFD 0).length = 2 := rfl
theorem card_FD_one : (allFD 1).length = 3 := rfl
theorem card_FD_two : (allFD 2).length = 6 := rfl
theorem card_FD_three : (allFD 3).length = 20 := by decide

theorem card_FD0_zero : (allFD0 0).length = 0 := rfl
theorem card_FD0_one : (allFD0 1).length = 1 := rfl
theorem card_FD0_two : (allFD0 2).length = 4 := rfl
theorem card_FD0_three : (allFD0 3).length = 18 := by decide

end SpernerFD
