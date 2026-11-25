/-
  Conjecture 00000008543 — Complete Self-Contained Core Lean 4.19.0 Disproof
  ==========================================================================
  Official statement:
    English: Definition: A Boole lattice is a Boolean lattice.
             Conjecture: The automorphism group of a Boolean lattice is the
             symmetric group; its irreducible automorphisms are of transposition
             type; and the isomorphism classification is uniquely determined by
             the dimension. (Boolean lattice automorphism type)
    Chinese: 定义：Boole 格即布尔格。猜想：布尔格的自同构群为对称群；其不可约自同构为
             对换型；同构分类由维数唯一决定。（布尔格自同构型）
-/

namespace Conjecture00000008543

/-! ## Section 1. Bijections, Abstract Groups, and Centers of Symmetric Groups -/

/-- Explicit bijection between two types. -/
structure Equiv (α : Type u) (β : Type v) where
  toFun : α → β
  invFun : β → α
  left_inv : ∀ a : α, invFun (toFun a) = a
  right_inv : ∀ b : β, toFun (invFun b) = b

/-- Permutations of a type `α` (the symmetric group `Sym(α)`). -/
abbrev Perm (α : Type u) := Equiv α α

namespace Equiv

def refl (α : Type u) : Equiv α α where
  toFun a := a
  invFun a := a
  left_inv _ := rfl
  right_inv _ := rfl

def symm {α : Type u} {β : Type v} (e : Equiv α β) : Equiv β α where
  toFun := e.invFun
  invFun := e.toFun
  left_inv := e.right_inv
  right_inv := e.left_inv

def trans {α : Type u} {β : Type v} {γ : Type w}
    (e₁ : Equiv α β) (e₂ : Equiv β γ) : Equiv α γ where
  toFun a := e₂.toFun (e₁.toFun a)
  invFun c := e₁.invFun (e₂.invFun c)
  left_inv a := by rw [e₂.left_inv, e₁.left_inv]
  right_inv c := by rw [e₁.right_inv, e₂.right_inv]

theorem ext {α : Type u} {β : Type v} {e₁ e₂ : Equiv α β}
    (h : ∀ a : α, e₁.toFun a = e₂.toFun a) : e₁ = e₂ := by
  cases e₁ with
  | mk f₁ g₁ l₁ r₁ =>
    cases e₂ with
    | mk f₂ g₂ l₂ r₂ =>
      have hf : f₁ = f₂ := funext h
      subst hf
      have hg : g₁ = g₂ := funext fun b => by
        have h1 : g₁ (f₁ (g₂ b)) = g₂ b := l₁ (g₂ b)
        rw [r₂ b] at h1
        exact h1
      subst hg
      rfl

theorem injective {α : Type u} {β : Type v} (e : Equiv α β)
    {a₁ a₂ : α} (h : e.toFun a₁ = e.toFun a₂) : a₁ = a₂ := by
  have h' := congrArg e.invFun h
  rw [e.left_inv, e.left_inv] at h'
  exact h'

noncomputable def swapFun {α : Type u} (a b x : α) : α :=
  let _ := Classical.propDecidable
  if x = a then b else if x = b then a else x

theorem swapFun_left {α : Type u} (a b : α) : swapFun a b a = b := by
  unfold swapFun
  simp

theorem swapFun_right {α : Type u} (a b : α) : swapFun a b b = a := by
  unfold swapFun
  by_cases h : b = a
  · simp [h]
  · simp [h]

theorem swapFun_of_ne {α : Type u} {a b x : α}
    (hxa : x ≠ a) (hxb : x ≠ b) : swapFun a b x = x := by
  unfold swapFun
  simp [hxa, hxb]

theorem swapFun_involutive {α : Type u} (a b x : α) :
    swapFun a b (swapFun a b x) = x := by
  by_cases hxa : x = a
  · subst hxa; rw [swapFun_left, swapFun_right]
  · by_cases hxb : x = b
    · subst hxb; rw [swapFun_right, swapFun_left]
    · rw [swapFun_of_ne hxa hxb, swapFun_of_ne hxa hxb]

/-- Classical transposition swapping `a` and `b` on any type `α`. -/
noncomputable def swap {α : Type u} (a b : α) : Perm α where
  toFun := swapFun a b
  invFun := swapFun a b
  left_inv := swapFun_involutive a b
  right_inv := swapFun_involutive a b

theorem swap_apply_left {α : Type u} (a b : α) : (swap a b).toFun a = b :=
  swapFun_left a b

theorem swap_apply_right {α : Type u} (a b : α) : (swap a b).toFun b = a :=
  swapFun_right a b

theorem swap_apply_of_ne_of_ne {α : Type u} {a b x : α}
    (hxa : x ≠ a) (hxb : x ≠ b) : (swap a b).toFun x = x :=
  swapFun_of_ne hxa hxb

end Equiv

/-- Standard abstract group structure on a carrier type `G`. -/
structure AbstractGroup (G : Type u) where
  mul : G → G → G
  one : G
  inv : G → G
  mul_assoc : ∀ a b c : G, mul (mul a b) c = mul a (mul b c)
  one_mul : ∀ a : G, mul one a = a
  mul_one : ∀ a : G, mul a one = a
  inv_mul_cancel : ∀ a : G, mul (inv a) a = one

/-- Symmetric group structure `(Perm X, ∘, id, ⁻¹)`. -/
def permGroup (X : Type u) : AbstractGroup (Perm X) where
  mul f g := Equiv.trans g f
  one := Equiv.refl X
  inv f := Equiv.symm f
  mul_assoc _ _ _ := Equiv.ext fun _ => rfl
  one_mul _ := Equiv.ext fun _ => rfl
  mul_one _ := Equiv.ext fun _ => rfl
  inv_mul_cancel f := Equiv.ext fun x => f.left_inv x

/-- Group isomorphism between two abstract groups. -/
structure GroupIso {G : Type u} {H : Type v}
    (grpG : AbstractGroup G) (grpH : AbstractGroup H) extends Equiv G H where
  map_mul : ∀ a b : G, toFun (grpG.mul a b) = grpH.mul (toFun a) (toFun b)

namespace GroupIso

theorem map_one {G : Type u} {H : Type v}
    {grpG : AbstractGroup G} {grpH : AbstractGroup H}
    (iso : GroupIso grpG grpH) : iso.toFun grpG.one = grpH.one := by
  have h1 : grpH.mul (iso.toFun grpG.one) (iso.toFun grpG.one) =
      grpH.mul (iso.toFun grpG.one) grpH.one := by
    rw [← iso.map_mul, grpG.one_mul, grpH.mul_one]
  have h2 := congrArg (grpH.mul (grpH.inv (iso.toFun grpG.one))) h1
  rw [← grpH.mul_assoc, ← grpH.mul_assoc, grpH.inv_mul_cancel,
      grpH.one_mul, grpH.one_mul] at h2
  exact h2

def symm {G : Type u} {H : Type v}
    {grpG : AbstractGroup G} {grpH : AbstractGroup H}
    (iso : GroupIso grpG grpH) : GroupIso grpH grpG where
  toEquiv := iso.toEquiv.symm
  map_mul x y := by
    apply iso.toEquiv.injective
    change iso.toFun (iso.invFun (grpH.mul x y)) =
      iso.toFun (grpG.mul (iso.invFun x) (iso.invFun y))
    rw [iso.right_inv, iso.map_mul, iso.right_inv, iso.right_inv]

end GroupIso

/-- An element `z` belongs to the center `Z(G)` iff it commutes with every element. -/
def IsCentral {G : Type u} (grp : AbstractGroup G) (z : G) : Prop :=
  ∀ g : G, grp.mul z g = grp.mul g z

/-- In `Perm X`, if `X` has at least 3 distinct elements, the center is trivial. -/
theorem perm_center_trivial_of_three {X : Type u} {x₁ x₂ x₃ : X}
    (h12 : x₁ ≠ x₂) (h13 : x₁ ≠ x₃) (h23 : x₂ ≠ x₃)
    {z : Perm X} (hz : IsCentral (permGroup X) z) : z = Equiv.refl X := by
  apply Equiv.ext
  intro x
  cases Classical.em (z.toFun x = x) with
  | inl hfix => exact hfix
  | inr hmov =>
    have hw : ∃ w : X, w ≠ x ∧ w ≠ z.toFun x := by
      cases Classical.em (x₁ = x ∨ x₁ = z.toFun x) with
      | inr h1 => exact ⟨x₁, fun h => h1 (Or.inl h), fun h => h1 (Or.inr h)⟩
      | inl h1 =>
        cases Classical.em (x₂ = x ∨ x₂ = z.toFun x) with
        | inr h2 => exact ⟨x₂, fun h => h2 (Or.inl h), fun h => h2 (Or.inr h)⟩
        | inl h2 =>
          refine ⟨x₃, ?_, ?_⟩
          · intro hx3
            cases h1 with
            | inl hx1 => exact h13 (hx1.trans hx3.symm)
            | inr hz1 =>
              cases h2 with
              | inl hx2 => exact h23 (hx2.trans hx3.symm)
              | inr hz2 => exact h12 (hz1.trans hz2.symm)
          · intro hz3
            cases h1 with
            | inr hz1 => exact h13 (hz1.trans hz3.symm)
            | inl hx1 =>
              cases h2 with
              | inr hz2 => exact h23 (hz2.trans hz3.symm)
              | inl hx2 => exact h12 (hx1.trans hx2.symm)
    rcases hw with ⟨w, hwx, hwz⟩
    let τ := Equiv.swap (z.toFun x) w
    have hcomm := congrArg (fun p : Perm X => p.toFun x) (hz τ)
    change z.toFun (τ.toFun x) = τ.toFun (z.toFun x) at hcomm
    have hτx : τ.toFun x = x :=
      Equiv.swap_apply_of_ne_of_ne (fun h => hmov h.symm) hwx.symm
    have hτzx : τ.toFun (z.toFun x) = w := Equiv.swap_apply_left (z.toFun x) w
    rw [hτx, hτzx] at hcomm
    exact False.elim (hwz hcomm.symm)

/-- If `X` has no 3 pairwise distinct elements, `Perm X` cannot have 3 distinct elements. -/
theorem perm_no_three_distinct_of_at_most_two {X : Type u}
    (hX : ¬ ∃ x₁ x₂ x₃ : X, x₁ ≠ x₂ ∧ x₁ ≠ x₃ ∧ x₂ ≠ x₃)
    {g₁ g₂ g₃ : Perm X} (h12 : g₁ ≠ g₂) (h13 : g₁ ≠ g₃) (h23 : g₂ ≠ g₃) : False := by
  have hex : ∃ a : X, g₁.toFun a ≠ g₂.toFun a := by
    cases Classical.em (∃ a : X, g₁.toFun a ≠ g₂.toFun a) with
    | inl h => exact h
    | inr h =>
      apply False.elim (h12 (Equiv.ext fun a => ?_))
      cases Classical.em (g₁.toFun a = g₂.toFun a) with
      | inl ha => exact ha
      | inr ha => exact False.elim (h ⟨a, ha⟩)
  rcases hex with ⟨a, hab⟩
  let b := g₁.toFun a
  let c := g₂.toFun a
  have hbc : b ≠ c := hab
  have hall : ∀ x : X, x = b ∨ x = c := fun x => by
    cases Classical.em (x = b) with
    | inl hxb => exact Or.inl hxb
    | inr hxb =>
      cases Classical.em (x = c) with
      | inl hxc => exact Or.inr hxc
      | inr hxc => exact False.elim (hX ⟨b, c, x, hbc, Ne.symm hxb, Ne.symm hxc⟩)
  have eq_of_eq_at_a : ∀ p q : Perm X, p.toFun a = q.toFun a → p = q := by
    intro p q hpa
    apply Equiv.ext
    intro x
    let target : X :=
      let _ := Classical.propDecidable
      if p.toFun a = b then c else b
    have htarget_ne : target ≠ p.toFun a := by
      dsimp only [target]
      by_cases hpab : p.toFun a = b
      · simp [hpab, hbc.symm]
      · simp [hpab, Ne.symm hpab]
    let d := p.invFun target
    have had : d ≠ a := by
      intro hda
      have hpd := congrArg p.toFun hda
      rw [p.right_inv] at hpd
      exact htarget_ne hpd
    have hxa_or_xd : x = a ∨ x = d := by
      cases Classical.em (x = a) with
      | inl h1 => exact Or.inl h1
      | inr h1 =>
        cases Classical.em (x = d) with
        | inl h2 => exact Or.inr h2
        | inr h2 => exact False.elim (hX ⟨a, d, x, had.symm, Ne.symm h1, Ne.symm h2⟩)
    cases hxa_or_xd with
    | inl hxa => subst hxa; exact hpa
    | inr hxd =>
      subst hxd
      have hpd_ne : p.toFun d ≠ p.toFun a := fun h => had (p.injective h)
      have hqd_ne : q.toFun d ≠ q.toFun a := fun h => had (q.injective h)
      rw [hpa] at hpd_ne
      cases hall (p.toFun d) with
      | inl hpb =>
        cases hall (q.toFun d) with
        | inl hqb => exact hpb.trans hqb.symm
        | inr hqc =>
          cases hall (q.toFun a) with
          | inl hqab => exact False.elim (hpd_ne (hpb.trans hqab.symm))
          | inr hqac => exact False.elim (hqd_ne (hqc.trans hqac.symm))
      | inr hpc =>
        cases hall (q.toFun d) with
        | inr hqc => exact hpc.trans hqc.symm
        | inl hqb =>
          cases hall (q.toFun a) with
          | inl hqab => exact False.elim (hqd_ne (hqb.trans hqab.symm))
          | inr hqac => exact False.elim (hpd_ne (hpc.trans hqac.symm))
  cases hall (g₃.toFun a) with
  | inl hg3b => exact h13 (eq_of_eq_at_a g₁ g₃ hg3b.symm)
  | inr hg3c => exact h23 (eq_of_eq_at_a g₂ g₃ hg3c.symm)

/-- Fundamental Group-Theoretic Obstruction:
    No group `G` having a non-identity central element `z` AND at least 3 distinct
    elements (`1, z, w`) can be isomorphic to `Perm X` for ANY type `X : Type u`. -/
theorem not_groupIso_perm_of_nontrivial_center_and_three
    {G : Type v} (grp : AbstractGroup G)
    {z w : G} (hz_cent : IsCentral grp z)
    (hz_ne_one : z ≠ grp.one) (hw_ne_one : w ≠ grp.one) (hw_ne_z : w ≠ z)
    (X : Type u) : ¬ Nonempty (GroupIso grp (permGroup X)) := by
  intro ⟨iso⟩
  cases Classical.em (∃ x₁ x₂ x₃ : X, x₁ ≠ x₂ ∧ x₁ ≠ x₃ ∧ x₂ ≠ x₃) with
  | inl h3 =>
    rcases h3 with ⟨x₁, x₂, x₃, h12, h13, h23⟩
    have hz'_cent : IsCentral (permGroup X) (iso.toFun z) := by
      intro p
      have h := iso.map_mul z (iso.invFun p)
      have h' := iso.map_mul (iso.invFun p) z
      rw [hz_cent (iso.invFun p)] at h
      rw [iso.right_inv] at h h'
      exact h.symm.trans h'
    have hz'_one : iso.toFun z = (permGroup X).one :=
      perm_center_trivial_of_three h12 h13 h23 hz'_cent
    rw [← iso.map_one] at hz'_one
    exact hz_ne_one (iso.toEquiv.injective hz'_one)
  | inr hno3 =>
    have h12 : iso.toFun grp.one ≠ iso.toFun z :=
      fun h => hz_ne_one (iso.toEquiv.injective h).symm
    have h13 : iso.toFun grp.one ≠ iso.toFun w :=
      fun h => hw_ne_one (iso.toEquiv.injective h).symm
    have h23 : iso.toFun z ≠ iso.toFun w :=
      fun h => hw_ne_z (iso.toEquiv.injective h).symm
    exact perm_no_three_distinct_of_at_most_two hno3 h12 h13 h23


/-! ## Section 2. Boolean Lattices, Automorphisms, Atoms, and Direct Products -/

/-- Exact textbook axiomatization of a Boolean lattice (Boole lattice / 布尔格):
    a bounded, distributive, complemented lattice `(L, ≤, ⊥, ⊤, ∧, ∨, ᶜ)`. -/
structure BooleanLattice (L : Type u) where
  le : L → L → Prop
  le_refl : ∀ x : L, le x x
  le_trans : ∀ {x y z : L}, le x y → le y z → le x z
  le_antisymm : ∀ {x y : L}, le x y → le y x → x = y
  bot : L
  top : L
  bot_le : ∀ x : L, le bot x
  le_top : ∀ x : L, le x top
  inf : L → L → L
  inf_le_left : ∀ x y : L, le (inf x y) x
  inf_le_right : ∀ x y : L, le (inf x y) y
  le_inf : ∀ {z x y : L}, le z x → le z y → le z (inf x y)
  sup : L → L → L
  le_sup_left : ∀ x y : L, le x (sup x y)
  le_sup_right : ∀ x y : L, le y (sup x y)
  sup_le : ∀ {x y z : L}, le x z → le y z → le (sup x y) z
  inf_sup_left : ∀ x y z : L, inf x (sup y z) = sup (inf x y) (inf x z)
  compl : L → L
  inf_compl : ∀ x : L, inf x (compl x) = bot
  sup_compl : ∀ x : L, sup x (compl x) = top

namespace BooleanLattice

variable {L : Type u} (bl : BooleanLattice L)

theorem inf_comm (x y : L) : bl.inf x y = bl.inf y x :=
  bl.le_antisymm
    (bl.le_inf (bl.inf_le_right x y) (bl.inf_le_left x y))
    (bl.le_inf (bl.inf_le_right y x) (bl.inf_le_left y x))

theorem sup_comm (x y : L) : bl.sup x y = bl.sup y x :=
  bl.le_antisymm
    (bl.sup_le (bl.le_sup_right y x) (bl.le_sup_left y x))
    (bl.sup_le (bl.le_sup_right x y) (bl.le_sup_left x y))

theorem inf_idem (x : L) : bl.inf x x = x :=
  bl.le_antisymm (bl.inf_le_left x x) (bl.le_inf (bl.le_refl x) (bl.le_refl x))

theorem sup_idem (x : L) : bl.sup x x = x :=
  bl.le_antisymm (bl.sup_le (bl.le_refl x) (bl.le_refl x)) (bl.le_sup_left x x)

theorem inf_bot_right (x : L) : bl.inf x bl.bot = bl.bot :=
  bl.le_antisymm (bl.inf_le_right x bl.bot) (bl.bot_le _)

theorem inf_top_right (x : L) : bl.inf x bl.top = x :=
  bl.le_antisymm (bl.inf_le_left x bl.top) (bl.le_inf (bl.le_refl x) (bl.le_top x))

theorem sup_bot_right (x : L) : bl.sup x bl.bot = x :=
  bl.le_antisymm (bl.sup_le (bl.le_refl x) (bl.bot_le x)) (bl.le_sup_left x bl.bot)

theorem sup_bot_left (x : L) : bl.sup bl.bot x = x := by
  rw [bl.sup_comm, bl.sup_bot_right]

theorem inf_top_left (x : L) : bl.inf bl.top x = x := by
  rw [bl.inf_comm, bl.inf_top_right]

theorem inf_assoc (x y z : L) : bl.inf (bl.inf x y) z = bl.inf x (bl.inf y z) := by
  apply bl.le_antisymm
  · refine bl.le_inf (bl.le_trans (bl.inf_le_left _ _) (bl.inf_le_left _ _)) ?_
    exact bl.le_inf (bl.le_trans (bl.inf_le_left _ _) (bl.inf_le_right _ _)) (bl.inf_le_right _ _)
  · refine bl.le_inf ?_ (bl.le_trans (bl.inf_le_right _ _) (bl.inf_le_right _ _))
    exact bl.le_inf (bl.inf_le_left _ _) (bl.le_trans (bl.inf_le_right _ _) (bl.inf_le_left _ _))

theorem sup_assoc (x y z : L) : bl.sup (bl.sup x y) z = bl.sup x (bl.sup y z) := by
  apply bl.le_antisymm
  · refine bl.sup_le ?_ (bl.le_trans (bl.le_sup_right _ _) (bl.le_sup_right _ _))
    exact bl.sup_le (bl.le_sup_left _ _) (bl.le_trans (bl.le_sup_left _ _) (bl.le_sup_right _ _))
  · refine bl.sup_le (bl.le_trans (bl.le_sup_left _ _) (bl.le_sup_left _ _)) ?_
    exact bl.sup_le (bl.le_trans (bl.le_sup_right _ _) (bl.le_sup_left _ _)) (bl.le_sup_right _ _)

theorem inf_sup_self (x y : L) : bl.inf x (bl.sup x y) = x :=
  bl.le_antisymm (bl.inf_le_left _ _) (bl.le_inf (bl.le_refl x) (bl.le_sup_left x y))

theorem sup_inf_self (x y : L) : bl.sup x (bl.inf x y) = x :=
  bl.le_antisymm (bl.sup_le (bl.le_refl x) (bl.inf_le_left x y)) (bl.le_sup_left _ _)

theorem inf_sup_right (x y z : L) : bl.inf (bl.sup x y) z = bl.sup (bl.inf x z) (bl.inf y z) := by
  rw [bl.inf_comm, bl.inf_sup_left, bl.inf_comm z x, bl.inf_comm z y]

/-- Dual distributivity `x ∨ (y ∧ z) = (x ∨ y) ∧ (x ∨ z)` follows from `inf_sup_left`. -/
theorem sup_inf_left (x y z : L) : bl.sup x (bl.inf y z) = bl.inf (bl.sup x y) (bl.sup x z) := by
  rw [bl.inf_sup_left (bl.sup x y) x z, bl.inf_comm (bl.sup x y) x, bl.inf_sup_self x y,
      bl.inf_sup_right x y z, ← bl.sup_assoc, bl.sup_inf_self x z]

/-- Uniqueness of complements in any bounded distributive lattice. -/
theorem compl_unique {x y : L} (hinf : bl.inf x y = bl.bot) (hsup : bl.sup x y = bl.top) :
    y = bl.compl x := by
  have h1 : y = bl.inf y (bl.sup x (bl.compl x)) := by rw [bl.sup_compl, bl.inf_top_right]
  rw [bl.inf_sup_left, bl.inf_comm y x, hinf, bl.sup_bot_left] at h1
  have h2 : bl.compl x = bl.inf (bl.compl x) (bl.sup x y) := by rw [hsup, bl.inf_top_right]
  rw [bl.inf_sup_left, bl.inf_comm (bl.compl x) x, bl.inf_compl, bl.sup_bot_left,
      bl.inf_comm] at h2
  exact h1.trans h2.symm

theorem compl_compl (x : L) : bl.compl (bl.compl x) = x := by
  symm
  apply bl.compl_unique
  · rw [bl.inf_comm, bl.inf_compl]
  · rw [bl.sup_comm, bl.sup_compl]

theorem le_iff_inf_eq (x y : L) : bl.le x y ↔ bl.inf x y = x := by
  constructor
  · intro h
    exact bl.le_antisymm (bl.inf_le_left x y) (bl.le_inf (bl.le_refl x) h)
  · intro h
    rw [← h]
    exact bl.inf_le_right x y

/-- Decomposition `y = (y ∧ u) ∨ (y ∧ uᶜ)` in any Boolean lattice. -/
theorem decomp_by (y u : L) : y = bl.sup (bl.inf y u) (bl.inf y (bl.compl u)) := by
  rw [← bl.inf_sup_left, bl.sup_compl, bl.inf_top_right]

/-- Symmetric difference `x △ y = (x ∧ yᶜ) ∨ (xᶜ ∧ y)` (Boolean ring addition). -/
def symmDiff (x y : L) : L :=
  bl.sup (bl.inf x (bl.compl y)) (bl.inf (bl.compl x) y)

/-- Strict order `x < y`. -/
def Lt (x y : L) : Prop := bl.le x y ∧ x ≠ y

/-- Atom of a Boolean lattice: minimal nonzero element. -/
def IsAtom (a : L) : Prop :=
  a ≠ bl.bot ∧ ∀ x : L, bl.le x a → x = bl.bot ∨ x = a

/-- Type of atoms of `bl`. -/
def Atoms := { a : L // bl.IsAtom a }

/-- A Boolean lattice is atomic if every nonzero element lies above an atom. -/
def IsAtomic : Prop :=
  ∀ x : L, x ≠ bl.bot → ∃ a : L, bl.IsAtom a ∧ bl.le a x

/-- A Boolean lattice is atomless if it possesses no atoms at all. -/
def IsAtomless : Prop :=
  ∀ a : L, ¬ bl.IsAtom a

end BooleanLattice

/-- Isomorphism of Boolean lattices: an order-preserving and order-reflecting bijection. -/
structure BLIso {L₁ : Type u} {L₂ : Type v}
    (bl₁ : BooleanLattice L₁) (bl₂ : BooleanLattice L₂) extends Equiv L₁ L₂ where
  map_le : ∀ x y : L₁, bl₂.le (toFun x) (toFun y) ↔ bl₁.le x y

/-- Automorphism of a Boolean lattice `bl`. -/
abbrev BLAut {L : Type u} (bl : BooleanLattice L) := BLIso bl bl

namespace BLIso

variable {L₁ : Type u} {L₂ : Type v}
  {bl₁ : BooleanLattice L₁} {bl₂ : BooleanLattice L₂}

def refl (bl : BooleanLattice L₁) : BLAut bl where
  toEquiv := Equiv.refl L₁
  map_le _ _ := Iff.rfl

def symm (f : BLIso bl₁ bl₂) : BLIso bl₂ bl₁ where
  toEquiv := f.toEquiv.symm
  map_le x y := by
    have h := f.map_le (f.invFun x) (f.invFun y)
    rw [f.right_inv, f.right_inv] at h
    exact h.symm

def trans {L₃ : Type w} {bl₃ : BooleanLattice L₃}
    (f : BLIso bl₁ bl₂) (g : BLIso bl₂ bl₃) : BLIso bl₁ bl₃ where
  toEquiv := Equiv.trans f.toEquiv g.toEquiv
  map_le x y := (g.map_le _ _).trans (f.map_le x y)

theorem ext {f g : BLIso bl₁ bl₂} (h : ∀ x : L₁, f.toFun x = g.toFun x) : f = g := by
  cases f with
  | mk ef lf =>
    cases g with
    | mk eg lg =>
      have he : ef = eg := Equiv.ext h
      subst he
      rfl

theorem map_bot (f : BLIso bl₁ bl₂) : f.toFun bl₁.bot = bl₂.bot := by
  apply bl₂.le_antisymm ?_ (bl₂.bot_le _)
  have h : bl₁.le bl₁.bot (f.invFun bl₂.bot) := bl₁.bot_le _
  rw [← f.map_le, f.right_inv] at h
  exact h

theorem map_top (f : BLIso bl₁ bl₂) : f.toFun bl₁.top = bl₂.top := by
  apply bl₂.le_antisymm (bl₂.le_top _) ?_
  have h : bl₁.le (f.invFun bl₂.top) bl₁.top := bl₁.le_top _
  rw [← f.map_le, f.right_inv] at h
  exact h

theorem map_inf (f : BLIso bl₁ bl₂) (x y : L₁) :
    f.toFun (bl₁.inf x y) = bl₂.inf (f.toFun x) (f.toFun y) := by
  apply bl₂.le_antisymm
  · exact bl₂.le_inf ((f.map_le _ _).mpr (bl₁.inf_le_left x y))
      ((f.map_le _ _).mpr (bl₁.inf_le_right x y))
  · have h1 : bl₂.le (bl₂.inf (f.toFun x) (f.toFun y)) (f.toFun x) := bl₂.inf_le_left _ _
    have h2 : bl₂.le (bl₂.inf (f.toFun x) (f.toFun y)) (f.toFun y) := bl₂.inf_le_right _ _
    let w := f.invFun (bl₂.inf (f.toFun x) (f.toFun y))
    have hw1 : bl₁.le w x := (f.map_le w x).mp (by dsimp [w]; rw [f.right_inv]; exact h1)
    have hw2 : bl₁.le w y := (f.map_le w y).mp (by dsimp [w]; rw [f.right_inv]; exact h2)
    have hw : bl₁.le w (bl₁.inf x y) := bl₁.le_inf hw1 hw2
    have hfw := (f.map_le w (bl₁.inf x y)).mpr hw
    dsimp [w] at hfw
    rw [f.right_inv] at hfw
    exact hfw

theorem map_sup (f : BLIso bl₁ bl₂) (x y : L₁) :
    f.toFun (bl₁.sup x y) = bl₂.sup (f.toFun x) (f.toFun y) := by
  apply bl₂.le_antisymm
  · have h1 : bl₂.le (f.toFun x) (bl₂.sup (f.toFun x) (f.toFun y)) := bl₂.le_sup_left _ _
    have h2 : bl₂.le (f.toFun y) (bl₂.sup (f.toFun x) (f.toFun y)) := bl₂.le_sup_right _ _
    let w := f.invFun (bl₂.sup (f.toFun x) (f.toFun y))
    have hw1 : bl₁.le x w := (f.map_le x w).mp (by dsimp [w]; rw [f.right_inv]; exact h1)
    have hw2 : bl₁.le y w := (f.map_le y w).mp (by dsimp [w]; rw [f.right_inv]; exact h2)
    have hw : bl₁.le (bl₁.sup x y) w := bl₁.sup_le hw1 hw2
    have hfw := (f.map_le (bl₁.sup x y) w).mpr hw
    dsimp [w] at hfw
    rw [f.right_inv] at hfw
    exact hfw
  · exact bl₂.sup_le ((f.map_le _ _).mpr (bl₁.le_sup_left x y))
      ((f.map_le _ _).mpr (bl₁.le_sup_right x y))

theorem map_compl (f : BLIso bl₁ bl₂) (x : L₁) :
    f.toFun (bl₁.compl x) = bl₂.compl (f.toFun x) := by
  apply bl₂.compl_unique
  · rw [← f.map_inf, bl₁.inf_compl, f.map_bot]
  · rw [← f.map_sup, bl₁.sup_compl, f.map_top]

theorem map_symmDiff (f : BLIso bl₁ bl₂) (x y : L₁) :
    f.toFun (bl₁.symmDiff x y) = bl₂.symmDiff (f.toFun x) (f.toFun y) := by
  unfold BooleanLattice.symmDiff
  rw [f.map_sup, f.map_inf, f.map_inf, f.map_compl, f.map_compl]

theorem map_isAtom (f : BLIso bl₁ bl₂) {a : L₁} (ha : bl₁.IsAtom a) :
    bl₂.IsAtom (f.toFun a) := by
  constructor
  · intro hbot
    rw [← f.map_bot] at hbot
    exact ha.1 (f.toEquiv.injective hbot)
  · intro y hy
    have hinv : bl₁.le (f.invFun y) a := by
      rw [← f.map_le, f.right_inv]
      exact hy
    cases ha.2 (f.invFun y) hinv with
    | inl h0 =>
      left
      have := congrArg f.toFun h0
      rw [f.right_inv, f.map_bot] at this
      exact this
    | inr h1 =>
      right
      have := congrArg f.toFun h1
      rw [f.right_inv] at this
      exact this

/-- Every Boolean lattice isomorphism induces a bijection between the atom sets. -/
def atomEquiv (f : BLIso bl₁ bl₂) : Equiv bl₁.Atoms bl₂.Atoms where
  toFun a := ⟨f.toFun a.1, f.map_isAtom a.2⟩
  invFun b := ⟨f.symm.toFun b.1, f.symm.map_isAtom b.2⟩
  left_inv a := Subtype.ext (f.left_inv a.1)
  right_inv b := Subtype.ext (f.right_inv b.1)

end BLIso

/-- Equivalence Theorem: A bijection `e : Equiv L₁ L₂` is a Boolean-lattice
    order isomorphism iff it is a Boolean-algebra homomorphism preserving
    `(⊥, ⊤, ∧, ∨, ᶜ)`. -/
theorem blIso_iff_algHom {L₁ : Type u} {L₂ : Type v}
    (bl₁ : BooleanLattice L₁) (bl₂ : BooleanLattice L₂) (e : Equiv L₁ L₂) :
    (∀ x y : L₁, bl₂.le (e.toFun x) (e.toFun y) ↔ bl₁.le x y) ↔
    (e.toFun bl₁.bot = bl₂.bot ∧
     e.toFun bl₁.top = bl₂.top ∧
     (∀ x y, e.toFun (bl₁.inf x y) = bl₂.inf (e.toFun x) (e.toFun y)) ∧
     (∀ x y, e.toFun (bl₁.sup x y) = bl₂.sup (e.toFun x) (e.toFun y)) ∧
     (∀ x, e.toFun (bl₁.compl x) = bl₂.compl (e.toFun x))) := by
  constructor
  · intro hle
    let iso : BLIso bl₁ bl₂ := ⟨e, hle⟩
    exact ⟨iso.map_bot, iso.map_top, iso.map_inf, iso.map_sup, iso.map_compl⟩
  · rintro ⟨_, _, hinf, _, _⟩ x y
    rw [bl₂.le_iff_inf_eq, bl₁.le_iff_inf_eq, ← hinf]
    exact ⟨fun h => e.injective h, fun h => congrArg e.toFun h⟩

/-- Group structure `(Aut(L), ∘, id, ⁻¹)` on the automorphisms of a Boolean lattice. -/
def blAutGroup {L : Type u} (bl : BooleanLattice L) : AbstractGroup (BLAut bl) where
  mul f g := BLIso.trans g f
  one := BLIso.refl bl
  inv f := BLIso.symm f
  mul_assoc _ _ _ := BLIso.ext fun _ => rfl
  one_mul _ := BLIso.ext fun _ => rfl
  mul_one _ := BLIso.ext fun _ => rfl
  inv_mul_cancel f := BLIso.ext fun x => f.left_inv x

/-- Direct product `L₁ × L₂` of two Boolean lattices. -/
def prodBL {L₁ : Type u} {L₂ : Type v}
    (bl₁ : BooleanLattice L₁) (bl₂ : BooleanLattice L₂) : BooleanLattice (L₁ × L₂) where
  le p q := bl₁.le p.1 q.1 ∧ bl₂.le p.2 q.2
  le_refl p := ⟨bl₁.le_refl p.1, bl₂.le_refl p.2⟩
  le_trans h1 h2 := ⟨bl₁.le_trans h1.1 h2.1, bl₂.le_trans h1.2 h2.2⟩
  le_antisymm h1 h2 := Prod.ext (bl₁.le_antisymm h1.1 h2.1) (bl₂.le_antisymm h1.2 h2.2)
  bot := (bl₁.bot, bl₂.bot)
  top := (bl₁.top, bl₂.top)
  bot_le p := ⟨bl₁.bot_le p.1, bl₂.bot_le p.2⟩
  le_top p := ⟨bl₁.le_top p.1, bl₂.le_top p.2⟩
  inf p q := (bl₁.inf p.1 q.1, bl₂.inf p.2 q.2)
  inf_le_left p q := ⟨bl₁.inf_le_left p.1 q.1, bl₂.inf_le_left p.2 q.2⟩
  inf_le_right p q := ⟨bl₁.inf_le_right p.1 q.1, bl₂.inf_le_right p.2 q.2⟩
  le_inf h1 h2 := ⟨bl₁.le_inf h1.1 h2.1, bl₂.le_inf h1.2 h2.2⟩
  sup p q := (bl₁.sup p.1 q.1, bl₂.sup p.2 q.2)
  le_sup_left p q := ⟨bl₁.le_sup_left p.1 q.1, bl₂.le_sup_left p.2 q.2⟩
  le_sup_right p q := ⟨bl₁.le_sup_right p.1 q.1, bl₂.le_sup_right p.2 q.2⟩
  sup_le h1 h2 := ⟨bl₁.sup_le h1.1 h2.1, bl₂.sup_le h1.2 h2.2⟩
  inf_sup_left p q r := Prod.ext (bl₁.inf_sup_left p.1 q.1 r.1) (bl₂.inf_sup_left p.2 q.2 r.2)
  compl p := (bl₁.compl p.1, bl₂.compl p.2)
  inf_compl p := Prod.ext (bl₁.inf_compl p.1) (bl₂.inf_compl p.2)
  sup_compl p := Prod.ext (bl₁.sup_compl p.1) (bl₂.sup_compl p.2)


/-! ## Section 3. Level A — Finite Boolean Lattices `B_n` (`FinBool n`) -/

/-- Carrier of the finite Boolean lattice `B_n = P({0, ..., n-1})`. -/
abbrev FinBool (n : Nat) := Fin n → Bool

/-- Standard order `false ≤ true` on `Bool`. -/
def boolLe (b₁ b₂ : Bool) : Prop := b₁ = true → b₂ = true

theorem boolLe_antisymm {a b : Bool} (h1 : boolLe a b) (h2 : boolLe b a) : a = b := by
  unfold boolLe at h1 h2
  cases a <;> cases b <;> simp_all

theorem boolLe_and {c a b : Bool} (h1 : boolLe c a) (h2 : boolLe c b) : boolLe c (a && b) := by
  unfold boolLe at *
  cases c <;> cases a <;> cases b <;> simp_all

theorem boolLe_or {a b c : Bool} (h1 : boolLe a c) (h2 : boolLe b c) : boolLe (a || b) c := by
  unfold boolLe at *
  cases a <;> cases b <;> cases c <;> simp_all

theorem bool_and_or (a b c : Bool) : (a && (b || c)) = ((a && b) || (a && c)) := by
  cases a <;> cases b <;> cases c <;> rfl

/-- Finite Boolean lattice `B_n` of dimension `n`. -/
def finBoolBL (n : Nat) : BooleanLattice (FinBool n) where
  le x y := ∀ i : Fin n, boolLe (x i) (y i)
  le_refl _ _ h := h
  le_trans h1 h2 i h := h2 i (h1 i h)
  le_antisymm h1 h2 := funext fun i => boolLe_antisymm (h1 i) (h2 i)
  bot _ := false
  top _ := true
  bot_le _ _ h := Bool.noConfusion h
  le_top _ _ _ := rfl
  inf x y i := x i && y i
  inf_le_left x y i := by unfold boolLe; cases x i <;> cases y i <;> decide
  inf_le_right x y i := by unfold boolLe; cases x i <;> cases y i <;> decide
  le_inf h1 h2 i := boolLe_and (h1 i) (h2 i)
  sup x y i := x i || y i
  le_sup_left x y i := by unfold boolLe; cases x i <;> cases y i <;> decide
  le_sup_right x y i := by unfold boolLe; cases x i <;> cases y i <;> decide
  sup_le h1 h2 i := boolLe_or (h1 i) (h2 i)
  inf_sup_left x y z := funext fun i => bool_and_or (x i) (y i) (z i)
  compl x i := !x i
  inf_compl x := funext fun i => by change (x i && !(x i)) = false; cases x i <;> rfl
  sup_compl x := funext fun i => by change (x i || !(x i)) = true; cases x i <;> rfl

/-- Standard `i`-th atom `e_i` of `FinBool n`. -/
def atomVec {n : Nat} (i : Fin n) : FinBool n :=
  fun j => decide (j = i)

theorem atomVec_self {n : Nat} (i : Fin n) : atomVec i i = true :=
  decide_eq_true rfl

theorem atomVec_ne {n : Nat} {i j : Fin n} (h : j ≠ i) : atomVec i j = false :=
  decide_eq_false h

theorem atomVec_injective {n : Nat} {i₁ i₂ : Fin n}
    (h : atomVec i₁ = atomVec i₂) : i₁ = i₂ := by
  have hi := congrFun h i₁
  rw [atomVec_self] at hi
  by_cases heq : i₁ = i₂
  · exact heq
  · rw [atomVec_ne heq] at hi
    exact Bool.noConfusion hi

/-- Coordinate membership `x i = true` is equivalent to `atomVec i ≤ x`. -/
theorem atomVec_le_iff {n : Nat} (i : Fin n) (x : FinBool n) :
    (finBoolBL n).le (atomVec i) x ↔ x i = true := by
  constructor
  · intro h
    exact h i (atomVec_self i)
  · intro hxi j hj
    unfold atomVec at hj
    by_cases hji : j = i
    · subst hji; exact hxi
    · rw [decide_eq_false hji] at hj
      exact Bool.noConfusion hj

theorem isAtom_atomVec {n : Nat} (i : Fin n) : (finBoolBL n).IsAtom (atomVec i) := by
  constructor
  · intro hbot
    have := congrFun hbot i
    rw [atomVec_self] at this
    exact Bool.noConfusion this
  · intro x hx
    cases hxi : x i with
    | false =>
      left
      funext j
      by_cases hji : j = i
      · subst hji; exact hxi
      · cases hxj : x j with
        | false => rfl
        | true =>
          have h1 := hx j hxj
          rw [atomVec_ne hji] at h1
          exact Bool.noConfusion h1
    | true =>
      right
      funext j
      by_cases hji : j = i
      · subst hji; rw [atomVec_self]; exact hxi
      · cases hxj : x j with
        | false => exact (atomVec_ne hji).symm
        | true =>
          have h1 := hx j hxj
          rw [atomVec_ne hji] at h1
          exact Bool.noConfusion h1

theorem exists_true_of_ne_bot {n : Nat} {x : FinBool n}
    (hx : x ≠ (finBoolBL n).bot) : ∃ i : Fin n, x i = true := by
  cases Classical.em (∃ i : Fin n, x i = true) with
  | inl h => exact h
  | inr h =>
    apply False.elim (hx (funext fun i => ?_))
    cases hxi : x i with
    | false => rfl
    | true => exact False.elim (h ⟨i, hxi⟩)

theorem isAtom_finBool_iff {n : Nat} (x : FinBool n) :
    (finBoolBL n).IsAtom x ↔ ∃ i : Fin n, x = atomVec i := by
  constructor
  · intro hx
    rcases exists_true_of_ne_bot hx.1 with ⟨i, hxi⟩
    have hle : (finBoolBL n).le (atomVec i) x := (atomVec_le_iff i x).mpr hxi
    cases hx.2 (atomVec i) hle with
    | inl hbot => exact False.elim ((isAtom_atomVec i).1 hbot)
    | inr heq => exact ⟨i, heq.symm⟩
  · rintro ⟨i, rfl⟩
    exact isAtom_atomVec i

theorem finBool_isAtomic (n : Nat) : (finBoolBL n).IsAtomic := by
  intro x hx
  rcases exists_true_of_ne_bot hx with ⟨i, hxi⟩
  exact ⟨atomVec i, isAtom_atomVec i, (atomVec_le_iff i x).mpr hxi⟩

/-- Explicit bijection `Fin n ≃ Atoms (FinBool n)`: atom dimension of `B_n` is `n`. -/
noncomputable def finBoolAtomsEquiv (n : Nat) : Equiv (Fin n) (finBoolBL n).Atoms where
  toFun i := ⟨atomVec i, isAtom_atomVec i⟩
  invFun a := Classical.choose ((isAtom_finBool_iff a.1).mp a.2)
  left_inv i := by
    have h := Classical.choose_spec ((isAtom_finBool_iff (atomVec i)).mp (isAtom_atomVec i))
    exact atomVec_injective h.symm
  right_inv a := by
    apply Subtype.ext
    exact (Classical.choose_spec ((isAtom_finBool_iff a.1).mp a.2)).symm

/-- Every permutation `π ∈ Perm (Fin n)` induces an automorphism of `FinBool n`. -/
def permToAut {n : Nat} (π : Perm (Fin n)) : BLAut (finBoolBL n) where
  toFun x j := x (π.invFun j)
  invFun x j := x (π.toFun j)
  left_inv x := funext fun j => congrArg x (π.left_inv j)
  right_inv x := funext fun j => congrArg x (π.right_inv j)
  map_le x y := by
    constructor
    · intro h i hxi
      have hj : x (π.invFun (π.toFun i)) = true → y (π.invFun (π.toFun i)) = true := h (π.toFun i)
      rw [π.left_inv] at hj
      exact hj hxi
    · intro h j hxj
      exact h (π.invFun j) hxj

theorem permToAut_atomVec {n : Nat} (π : Perm (Fin n)) (i : Fin n) :
    (permToAut π).toFun (atomVec i) = atomVec (π.toFun i) := by
  funext j
  change decide (π.invFun j = i) = decide (j = π.toFun i)
  by_cases h : π.invFun j = i
  · have hj : j = π.toFun i := by rw [← h, π.right_inv]
    rw [decide_eq_true h, decide_eq_true hj]
  · have hj : j ≠ π.toFun i := fun heq => h (by rw [heq, π.left_inv])
    rw [decide_eq_false h, decide_eq_false hj]

/-- Positive Theorem A1: `Aut(B_n) ≅ Sym(Fin n)` for every finite `n`. -/
noncomputable def finBoolAutGroupIso (n : Nat) :
    GroupIso (blAutGroup (finBoolBL n)) (permGroup (Fin n)) where
  toFun f := Equiv.trans (finBoolAtomsEquiv n)
    (Equiv.trans f.atomEquiv (finBoolAtomsEquiv n).symm)
  invFun π := permToAut π
  left_inv f := by
    apply BLIso.ext
    intro x
    funext j
    -- Compare `(permToAut π).toFun x j` and `f.toFun x j` via `atomVec_le_iff`
    let π := Equiv.trans (finBoolAtomsEquiv n)
      (Equiv.trans f.atomEquiv (finBoolAtomsEquiv n).symm)
    have hπinv : atomVec (π.invFun j) = f.invFun (atomVec j) := by
      have hspec := Classical.choose_spec
        ((isAtom_finBool_iff (f.symm.toFun (atomVec j))).mp
          (f.symm.map_isAtom (isAtom_atomVec j)))
      exact hspec.symm
    have hiff : (permToAut π).toFun x j = true ↔ f.toFun x j = true := by
      unfold permToAut
      dsimp
      rw [← atomVec_le_iff (π.invFun j) x, hπinv, ← atomVec_le_iff j (f.toFun x)]
      have hm := f.map_le (f.invFun (atomVec j)) x
      rw [f.right_inv] at hm
      exact hm.symm
    cases h1 : (permToAut π).toFun x j <;> cases h2 : f.toFun x j <;> simp_all
  right_inv π := by
    apply Equiv.ext
    intro i
    dsimp [Equiv.trans, Equiv.symm, finBoolAtomsEquiv, BLIso.atomEquiv]
    apply atomVec_injective
    have hspec := Classical.choose_spec
      ((isAtom_finBool_iff ((permToAut π).toFun (atomVec i))).mp
        ((permToAut π).map_isAtom (isAtom_atomVec i)))
    rw [← hspec, permToAut_atomVec]
  map_mul f g := by
    apply Equiv.ext
    intro i
    dsimp [blAutGroup, permGroup, Equiv.trans, Equiv.symm, finBoolAtomsEquiv,
      BLIso.atomEquiv, BLIso.trans]
    apply atomVec_injective
    have hg := Classical.choose_spec
      ((isAtom_finBool_iff (g.toFun (atomVec i))).mp (g.map_isAtom (isAtom_atomVec i)))
    let k := Classical.choose
      ((isAtom_finBool_iff (g.toFun (atomVec i))).mp (g.map_isAtom (isAtom_atomVec i)))
    have hfk := Classical.choose_spec
      ((isAtom_finBool_iff (f.toFun (atomVec k))).mp (f.map_isAtom (isAtom_atomVec k)))
    have hfg := Classical.choose_spec
      ((isAtom_finBool_iff (f.toFun (g.toFun (atomVec i)))).mp
        ((BLIso.trans g f).map_isAtom (isAtom_atomVec i)))
    change atomVec _ = atomVec _
    rw [← hfg, ← hfk]
    exact congrArg f.toFun hg

/-- Pigeonhole theorem for `Fin`: `Equiv (Fin m) (Fin n)` implies `m = n`. -/
theorem fin_equiv_eq : ∀ {m n : Nat}, Equiv (Fin m) (Fin n) → m = n
  | 0, 0, _ => rfl
  | 0, _ + 1, e => Fin.elim0 (e.invFun ⟨0, Nat.succ_pos _⟩)
  | _ + 1, 0, e => Fin.elim0 (e.toFun ⟨0, Nat.succ_pos _⟩)
  | m + 1, n + 1, e => by
    let lastM : Fin (m + 1) := ⟨m, Nat.lt_succ_self m⟩
    let lastN : Fin (n + 1) := ⟨n, Nat.lt_succ_self n⟩
    -- Post-compose `e` with `swap (e lastM) lastN` so `lastM` maps to `lastN`
    let e' : Equiv (Fin (m + 1)) (Fin (n + 1)) :=
      Equiv.trans e (Equiv.swap (e.toFun lastM) lastN)
    have hlast_to : e'.toFun lastM = lastN := by
      dsimp [e', Equiv.trans]
      exact Equiv.swap_apply_left (e.toFun lastM) lastN
    have hlast_inv : e'.invFun lastN = lastM := by
      apply e'.injective
      rw [e'.right_inv, hlast_to]
    have hlt_to : ∀ i : Fin m, (e'.toFun ⟨i.1, Nat.lt_succ_of_lt i.2⟩).1 < n := by
      intro i
      let i' : Fin (m + 1) := ⟨i.1, Nat.lt_succ_of_lt i.2⟩
      have hne : e'.toFun i' ≠ lastN := by
        intro heq
        rw [← hlast_to] at heq
        have hi := e'.injective heq
        have : i.1 = m := congrArg Fin.val hi
        exact Nat.ne_of_lt i.2 this
      have hlt := (e'.toFun i').2
      exact Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hlt) (fun hv => hne (Fin.ext hv))
    have hlt_inv : ∀ j : Fin n, (e'.invFun ⟨j.1, Nat.lt_succ_of_lt j.2⟩).1 < m := by
      intro j
      let j' : Fin (n + 1) := ⟨j.1, Nat.lt_succ_of_lt j.2⟩
      have hne : e'.invFun j' ≠ lastM := by
        intro heq
        have hj := congrArg e'.toFun heq
        rw [e'.right_inv, hlast_to] at hj
        have : j.1 = n := congrArg Fin.val hj
        exact Nat.ne_of_lt j.2 this
      have hlt := (e'.invFun j').2
      exact Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hlt) (fun hv => hne (Fin.ext hv))
    let res : Equiv (Fin m) (Fin n) := {
      toFun := fun i => ⟨(e'.toFun ⟨i.1, Nat.lt_succ_of_lt i.2⟩).1, hlt_to i⟩
      invFun := fun j => ⟨(e'.invFun ⟨j.1, Nat.lt_succ_of_lt j.2⟩).1, hlt_inv j⟩
      left_inv := fun i => by
        apply Fin.ext
        dsimp
        exact congrArg Fin.val (e'.left_inv ⟨i.1, Nat.lt_succ_of_lt i.2⟩)
      right_inv := fun j => by
        apply Fin.ext
        dsimp
        exact congrArg Fin.val (e'.right_inv ⟨j.1, Nat.lt_succ_of_lt j.2⟩)
    }
    exact congrArg Nat.succ (fin_equiv_eq res)

/-- Positive Theorem A2: Finite Boolean lattices `B_m` and `B_n` are isomorphic iff `m = n`. -/
theorem finBool_iso_iff_eq (m n : Nat) :
    Nonempty (BLIso (finBoolBL m) (finBoolBL n)) ↔ m = n := by
  constructor
  · rintro ⟨iso⟩
    have eAtoms : Equiv (Fin m) (Fin n) :=
      Equiv.trans (finBoolAtomsEquiv m)
        (Equiv.trans iso.atomEquiv (finBoolAtomsEquiv n).symm)
    exact fin_equiv_eq eAtoms
  · rintro rfl
    exact ⟨BLIso.refl (finBoolBL m)⟩


/-! ### Section 3.1. Definitions of Transposition Type and Irreducible Automorphisms -/

/-- Strictest definition of transposition type: swaps two distinct atoms `a ≠ b`
    and fixes every element disjoint from `a ∨ b` (below `(a ∨ b)ᶜ`). -/
def IsAtomTransposition {L : Type u} (bl : BooleanLattice L) (f : BLAut bl) : Prop :=
  ∃ a b : bl.Atoms, a ≠ b ∧
    f.toFun a.1 = b.1 ∧
    f.toFun b.1 = a.1 ∧
    ∀ x : L, bl.le x (bl.compl (bl.sup a.1 b.1)) → f.toFun x = x

/-- Conjugate in `Aut(L)` to an atom transposition. -/
def IsConjugateToAtomTransposition {L : Type u} (bl : BooleanLattice L) (f : BLAut bl) : Prop :=
  ∃ g : BLAut bl, IsAtomTransposition bl
    ((blAutGroup bl).mul ((blAutGroup bl).mul g f) ((blAutGroup bl).inv g))

/-- Broadest possible definition of transposition type: any non-identity involution
    `f ≠ 1` with `f² = 1` (covers all single transpositions, their conjugates, and
    arbitrary products of disjoint transpositions). -/
def IsInvolutionAut {L : Type u} (bl : BooleanLattice L) (f : BLAut bl) : Prop :=
  f ≠ (blAutGroup bl).one ∧ (blAutGroup bl).mul f f = (blAutGroup bl).one

/-- Universal Implication 1: Every atom transposition on ANY Boolean lattice is an involution. -/
theorem isAtomTransposition_imp_involution {L : Type u} {bl : BooleanLattice L}
    {f : BLAut bl} (ht : IsAtomTransposition bl f) : IsInvolutionAut bl f := by
  rcases ht with ⟨a, b, hab, hfa, hfb, hfix⟩
  constructor
  · intro hone
    have : f.toFun a.1 = a.1 := congrArg (fun g : BLAut bl => g.toFun a.1) hone
    rw [hfa] at this
    exact hab (Subtype.ext this.symm)
  · apply BLIso.ext
    intro y
    change f.toFun (f.toFun y) = y
    let u := bl.sup a.1 b.1
    have hy : y = bl.sup (bl.sup (bl.inf y a.1) (bl.inf y b.1)) (bl.inf y (bl.compl u)) := by
      have hd := bl.decomp_by y u
      rw [bl.inf_sup_left y a.1 b.1] at hd
      exact hd
    have hya : f.toFun (f.toFun (bl.inf y a.1)) = bl.inf y a.1 := by
      cases a.2.2 (bl.inf y a.1) (bl.inf_le_right y a.1) with
      | inl h0 => rw [h0, f.map_bot, f.map_bot]
      | inr h1 => rw [h1, hfa, hfb]
    have hyb : f.toFun (f.toFun (bl.inf y b.1)) = bl.inf y b.1 := by
      cases b.2.2 (bl.inf y b.1) (bl.inf_le_right y b.1) with
      | inl h0 => rw [h0, f.map_bot, f.map_bot]
      | inr h1 => rw [h1, hfb, hfa]
    have hyc : f.toFun (f.toFun (bl.inf y (bl.compl u))) = bl.inf y (bl.compl u) := by
      have hf1 := hfix (bl.inf y (bl.compl u)) (bl.inf_le_right y (bl.compl u))
      rw [hf1, hf1]
    conv => lhs; rw [hy]
    rw [f.map_sup, f.map_sup, f.map_sup, f.map_sup, hya, hyb, hyc, ← hy]

theorem isAtomTransposition_imp_conjugate {L : Type u} {bl : BooleanLattice L}
    {f : BLAut bl} (ht : IsAtomTransposition bl f) : IsConjugateToAtomTransposition bl f := by
  refine ⟨(blAutGroup bl).one, ?_⟩
  rw [(blAutGroup bl).one_mul]
  have hinv1 : (blAutGroup bl).inv (blAutGroup bl).one = (blAutGroup bl).one := rfl
  rw [hinv1, (blAutGroup bl).mul_one]
  exact ht

theorem isConjugate_imp_involution {L : Type u} {bl : BooleanLattice L}
    {f : BLAut bl} (hc : IsConjugateToAtomTransposition bl f) : IsInvolutionAut bl f := by
  rcases hc with ⟨g, ht⟩
  have hinv := isAtomTransposition_imp_involution ht
  constructor
  · intro hf1
    apply hinv.1
    rw [hf1, (blAutGroup bl).mul_one]
    apply BLIso.ext
    intro x
    exact g.right_inv x
  · apply BLIso.ext
    intro x
    have hsq := congrArg (fun h : BLAut bl => h.toFun (g.toFun x)) hinv.2
    dsimp [blAutGroup, BLIso.trans, BLIso.symm, BLIso.refl, Equiv.trans, Equiv.symm] at hsq ⊢
    rw [g.left_inv, g.left_inv] at hsq
    exact g.toEquiv.injective hsq

/-- Positive Boundary Theorem A3 (`n = 2`): On `B_2`, every non-identity automorphism
    IS an atom transposition (explaining why Clause II holds for `n ≤ 2`). -/
theorem finBool2_nonid_isAtomTransposition (f : BLAut (finBoolBL 2))
    (hf : f ≠ (blAutGroup (finBoolBL 2)).one) : IsAtomTransposition (finBoolBL 2) f := by
  let i0 : Fin 2 := ⟨0, by decide⟩
  let i1 : Fin 2 := ⟨1, by decide⟩
  let a0 : (finBoolBL 2).Atoms := ⟨atomVec i0, isAtom_atomVec i0⟩
  let a1 : (finBoolBL 2).Atoms := ⟨atomVec i1, isAtom_atomVec i1⟩
  have ha01 : a0 ≠ a1 := by
    intro h
    have hv := congrArg Fin.val (atomVec_injective (congrArg Subtype.val h))
    exact Nat.noConfusion hv
  -- `f` permutes `{a0, a1}`; if `f a0 = a0` then `f a1 = a1`, forcing `f = 1`
  rcases (isAtom_finBool_iff (f.toFun a0.1)).mp (f.map_isAtom a0.2) with ⟨k0, hk0⟩
  rcases (isAtom_finBool_iff (f.toFun a1.1)).mp (f.map_isAtom a1.2) with ⟨k1, hk1⟩
  have hk0_cases : k0 = i0 ∨ k0 = i1 := by
    match k0 with
    | ⟨0, _⟩ => exact Or.inl rfl
    | ⟨1, _⟩ => exact Or.inr rfl
  have hk1_cases : k1 = i0 ∨ k1 = i1 := by
    match k1 with
    | ⟨0, _⟩ => exact Or.inl rfl
    | ⟨1, _⟩ => exact Or.inr rfl
  cases hk0_cases with
  | inl hk00 =>
    subst hk00
    cases hk1_cases with
    | inl hk10 =>
      subst hk10
      exact False.elim (ha01 (Subtype.ext (f.toEquiv.injective (hk0.trans hk1.symm))))
    | inr hk11 =>
      subst hk11
      -- Both atoms fixed => f = 1
      apply False.elim (hf (BLIso.ext fun x => funext fun j => ?_))
      have hle0 : (finBoolBL 2).le a0.1 (f.toFun x) ↔ (finBoolBL 2).le a0.1 x := by
        have hm := f.map_le a0.1 x; rw [hk0] at hm; exact hm
      have hle1 : (finBoolBL 2).le a1.1 (f.toFun x) ↔ (finBoolBL 2).le a1.1 x := by
        have hm := f.map_le a1.1 x; rw [hk1] at hm; exact hm
      match j with
      | ⟨0, hj⟩ =>
        have hjeq : (⟨0, hj⟩ : Fin 2) = i0 := rfl
        rw [hjeq]
        change f.toFun x i0 = x i0
        rw [atomVec_le_iff, atomVec_le_iff] at hle0
        cases h1 : f.toFun x i0 <;> cases h2 : x i0 <;> simp_all
      | ⟨1, hj⟩ =>
        have hjeq : (⟨1, hj⟩ : Fin 2) = i1 := rfl
        rw [hjeq]
        change f.toFun x i1 = x i1
        rw [atomVec_le_iff, atomVec_le_iff] at hle1
        cases h1 : f.toFun x i1 <;> cases h2 : x i1 <;> simp_all
  | inr hk01 =>
    subst hk01
    cases hk1_cases with
    | inr hk11 =>
      subst hk11
      exact False.elim (ha01 (Subtype.ext (f.toEquiv.injective (hk0.trans hk1.symm))))
    | inl hk10 =>
      subst hk10
      refine ⟨a0, a1, ha01, hk0, hk1, ?_⟩
      intro x hx
      have hbot : x = (finBoolBL 2).bot := by
        funext j
        match j with
        | ⟨0, hj0⟩ =>
          have hjeq : (⟨0, hj0⟩ : Fin 2) = i0 := rfl
          rw [hjeq]
          cases hxj : x i0 with
          | false => rfl
          | true =>
            have h0 : !((atomVec i0 i0) || (atomVec i1 i0)) = true := hx i0 hxj
            rw [atomVec_self] at h0
            exact Bool.noConfusion h0
        | ⟨1, hj1⟩ =>
          have hjeq : (⟨1, hj1⟩ : Fin 2) = i1 := rfl
          rw [hjeq]
          cases hxj : x i1 with
          | false => rfl
          | true =>
            have h1 : !((atomVec i0 i1) || (atomVec i1 i1)) = true := hx i1 hxj
            rw [atomVec_self] at h1
            cases atomVec i0 i1 <;> exact Bool.noConfusion h1
      rw [hbot, f.map_bot]

/-- Irreducibility Definition (i): Direct-factor / central-idempotent irreducibility
    (indecomposability of `(L, f)` into `[⊥, x] × [⊥, xᶜ]` with `x ∉ {⊥, ⊤}`). -/
def IsDirectFactorIrreducible {L : Type u} (bl : BooleanLattice L) (f : BLAut bl) : Prop :=
  bl.bot ≠ bl.top ∧ ∀ x : L, f.toFun x = x → x = bl.bot ∨ x = bl.top

/-- Predicate for an `f`-invariant Boolean sublattice `S ⊆ L`. -/
structure IsInvSublattice {L : Type u} (bl : BooleanLattice L)
    (f : BLAut bl) (S : L → Prop) : Prop where
  has_bot : S bl.bot
  has_top : S bl.top
  closed_inf : ∀ {x y}, S x → S y → S (bl.inf x y)
  closed_sup : ∀ {x y}, S x → S y → S (bl.sup x y)
  closed_compl : ∀ {x}, S x → S (bl.compl x)
  closed_aut : ∀ {x}, S x → S (f.toFun x)

/-- Irreducibility Definition (ii): Boolean-sublattice simplicity — no proper
    nontrivial `f`-invariant Boolean sublattice exists. -/
def IsSublatticeIrreducible {L : Type u} (bl : BooleanLattice L) (f : BLAut bl) : Prop :=
  bl.bot ≠ bl.top ∧
  ∀ S : L → Prop, IsInvSublattice bl f S →
    (∀ x : L, S x → x = bl.bot ∨ x = bl.top) ∨ (∀ x : L, S x)

/-- Disjoint atom support for two automorphisms `g, h ∈ Aut(L)`. -/
def DisjointAtomSupport {L : Type u} (bl : BooleanLattice L)
    (g h : BLAut bl) : Prop :=
  ∀ a : bl.Atoms, g.toFun a.1 = a.1 ∨ h.toFun a.1 = a.1

/-- Irreducibility Definition (iii): Cycle / disjoint-support irreducibility —
    `f ≠ 1` cannot be factored into two non-identity automorphisms of disjoint atom support. -/
def IsCycleIrreducible {L : Type u} (bl : BooleanLattice L) (f : BLAut bl) : Prop :=
  f ≠ (blAutGroup bl).one ∧
  ¬ ∃ g h : BLAut bl,
      g ≠ (blAutGroup bl).one ∧
      h ≠ (blAutGroup bl).one ∧
      f = (blAutGroup bl).mul g h ∧
      DisjointAtomSupport bl g h

/-- Even-weight (augmentation) hyperplane `W_0 ⊂ B_3` over `F_2`. -/
def EvenParity3 (x : FinBool 3) : Prop :=
  xor (xor (x ⟨0, by decide⟩) (x ⟨1, by decide⟩)) (x ⟨2, by decide⟩) = false

/-- Irreducibility Definition (iv): `F_2`-linear irreducibility of `f` on the
    2-dimensional augmentation hyperplane `W_0 ⊂ (B_3, △)` over `F_2`. -/
def IsF2ReducedIrreducible3 (f : BLAut (finBoolBL 3)) : Prop :=
  (∀ x : FinBool 3, EvenParity3 x → EvenParity3 (f.toFun x)) ∧
  ∀ W : FinBool 3 → Prop,
    (∀ x, W x → EvenParity3 x) →
    W (finBoolBL 3).bot →
    (∀ x y, W x → W y → W ((finBoolBL 3).symmDiff x y)) →
    (∀ x, W x → W (f.toFun x)) →
    (∀ x, W x → x = (finBoolBL 3).bot) ∨ (∀ x, EvenParity3 x → W x)


/-! ### Section 3.2. Cyclic Shift Automorphism `cycleAut` and Disproof for ALL `d ≥ 3` -/

/-- Standard `(m+1)`-cycle `0 ↦ 1 ↦ ... ↦ m ↦ 0` on `Fin (m + 1)`. -/
def cyclePerm (m : Nat) : Perm (Fin (m + 1)) where
  toFun i := ⟨(i.1 + 1) % (m + 1), Nat.mod_lt _ (Nat.succ_pos m)⟩
  invFun i := ⟨(i.1 + m) % (m + 1), Nat.mod_lt _ (Nat.succ_pos m)⟩
  left_inv i := by
    apply Fin.ext
    dsimp
    have h1 : ((i.1 + 1) % (m + 1) + m) % (m + 1) = (i.1 + 1 + m) % (m + 1) := by
      rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    rw [h1]
    have h2 : i.1 + 1 + m = i.1 + (m + 1) := by omega
    rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt i.2]
  right_inv i := by
    apply Fin.ext
    dsimp
    have h1 : ((i.1 + m) % (m + 1) + 1) % (m + 1) = (i.1 + m + 1) % (m + 1) := by
      rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    rw [h1]
    have h2 : i.1 + m + 1 = i.1 + (m + 1) := by omega
    rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt i.2]

/-- Cyclic shift automorphism on `B_{m+1}`. -/
def cycleAut (m : Nat) : BLAut (finBoolBL (m + 1)) :=
  permToAut (cyclePerm m)

/-- Iterating `cyclePerm m` `k` times from `i` reaches `(i + k) % (m + 1)`. -/
def iterPerm {α : Type u} (p : Perm α) : Nat → α → α
  | 0, x => x
  | k + 1, x => p.toFun (iterPerm p k x)

theorem iterPerm_cyclePerm (m : Nat) (k : Nat) (i : Fin (m + 1)) :
    (iterPerm (cyclePerm m) k i).1 = (i.1 + k) % (m + 1) := by
  induction k with
  | zero =>
    exact (Nat.mod_eq_of_lt i.2).symm
  | succ k ih =>
    change ((iterPerm (cyclePerm m) k i).1 + 1) % (m + 1) = (i.1 + (k + 1)) % (m + 1)
    rw [ih, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, Nat.add_assoc]

/-- `cyclePerm m` acts transitively on `Fin (m + 1)`. -/
theorem cyclePerm_transitive (m : Nat) (i j : Fin (m + 1)) :
    ∃ k : Nat, iterPerm (cyclePerm m) k i = j := by
  let k := (j.1 + (m + 1) - i.1 % (m + 1)) % (m + 1)
  refine ⟨j.1 + (m + 1) - i.1, ?_⟩
  apply Fin.ext
  rw [iterPerm_cyclePerm]
  have h1 : i.1 + (j.1 + (m + 1) - i.1) = j.1 + (m + 1) := by
    have hi := i.2
    omega
  rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt j.2]

/-- Theorem A4.1: For EVERY `m`, `cycleAut m` is direct-factor irreducible on `B_{m+1}`. -/
theorem cycleAut_isDirectFactorIrreducible (m : Nat) :
    IsDirectFactorIrreducible (finBoolBL (m + 1)) (cycleAut m) := by
  constructor
  · intro hbt
    have := congrFun hbt ⟨0, Nat.succ_pos m⟩
    exact Bool.noConfusion this
  · intro x hfix
    -- `x (cyclePerm.toFun i) = x i` for all `i`
    have hstep : ∀ i : Fin (m + 1), x ((cyclePerm m).toFun i) = x i := by
      intro i
      have h := congrFun hfix ((cyclePerm m).toFun i)
      unfold cycleAut permToAut at h
      dsimp at h
      rw [(cyclePerm m).left_inv] at h
      exact h.symm
    have hiter : ∀ k : Nat, x (iterPerm (cyclePerm m) k ⟨0, Nat.succ_pos m⟩) =
        x ⟨0, Nat.succ_pos m⟩ := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih =>
        change x ((cyclePerm m).toFun (iterPerm (cyclePerm m) k ⟨0, Nat.succ_pos m⟩)) =
          x ⟨0, Nat.succ_pos m⟩
        rw [hstep, ih]
    cases hx0 : x ⟨0, Nat.succ_pos m⟩ with
    | false =>
      left
      funext j
      rcases cyclePerm_transitive m ⟨0, Nat.succ_pos m⟩ j with ⟨k, rfl⟩
      rw [hiter k, hx0]
      rfl
    | true =>
      right
      funext j
      rcases cyclePerm_transitive m ⟨0, Nat.succ_pos m⟩ j with ⟨k, rfl⟩
      rw [hiter k, hx0]
      rfl

/-- Helper: On `FinBool n`, an automorphism fixing all atoms is the identity. -/
theorem finBoolAut_eq_one_of_fix_atoms {n : Nat} {g : BLAut (finBoolBL n)}
    (hfix : ∀ i : Fin n, g.toFun (atomVec i) = atomVec i) :
    g = (blAutGroup (finBoolBL n)).one := by
  apply BLIso.ext
  intro x
  funext j
  change g.toFun x j = x j
  have hm := g.map_le (atomVec j) x
  rw [hfix j, atomVec_le_iff, atomVec_le_iff] at hm
  cases h1 : g.toFun x j <;> cases h2 : x j <;> simp_all

/-- Theorem A4.2: For EVERY `n : Nat` (`d = n + 3 ≥ 3`, or in fact `m + 2 ≥ 2`),
    `cycleAut (m + 1)` is disjoint-support cycle-irreducible on `B_{m+2}`. -/
theorem cycleAut_isCycleIrreducible (m : Nat) :
    IsCycleIrreducible (finBoolBL (m + 2)) (cycleAut (m + 1)) := by
  constructor
  · intro hone
    have h := congrArg (fun f : BLAut (finBoolBL (m + 2)) =>
      f.toFun (atomVec ⟨0, by omega⟩)) hone
    change (permToAut (cyclePerm (m + 1))).toFun (atomVec ⟨0, by omega⟩) =
      atomVec ⟨0, by omega⟩ at h
    rw [permToAut_atomVec] at h
    have hi := atomVec_injective h
    have hv : (1 : Nat) % (m + 2) = 0 := congrArg Fin.val hi
    have hmod : (1 : Nat) % (m + 2) = 1 := Nat.mod_eq_of_lt (by omega)
    omega
  · rintro ⟨g, h, hg1, hh1, hfgh, hdisj⟩
    -- Since `g ≠ 1`, some atom `i₀` is moved by `g`
    have hex_g : ∃ i₀ : Fin (m + 2), g.toFun (atomVec i₀) ≠ atomVec i₀ := by
      cases Classical.em (∃ i₀ : Fin (m + 2), g.toFun (atomVec i₀) ≠ atomVec i₀) with
      | inl hex => exact hex
      | inr hno =>
        apply False.elim (hg1 (finBoolAut_eq_one_of_fix_atoms fun i => ?_))
        cases Classical.em (g.toFun (atomVec i) = atomVec i) with
        | inl heq => exact heq
        | inr hne => exact False.elim (hno ⟨i, hne⟩)
    rcases hex_g with ⟨i₀, hi₀⟩
    -- Key orbit-closure step: if `g` moves `atomVec i`, then `g` also moves
    -- `atomVec ((cyclePerm (m + 1)).toFun i)`!
    have step_supp : ∀ i : Fin (m + 2),
        g.toFun (atomVec i) ≠ atomVec i →
        g.toFun (atomVec ((cyclePerm (m + 1)).toFun i)) ≠
          atomVec ((cyclePerm (m + 1)).toFun i) := by
      intro i hgi
      have hhi : h.toFun (atomVec i) = atomVec i := by
        cases hdisj ⟨atomVec i, isAtom_atomVec i⟩ with
        | inl hgfix => exact False.elim (hgi hgfix)
        | inr hhfix => exact hhfix
      have hcyc : (cycleAut (m + 1)).toFun (atomVec i) = g.toFun (h.toFun (atomVec i)) :=
        congrArg (fun f : BLAut (finBoolBL (m + 2)) => f.toFun (atomVec i)) hfgh
      rw [hhi] at hcyc
      change (permToAut (cyclePerm (m + 1))).toFun (atomVec i) = g.toFun (atomVec i) at hcyc
      rw [permToAut_atomVec] at hcyc
      -- Now `atomVec (cyclePerm i) = g (atomVec i)`. If `g` fixed `atomVec (cyclePerm i)`,
      -- injectivity of `g` would give `atomVec (cyclePerm i) = atomVec i`, contradicting `hgi`!
      intro hg_next
      rw [hcyc] at hg_next
      have heq := g.toEquiv.injective hg_next
      exact hgi heq
    have iter_supp : ∀ k : Nat,
        g.toFun (atomVec (iterPerm (cyclePerm (m + 1)) k i₀)) ≠
          atomVec (iterPerm (cyclePerm (m + 1)) k i₀) := by
      intro k
      induction k with
      | zero => exact hi₀
      | succ k ih => exact step_supp _ ih
    -- By transitivity of `cyclePerm`, `g` moves EVERY atom, so `h` fixes EVERY atom!
    apply hh1
    apply finBoolAut_eq_one_of_fix_atoms
    intro j
    rcases cyclePerm_transitive (m + 1) i₀ j with ⟨k, rfl⟩
    cases hdisj ⟨atomVec (iterPerm (cyclePerm (m + 1)) k i₀), isAtom_atomVec _⟩ with
    | inl hgfix => exact False.elim (iter_supp k hgfix)
    | inr hhfix => exact hhfix

/-- Theorem A4.3: For EVERY `n : Nat` (`d = n + 3 ≥ 3`), `cycleAut (n + 2)` is NOT
    an involution (`f² ≠ 1`), hence NOT of transposition type under ANY definition! -/
theorem cycleAut_not_involution (n : Nat) :
    ¬ IsInvolutionAut (finBoolBL (n + 3)) (cycleAut (n + 2)) := by
  intro hinv
  let i0 : Fin (n + 3) := ⟨0, by omega⟩
  let i2 : Fin (n + 3) := ⟨2, by omega⟩
  have hsq := congrArg (fun f : BLAut (finBoolBL (n + 3)) => f.toFun (atomVec i0)) hinv.2
  change (cycleAut (n + 2)).toFun ((cycleAut (n + 2)).toFun (atomVec i0)) = atomVec i0 at hsq
  unfold cycleAut at hsq
  rw [permToAut_atomVec, permToAut_atomVec] at hsq
  have hi := atomVec_injective hsq
  have hv : ((0 + 1) % (n + 3) + 1) % (n + 3) = 0 := congrArg Fin.val hi
  have h1 : (0 + 1) % (n + 3) = 1 := Nat.mod_eq_of_lt (by omega)
  rw [h1] at hv
  have h2 : (1 + 1) % (n + 3) = 2 := Nat.mod_eq_of_lt (by omega)
  rw [h2] at hv
  exact Nat.noConfusion hv

theorem cycleAut_not_conjugateTransposition (n : Nat) :
    ¬ IsConjugateToAtomTransposition (finBoolBL (n + 3)) (cycleAut (n + 2)) :=
  fun h => cycleAut_not_involution n (isConjugate_imp_involution h)

theorem cycleAut_not_atomTransposition (n : Nat) :
    ¬ IsAtomTransposition (finBoolBL (n + 3)) (cycleAut (n + 2)) :=
  fun h => cycleAut_not_involution n (isAtomTransposition_imp_involution h)

/-- Theorem A4.4: Conversely, on `B_{n+3}` (`d ≥ 3`), NO atom transposition is
    direct-factor irreducible (every atom transposition fixes a third atom!). -/
theorem atomTransposition_not_directFactorIrreducible (n : Nat)
    (f : BLAut (finBoolBL (n + 3)))
    (ht : IsAtomTransposition (finBoolBL (n + 3)) f) :
    ¬ IsDirectFactorIrreducible (finBoolBL (n + 3)) f := by
  rcases ht with ⟨a, b, _, _, _, hfix⟩
  rcases (isAtom_finBool_iff a.1).mp a.2 with ⟨ia, hia⟩
  rcases (isAtom_finBool_iff b.1).mp b.2 with ⟨ib, hib⟩
  intro hirr
  let c0 : Fin (n + 3) := ⟨0, by omega⟩
  let c1 : Fin (n + 3) := ⟨1, by omega⟩
  let c2 : Fin (n + 3) := ⟨2, by omega⟩
  -- Among `c0, c1, c2`, pick `k` distinct from `ia` and `ib`
  have hc01 : c0 ≠ c1 := by
    intro h; have hv : (0 : Nat) = 1 := congrArg Fin.val h; omega
  have hc02 : c0 ≠ c2 := by
    intro h; have hv : (0 : Nat) = 2 := congrArg Fin.val h; omega
  have hc12 : c1 ≠ c2 := by
    intro h; have hv : (1 : Nat) = 2 := congrArg Fin.val h; omega
  have hex : ∃ k : Fin (n + 3), k ≠ ia ∧ k ≠ ib := by
    by_cases h0 : c0 = ia ∨ c0 = ib
    · by_cases h1 : c1 = ia ∨ c1 = ib
      · refine ⟨c2, ?_, ?_⟩
        · intro h2a
          cases h0 with
          | inl h0a => exact hc02 (h0a.trans h2a.symm)
          | inr h0b =>
            cases h1 with
            | inl h1a => exact hc12 (h1a.trans h2a.symm)
            | inr h1b => exact hc01 (h0b.trans h1b.symm)
        · intro h2b
          cases h0 with
          | inr h0b => exact hc02 (h0b.trans h2b.symm)
          | inl h0a =>
            cases h1 with
            | inr h1b => exact hc12 (h1b.trans h2b.symm)
            | inl h1a => exact hc01 (h0a.trans h1a.symm)
      · exact ⟨c1, fun h => h1 (Or.inl h), fun h => h1 (Or.inr h)⟩
    · exact ⟨c0, fun h => h0 (Or.inl h), fun h => h0 (Or.inr h)⟩
  rcases hex with ⟨k, hka, hkb⟩
  have hle : (finBoolBL (n + 3)).le (atomVec k)
      ((finBoolBL (n + 3)).compl ((finBoolBL (n + 3)).sup a.1 b.1)) := by
    rw [atomVec_le_iff, hia, hib]
    have hval : ((finBoolBL (n + 3)).compl
        ((finBoolBL (n + 3)).sup (atomVec ia) (atomVec ib))) k =
        !((atomVec ia k) || (atomVec ib k)) := rfl
    rw [hval, atomVec_ne hka, atomVec_ne hkb]
    rfl
  have hfk := hfix (atomVec k) hle
  cases hirr.2 (atomVec k) hfk with
  | inl hbot => exact (isAtom_atomVec k).1 hbot
  | inr htop =>
    -- `atomVec k` cannot be `⊤` since `n + 3 ≥ 3` has another index `m ≠ k`
    by_cases hk0 : k.1 = 0
    · have hmk : c1 ≠ k := by
        intro h
        have hv : (1 : Nat) = k.1 := congrArg Fin.val h
        omega
      have hm := congrFun htop c1
      rw [atomVec_ne hmk] at hm
      exact Bool.noConfusion hm
    · have hmk : c0 ≠ k := by
        intro h
        have hv : (0 : Nat) = k.1 := congrArg Fin.val h
        omega
      have hm := congrFun htop c0
      rw [atomVec_ne hmk] at hm
      exact Bool.noConfusion hm


/-! ### Section 3.3. Strengthened Fourfold Irreducibility on `B_3` (`FinBool 3`) -/

def fin3_0 : Fin 3 := ⟨0, by decide⟩
def fin3_1 : Fin 3 := ⟨1, by decide⟩
def fin3_2 : Fin 3 := ⟨2, by decide⟩

theorem fin3_ext (u v : FinBool 3)
    (h0 : u fin3_0 = v fin3_0) (h1 : u fin3_1 = v fin3_1) (h2 : u fin3_2 = v fin3_2) :
    u = v := by
  funext j
  match j with
  | ⟨0, _⟩ => exact h0
  | ⟨1, _⟩ => exact h1
  | ⟨2, _⟩ => exact h2

/-- Exhaustive decomposition of `FinBool 3`: every element `x ∉ {⊥, ⊤}` either is
    an atom `atomVec i` or its complement `compl x` is an atom `atomVec i`. -/
theorem finBool3_atom_or_compl_atom {x : FinBool 3}
    (hne_bot : x ≠ (finBoolBL 3).bot) (hne_top : x ≠ (finBoolBL 3).top) :
    (∃ i : Fin 3, x = atomVec i) ∨ (∃ i : Fin 3, (finBoolBL 3).compl x = atomVec i) := by
  have hc : ∀ j : Fin 3, (finBoolBL 3).compl x j = !(x j) := fun _ => rfl
  cases h0 : x fin3_0 <;> cases h1 : x fin3_1 <;> cases h2 : x fin3_2
  · exact False.elim (hne_bot (fin3_ext x _ h0 h1 h2))
  · exact Or.inl ⟨fin3_2, fin3_ext x _ h0 h1 h2⟩
  · exact Or.inl ⟨fin3_1, fin3_ext x _ h0 h1 h2⟩
  · exact Or.inr ⟨fin3_0, fin3_ext ((finBoolBL 3).compl x) _
      (by rw [hc, h0]; rfl) (by rw [hc, h1]; rfl) (by rw [hc, h2]; rfl)⟩
  · exact Or.inl ⟨fin3_0, fin3_ext x _ h0 h1 h2⟩
  · exact Or.inr ⟨fin3_1, fin3_ext ((finBoolBL 3).compl x) _
      (by rw [hc, h0]; rfl) (by rw [hc, h1]; rfl) (by rw [hc, h2]; rfl)⟩
  · exact Or.inr ⟨fin3_2, fin3_ext ((finBoolBL 3).compl x) _
      (by rw [hc, h0]; rfl) (by rw [hc, h1]; rfl) (by rw [hc, h2]; rfl)⟩
  · exact False.elim (hne_top (fin3_ext x _ h0 h1 h2))

/-- Theorem A4.5: On `B_3`, the 3-cycle `cycleAut 2` is Boolean-sublattice simple
    (has NO proper nontrivial invariant Boolean sublattice whatsoever!). -/
theorem cycleAut3_isSublatticeIrreducible :
    IsSublatticeIrreducible (finBoolBL 3) (cycleAut 2) := by
  constructor
  · exact (cycleAut_isDirectFactorIrreducible 2).1
  · intro S hS
    cases Classical.em (∃ x : FinBool 3, S x ∧ x ≠ (finBoolBL 3).bot ∧ x ≠ (finBoolBL 3).top) with
    | inr htriv =>
      left
      intro x hsx
      cases Classical.em (x = (finBoolBL 3).bot) with
      | inl hb => exact Or.inl hb
      | inr hb =>
        cases Classical.em (x = (finBoolBL 3).top) with
        | inl ht => exact Or.inr ht
        | inr ht => exact False.elim (htriv ⟨x, hsx, hb, ht⟩)
    | inl hex =>
      right
      rcases hex with ⟨x, hsx, hxb, hxt⟩
      have hex_atom : ∃ i : Fin 3, S (atomVec i) := by
        cases finBool3_atom_or_compl_atom hxb hxt with
        | inl h => rcases h with ⟨i, rfl⟩; exact ⟨i, hsx⟩
        | inr h => rcases h with ⟨i, hc⟩; exact ⟨i, hc ▸ hS.closed_compl hsx⟩
      rcases hex_atom with ⟨i, hsi⟩
      have hall_atoms : ∀ j : Fin 3, S (atomVec j) := by
        intro j
        rcases cyclePerm_transitive 2 i j with ⟨k, rfl⟩
        induction k with
        | zero => exact hsi
        | succ k ih =>
          dsimp [iterPerm]
          have hstep := hS.closed_aut ih
          unfold cycleAut at hstep
          rw [permToAut_atomVec] at hstep
          exact hstep
      intro y
      let p0 := if y fin3_0 then atomVec fin3_0 else (finBoolBL 3).bot
      let p1 := if y fin3_1 then atomVec fin3_1 else (finBoolBL 3).bot
      let p2 := if y fin3_2 then atomVec fin3_2 else (finBoolBL 3).bot
      have hp0 : S p0 := by
        dsimp [p0]
        cases y fin3_0 with
        | false => exact hS.has_bot
        | true => exact hall_atoms fin3_0
      have hp1 : S p1 := by
        dsimp [p1]
        cases y fin3_1 with
        | false => exact hS.has_bot
        | true => exact hall_atoms fin3_1
      have hp2 : S p2 := by
        dsimp [p2]
        cases y fin3_2 with
        | false => exact hS.has_bot
        | true => exact hall_atoms fin3_2
      have hy : y = (finBoolBL 3).sup ((finBoolBL 3).sup p0 p1) p2 := by
        apply fin3_ext
        · change y fin3_0 = ((p0 fin3_0 || p1 fin3_0) || p2 fin3_0)
          dsimp [p0, p1, p2, atomVec, finBoolBL]
          cases y fin3_0 <;> cases y fin3_1 <;> cases y fin3_2 <;> rfl
        · change y fin3_1 = ((p0 fin3_1 || p1 fin3_1) || p2 fin3_1)
          dsimp [p0, p1, p2, atomVec, finBoolBL]
          cases y fin3_0 <;> cases y fin3_1 <;> cases y fin3_2 <;> rfl
        · change y fin3_2 = ((p0 fin3_2 || p1 fin3_2) || p2 fin3_2)
          dsimp [p0, p1, p2, atomVec, finBoolBL]
          cases y fin3_0 <;> cases y fin3_1 <;> cases y fin3_2 <;> rfl
      rw [hy]
      exact hS.closed_sup (hS.closed_sup hp0 hp1) hp2

/-- Helper for `EvenParity3` in terms of `fin3_0, fin3_1, fin3_2`. -/
theorem evenParity3_iff (x : FinBool 3) :
    EvenParity3 x ↔ xor (xor (x fin3_0) (x fin3_1)) (x fin3_2) = false :=
  Iff.rfl

/-- Theorem A4.6: On `B_3`, `cycleAut 2` acts irreducibly over `F_2` on the
    2-dimensional augmentation hyperplane `EvenParity3`. -/
theorem cycleAut3_isF2ReducedIrreducible :
    IsF2ReducedIrreducible3 (cycleAut 2) := by
  constructor
  · intro x hx
    rw [evenParity3_iff] at hx ⊢
    have h0 : (cycleAut 2).toFun x fin3_0 = x fin3_2 := rfl
    have h1 : (cycleAut 2).toFun x fin3_1 = x fin3_0 := rfl
    have h2 : (cycleAut 2).toFun x fin3_2 = x fin3_1 := rfl
    rw [h0, h1, h2]
    cases ha : x fin3_0 <;> cases hb : x fin3_1 <;> cases hc : x fin3_2 <;> simp_all
  · intro W hW_sub hW_bot _ hW_aut
    cases Classical.em (∃ v : FinBool 3, W v ∧ v ≠ (finBoolBL 3).bot) with
    | inr hzero =>
      left
      intro x hwx
      cases Classical.em (x = (finBoolBL 3).bot) with
      | inl hb => exact hb
      | inr hb => exact False.elim (hzero ⟨x, hwx, hb⟩)
    | inl hex =>
      right
      rcases hex with ⟨v, hwv, hv_ne⟩
      have hve : xor (xor (v fin3_0) (v fin3_1)) (v fin3_2) = false :=
        (evenParity3_iff v).mp (hW_sub v hwv)
      let v1 := (cycleAut 2).toFun v
      let v2 := (cycleAut 2).toFun v1
      have hwv1 : W v1 := hW_aut v hwv
      have hwv2 : W v2 := hW_aut v1 hwv1
      have hv1_0 : v1 fin3_0 = v fin3_2 := rfl
      have hv1_1 : v1 fin3_1 = v fin3_0 := rfl
      have hv1_2 : v1 fin3_2 = v fin3_1 := rfl
      have hv2_0 : v2 fin3_0 = v fin3_1 := rfl
      have hv2_1 : v2 fin3_1 = v fin3_2 := rfl
      have hv2_2 : v2 fin3_2 = v fin3_0 := rfl
      have hbot_0 : (finBoolBL 3).bot fin3_0 = false := rfl
      have hbot_1 : (finBoolBL 3).bot fin3_1 = false := rfl
      have hbot_2 : (finBoolBL 3).bot fin3_2 = false := rfl
      intro x hxe_raw
      have hxe : xor (xor (x fin3_0) (x fin3_1)) (x fin3_2) = false :=
        (evenParity3_iff x).mp hxe_raw
      cases hv0 : v fin3_0 <;> cases hv1 : v fin3_1 <;> cases hv2 : v fin3_2
      · exact False.elim (hv_ne (fin3_ext v (finBoolBL 3).bot
          (hv0.trans hbot_0.symm) (hv1.trans hbot_1.symm) (hv2.trans hbot_2.symm)))
      · rw [hv0, hv1, hv2] at hve; exact Bool.noConfusion hve
      · rw [hv0, hv1, hv2] at hve; exact Bool.noConfusion hve
      · -- v = (false, true, true)
        cases hx0 : x fin3_0 <;> cases hx1 : x fin3_1 <;> cases hx2 : x fin3_2
        · rw [fin3_ext x (finBoolBL 3).bot (hx0.trans hbot_0.symm)
            (hx1.trans hbot_1.symm) (hx2.trans hbot_2.symm)]; exact hW_bot
        · rw [hx0, hx1, hx2] at hxe; exact Bool.noConfusion hxe
        · rw [hx0, hx1, hx2] at hxe; exact Bool.noConfusion hxe
        · rw [fin3_ext x v (hx0.trans hv0.symm) (hx1.trans hv1.symm) (hx2.trans hv2.symm)]
          exact hwv
        · rw [hx0, hx1, hx2] at hxe; exact Bool.noConfusion hxe
        · rw [fin3_ext x v1 (hx0.trans (hv1_0.trans hv2).symm)
            (hx1.trans (hv1_1.trans hv0).symm) (hx2.trans (hv1_2.trans hv1).symm)]
          exact hwv1
        · rw [fin3_ext x v2 (hx0.trans (hv2_0.trans hv1).symm)
            (hx1.trans (hv2_1.trans hv2).symm) (hx2.trans (hv2_2.trans hv0).symm)]
          exact hwv2
        · rw [hx0, hx1, hx2] at hxe; exact Bool.noConfusion hxe
      · rw [hv0, hv1, hv2] at hve; exact Bool.noConfusion hve
      · -- v = (true, false, true)
        cases hx0 : x fin3_0 <;> cases hx1 : x fin3_1 <;> cases hx2 : x fin3_2
        · rw [fin3_ext x (finBoolBL 3).bot (hx0.trans hbot_0.symm)
            (hx1.trans hbot_1.symm) (hx2.trans hbot_2.symm)]; exact hW_bot
        · rw [hx0, hx1, hx2] at hxe; exact Bool.noConfusion hxe
        · rw [hx0, hx1, hx2] at hxe; exact Bool.noConfusion hxe
        · rw [fin3_ext x v2 (hx0.trans (hv2_0.trans hv1).symm)
            (hx1.trans (hv2_1.trans hv2).symm) (hx2.trans (hv2_2.trans hv0).symm)]
          exact hwv2
        · rw [hx0, hx1, hx2] at hxe; exact Bool.noConfusion hxe
        · rw [fin3_ext x v (hx0.trans hv0.symm) (hx1.trans hv1.symm) (hx2.trans hv2.symm)]
          exact hwv
        · rw [fin3_ext x v1 (hx0.trans (hv1_0.trans hv2).symm)
            (hx1.trans (hv1_1.trans hv0).symm) (hx2.trans (hv1_2.trans hv1).symm)]
          exact hwv1
        · rw [hx0, hx1, hx2] at hxe; exact Bool.noConfusion hxe
      · -- v = (true, true, false)
        cases hx0 : x fin3_0 <;> cases hx1 : x fin3_1 <;> cases hx2 : x fin3_2
        · rw [fin3_ext x (finBoolBL 3).bot (hx0.trans hbot_0.symm)
            (hx1.trans hbot_1.symm) (hx2.trans hbot_2.symm)]; exact hW_bot
        · rw [hx0, hx1, hx2] at hxe; exact Bool.noConfusion hxe
        · rw [hx0, hx1, hx2] at hxe; exact Bool.noConfusion hxe
        · rw [fin3_ext x v1 (hx0.trans (hv1_0.trans hv2).symm)
            (hx1.trans (hv1_1.trans hv0).symm) (hx2.trans (hv1_2.trans hv1).symm)]
          exact hwv1
        · rw [hx0, hx1, hx2] at hxe; exact Bool.noConfusion hxe
        · rw [fin3_ext x v2 (hx0.trans (hv2_0.trans hv1).symm)
            (hx1.trans (hv2_1.trans hv2).symm) (hx2.trans (hv2_2.trans hv0).symm)]
          exact hwv2
        · rw [fin3_ext x v (hx0.trans hv0.symm) (hx1.trans hv1.symm) (hx2.trans hv2.symm)]
          exact hwv
        · rw [hx0, hx1, hx2] at hxe; exact Bool.noConfusion hxe
      · rw [hv0, hv1, hv2] at hve; exact Bool.noConfusion hve

/-- Exact order 3 of `cycleAut 2` on `B_3`. -/
theorem cycleAut3_cubed_eq_one :
    (blAutGroup (finBoolBL 3)).mul
      ((blAutGroup (finBoolBL 3)).mul (cycleAut 2) (cycleAut 2)) (cycleAut 2) =
    (blAutGroup (finBoolBL 3)).one := by
  apply BLIso.ext
  intro x
  funext j
  change x ((cyclePerm 2).invFun ((cyclePerm 2).invFun ((cyclePerm 2).invFun j))) = x j
  apply congrArg x
  apply Fin.ext
  have hj := j.2
  dsimp [cyclePerm]
  omega


/-! ## Section 4. Level B — Infinite Boolean Lattices (Refuting Clauses I and III) -/

/-! ### Section 4.1. Refuting Clause I via `DyadicBL` and `HybridBL = DyadicBL × B_2` -/

theorem pow2_pos : ∀ k : Nat, 0 < 2 ^ k
  | 0 => by decide
  | k + 1 => by
    have ih := pow2_pos k
    rw [Nat.pow_succ]
    omega

theorem pow2_succ_add (k : Nat) : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by
  rw [Nat.pow_succ]
  omega

/-- A subset `S ⊆ ℕ` is `2^k`-periodic if `n + 2^k ∈ S ↔ n ∈ S` for all `n`. -/
def IsPow2Per (k : Nat) (S : Nat → Prop) : Prop :=
  ∀ n : Nat, S (n + 2 ^ k) ↔ S n

theorem isPow2Per_add (k : Nat) :
    ∀ (d : Nat) {S : Nat → Prop}, IsPow2Per k S → IsPow2Per (k + d) S
  | 0, _, h => h
  | d + 1, S, h => by
    have ih := isPow2Per_add k d h
    intro n
    have hp : 2 ^ (k + (d + 1)) = 2 ^ (k + d) + 2 ^ (k + d) := pow2_succ_add (k + d)
    rw [hp, ← Nat.add_assoc]
    exact (ih (n + 2 ^ (k + d))).trans (ih n)

/-- Carrier of the countable atomless dyadic Boolean lattice `L_dyad`. -/
def DyadicSet := { S : Nat → Prop // ∃ k : Nat, IsPow2Per k S }

/-- The dyadic periodic Boolean lattice `L_dyad ⊆ P(ℕ)`. -/
def dyadicBL : BooleanLattice DyadicSet where
  le A B := ∀ n : Nat, A.1 n → B.1 n
  le_refl _ _ h := h
  le_trans h1 h2 n h := h2 n (h1 n h)
  le_antisymm h1 h2 := Subtype.ext (funext fun n => propext ⟨h1 n, h2 n⟩)
  bot := ⟨fun _ => False, ⟨0, fun _ => Iff.rfl⟩⟩
  top := ⟨fun _ => True, ⟨0, fun _ => Iff.rfl⟩⟩
  bot_le _ _ h := False.elim h
  le_top _ _ _ := True.intro
  inf A B := ⟨fun n => A.1 n ∧ B.1 n, by
    rcases A.2 with ⟨kA, hA⟩
    rcases B.2 with ⟨kB, hB⟩
    refine ⟨kA + kB, fun n => ?_⟩
    have hA' := isPow2Per_add kA kB hA n
    have hB' : B.1 (n + 2 ^ (kA + kB)) ↔ B.1 n := by
      rw [Nat.add_comm kA kB]
      exact isPow2Per_add kB kA hB n
    exact ⟨fun ⟨ha, hb⟩ => ⟨hA'.mp ha, hB'.mp hb⟩,
           fun ⟨ha, hb⟩ => ⟨hA'.mpr ha, hB'.mpr hb⟩⟩⟩
  inf_le_left _ _ _ h := h.1
  inf_le_right _ _ _ h := h.2
  le_inf h1 h2 n h := ⟨h1 n h, h2 n h⟩
  sup A B := ⟨fun n => A.1 n ∨ B.1 n, by
    rcases A.2 with ⟨kA, hA⟩
    rcases B.2 with ⟨kB, hB⟩
    refine ⟨kA + kB, fun n => ?_⟩
    have hA' := isPow2Per_add kA kB hA n
    have hB' : B.1 (n + 2 ^ (kA + kB)) ↔ B.1 n := by
      rw [Nat.add_comm kA kB]
      exact isPow2Per_add kB kA hB n
    exact ⟨fun h => h.elim (fun ha => Or.inl (hA'.mp ha)) (fun hb => Or.inr (hB'.mp hb)),
           fun h => h.elim (fun ha => Or.inl (hA'.mpr ha)) (fun hb => Or.inr (hB'.mpr hb))⟩⟩
  le_sup_left _ _ _ h := Or.inl h
  le_sup_right _ _ _ h := Or.inr h
  sup_le h1 h2 n h := h.elim (h1 n) (h2 n)
  inf_sup_left A B C := Subtype.ext (funext fun n => propext ⟨
    fun ⟨ha, hbc⟩ => hbc.elim (fun hb => Or.inl ⟨ha, hb⟩) (fun hc => Or.inr ⟨ha, hc⟩),
    fun h => h.elim (fun ⟨ha, hb⟩ => ⟨ha, Or.inl hb⟩) (fun ⟨ha, hc⟩ => ⟨ha, Or.inr hc⟩)⟩)
  compl A := ⟨fun n => ¬ A.1 n, by
    rcases A.2 with ⟨kA, hA⟩
    exact ⟨kA, fun n => not_congr (hA n)⟩⟩
  inf_compl A := Subtype.ext (funext fun n => propext ⟨fun ⟨h, hn⟩ => hn h, False.elim⟩)
  sup_compl A := Subtype.ext (funext fun n => propext
    ⟨fun _ => True.intro, fun _ => Classical.em (A.1 n)⟩)

/-- `dyadicBL` is atomless: every nonzero element strictly contains a smaller nonzero element. -/
theorem dyadicBL_isAtomless : dyadicBL.IsAtomless := by
  intro S hAtom
  have hex : ∃ n₀ : Nat, S.1 n₀ := by
    cases Classical.em (∃ n₀ : Nat, S.1 n₀) with
    | inl h => exact h
    | inr h =>
      apply False.elim (hAtom.1 (Subtype.ext (funext fun n => propext ?_)))
      exact ⟨fun hs => False.elim (h ⟨n, hs⟩), False.elim⟩
  rcases hex with ⟨n₀, hn₀⟩
  rcases S.2 with ⟨k, hk⟩
  have hp : 0 < 2 ^ k := pow2_pos k
  have hdiv1 : ∀ m : Nat, (m + 2 ^ k) / 2 ^ k = m / 2 ^ k + 1 :=
    fun m => Nat.add_div_right m hp
  let T : DyadicSet := ⟨fun n => S.1 n ∧ (n / 2 ^ k) % 2 = 0, by
    refine ⟨k + 1, fun n => ?_⟩
    have hS1 := isPow2Per_add k 1 hk n
    have hq : (n + 2 ^ (k + 1)) / 2 ^ k = n / 2 ^ k + 2 := by
      rw [pow2_succ_add k, ← Nat.add_assoc, hdiv1 (n + 2 ^ k), hdiv1 n]
    have hmod : ((n + 2 ^ (k + 1)) / 2 ^ k) % 2 = 0 ↔ (n / 2 ^ k) % 2 = 0 := by
      rw [hq]; omega
    exact ⟨fun ⟨hs, hm⟩ => ⟨hS1.mp hs, hmod.mp hm⟩,
           fun ⟨hs, hm⟩ => ⟨hS1.mpr hs, hmod.mpr hm⟩⟩⟩
  have hT_le : dyadicBL.le T S := fun _ h => h.1
  have hn₀_shift : S.1 (n₀ + 2 ^ k) := (hk n₀).mpr hn₀
  have hT_ne_bot : T ≠ dyadicBL.bot := by
    intro hbot
    by_cases hpar : (n₀ / 2 ^ k) % 2 = 0
    · have ht : T.1 n₀ := ⟨hn₀, hpar⟩
      rw [hbot] at ht
      exact ht
    · have hpar1 : ((n₀ + 2 ^ k) / 2 ^ k) % 2 = 0 := by
        rw [hdiv1 n₀]; omega
      have ht : T.1 (n₀ + 2 ^ k) := ⟨hn₀_shift, hpar1⟩
      rw [hbot] at ht
      exact ht
  have hT_ne_S : T ≠ S := by
    intro heq
    by_cases hpar : (n₀ / 2 ^ k) % 2 = 0
    · have hpar1 : ((n₀ + 2 ^ k) / 2 ^ k) % 2 ≠ 0 := by
        rw [hdiv1 n₀]; omega
      have ht : T.1 (n₀ + 2 ^ k) := by rw [heq]; exact hn₀_shift
      exact hpar1 ht.2
    · have ht : T.1 n₀ := by rw [heq]; exact hn₀
      exact hpar ht.2
  cases hAtom.2 T hT_le with
  | inl hb => exact hT_ne_bot hb
  | inr hs => exact hT_ne_S hs

/-- Parity-flip involution `0 ↔ 1, 2 ↔ 3, ...` on `ℕ`. -/
def flip0 (n : Nat) : Nat :=
  if n % 2 = 0 then n + 1 else n - 1

theorem flip0_invol (n : Nat) : flip0 (flip0 n) = n := by
  unfold flip0
  split <;> split <;> omega

theorem flip0_add_even (m n : Nat) :
    flip0 (n + (m + m)) = flip0 n + (m + m) := by
  have hmod : (n + (m + m)) % 2 = n % 2 := by omega
  unfold flip0
  rw [hmod]
  split <;> omega

theorem flip0_add_pow2_succ (k n : Nat) :
    flip0 (n + 2 ^ (k + 1)) = flip0 n + 2 ^ (k + 1) := by
  rw [pow2_succ_add k]
  exact flip0_add_even (2 ^ k) n

/-- Non-identity automorphism `xor1Aut` on `dyadicBL` induced by `flip0`. -/
def xor1Aut : BLAut dyadicBL where
  toFun S := ⟨fun n => S.1 (flip0 n), by
    rcases S.2 with ⟨k, hk⟩
    have hk1 := isPow2Per_add k 1 hk
    refine ⟨k + 1, fun n => ?_⟩
    dsimp
    rw [flip0_add_pow2_succ]
    exact hk1 (flip0 n)⟩
  invFun S := ⟨fun n => S.1 (flip0 n), by
    rcases S.2 with ⟨k, hk⟩
    have hk1 := isPow2Per_add k 1 hk
    refine ⟨k + 1, fun n => ?_⟩
    dsimp
    rw [flip0_add_pow2_succ]
    exact hk1 (flip0 n)⟩
  left_inv S := Subtype.ext (funext fun n => by dsimp; rw [flip0_invol])
  right_inv S := Subtype.ext (funext fun n => by dsimp; rw [flip0_invol])
  map_le A B := by
    constructor
    · intro h n ha
      have hf := h (flip0 n)
      dsimp at hf
      rw [flip0_invol] at hf
      exact hf ha
    · intro h n ha
      exact h (flip0 n) ha

def evensDyad : DyadicSet :=
  ⟨fun n => n % 2 = 0, ⟨1, fun n => by change (n + 2) % 2 = 0 ↔ n % 2 = 0; omega⟩⟩

theorem xor1Aut_ne_one : xor1Aut ≠ (blAutGroup dyadicBL).one := by
  intro h
  have hev : (xor1Aut.toFun evensDyad).1 0 = ((blAutGroup dyadicBL).one.toFun evensDyad).1 0 :=
    congrArg (fun f : BLAut dyadicBL => (f.toFun evensDyad).1 0) h
  have ht : ((blAutGroup dyadicBL).one.toFun evensDyad).1 0 := rfl
  rw [← hev] at ht
  change (flip0 0) % 2 = 0 at ht
  have hf0 : flip0 0 = 1 := rfl
  rw [hf0] at ht
  omega

/-- Clause I Refutation (Atom-Symmetric Reading): `Aut(dyadicBL)` is NOT isomorphic
    to `Perm (Atoms dyadicBL)` (`|Aut| ≥ 2` while `Atoms = ∅` gives `|Perm(∅)| = 1`). -/
theorem dyadicBL_aut_not_iso_perm_atoms :
    ¬ Nonempty (GroupIso (blAutGroup dyadicBL) (permGroup dyadicBL.Atoms)) := by
  rintro ⟨iso⟩
  have hsub : iso.toFun xor1Aut = iso.toFun (blAutGroup dyadicBL).one := by
    apply Equiv.ext
    intro a
    exact False.elim (dyadicBL_isAtomless a.1 a.2)
  exact xor1Aut_ne_one (iso.toEquiv.injective hsub)

/-- Hybrid countable Boolean lattice `L_* = L_dyad × B_2` refuting Clause I universally. -/
abbrev HybridCarrier := DyadicSet × FinBool 2

def hybridBL : BooleanLattice HybridCarrier :=
  prodBL dyadicBL (finBoolBL 2)

def fin2_0 : Fin 2 := ⟨0, by decide⟩
def fin2_1 : Fin 2 := ⟨1, by decide⟩

theorem fin2_ext (u v : FinBool 2)
    (h0 : u fin2_0 = v fin2_0) (h1 : u fin2_1 = v fin2_1) : u = v := by
  funext j
  match j with
  | ⟨0, _⟩ => exact h0
  | ⟨1, _⟩ => exact h1

def hybAtom0 : HybridCarrier := (dyadicBL.bot, atomVec fin2_0)
def hybAtom1 : HybridCarrier := (dyadicBL.bot, atomVec fin2_1)

theorem hybAtom0_ne_hybAtom1 : hybAtom0 ≠ hybAtom1 := by
  intro h
  have hv := congrArg (fun p : HybridCarrier => p.2 fin2_0) h
  exact Bool.noConfusion hv

theorem isAtom_hybAtom0 : hybridBL.IsAtom hybAtom0 := by
  constructor
  · intro h
    have hv := congrArg (fun p : HybridCarrier => p.2 fin2_0) h
    exact Bool.noConfusion hv
  · rintro ⟨S, u⟩ ⟨hS, hu⟩
    have hS0 : S = dyadicBL.bot :=
      dyadicBL.le_antisymm hS (dyadicBL.bot_le S)
    subst hS0
    cases (isAtom_atomVec fin2_0).2 u hu with
    | inl hu0 => subst hu0; exact Or.inl rfl
    | inr hu1 => subst hu1; exact Or.inr rfl

theorem isAtom_hybAtom1 : hybridBL.IsAtom hybAtom1 := by
  constructor
  · intro h
    have hv := congrArg (fun p : HybridCarrier => p.2 fin2_1) h
    exact Bool.noConfusion hv
  · rintro ⟨S, u⟩ ⟨hS, hu⟩
    have hS0 : S = dyadicBL.bot :=
      dyadicBL.le_antisymm hS (dyadicBL.bot_le S)
    subst hS0
    cases (isAtom_atomVec fin2_1).2 u hu with
    | inl hu0 => subst hu0; exact Or.inl rfl
    | inr hu1 => subst hu1; exact Or.inr rfl

/-- The ONLY atoms of `hybridBL = dyadicBL × B_2` are `hybAtom0` and `hybAtom1`. -/
theorem isAtom_hybridBL_iff (p : HybridCarrier) :
    hybridBL.IsAtom p ↔ p = hybAtom0 ∨ p = hybAtom1 := by
  constructor
  · rcases p with ⟨S, u⟩
    intro hp
    -- First show `S = ⊥`; otherwise `(S, ⊥)` forces `S` to be an atom of `dyadicBL`!
    have hS_bot : S = dyadicBL.bot := by
      cases Classical.em (S = dyadicBL.bot) with
      | inl h => exact h
      | inr hSne =>
        have hle : hybridBL.le (S, (finBoolBL 2).bot) (S, u) :=
          ⟨dyadicBL.le_refl S, (finBoolBL 2).bot_le u⟩
        cases hp.2 (S, (finBoolBL 2).bot) hle with
        | inl hbot =>
          exact False.elim (hSne (congrArg Prod.fst hbot))
        | inr heq =>
          have hu_bot : u = (finBoolBL 2).bot := (congrArg Prod.snd heq).symm
          subst hu_bot
          -- Now `S` would be an atom of `dyadicBL`
          have hS_atom : dyadicBL.IsAtom S := by
            refine ⟨hSne, fun T hTS => ?_⟩
            cases hp.2 (T, (finBoolBL 2).bot) ⟨hTS, (finBoolBL 2).le_refl _⟩ with
            | inl hb => exact Or.inl (congrArg Prod.fst hb)
            | inr hs => exact Or.inr (congrArg Prod.fst hs)
          exact False.elim (dyadicBL_isAtomless S hS_atom)
    subst hS_bot
    -- Now `u` is an atom of `finBoolBL 2`
    have hu_atom : (finBoolBL 2).IsAtom u := by
      refine ⟨fun hub => hp.1 (Prod.ext rfl hub), fun v hvu => ?_⟩
      cases hp.2 (dyadicBL.bot, v) ⟨dyadicBL.le_refl _, hvu⟩ with
      | inl hb => exact Or.inl (congrArg Prod.snd hb)
      | inr hs => exact Or.inr (congrArg Prod.snd hs)
    rcases (isAtom_finBool_iff u).mp hu_atom with ⟨j, rfl⟩
    match j with
    | ⟨0, _⟩ => exact Or.inl rfl
    | ⟨1, _⟩ => exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact isAtom_hybAtom0
    · exact isAtom_hybAtom1

/-- Coordinate swap on `FinBool 2`. -/
def swapB2 (u : FinBool 2) : FinBool 2
  | ⟨0, _⟩ => u fin2_1
  | ⟨1, _⟩ => u fin2_0

theorem swapB2_invol (u : FinBool 2) : swapB2 (swapB2 u) = u :=
  fin2_ext _ _ rfl rfl

/-- Central swap automorphism `(S, u) ↦ (S, swapB2 u)` on `hybridBL`. -/
def centralSwap : BLAut hybridBL where
  toFun p := (p.1, swapB2 p.2)
  invFun p := (p.1, swapB2 p.2)
  left_inv p := Prod.ext rfl (swapB2_invol p.2)
  right_inv p := Prod.ext rfl (swapB2_invol p.2)
  map_le p q := by
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun j hj => ?_⟩
      match j with
      | ⟨0, _⟩ => exact h2 fin2_1 hj
      | ⟨1, _⟩ => exact h2 fin2_0 hj
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun j hj => ?_⟩
      match j with
      | ⟨0, _⟩ => exact h2 fin2_1 hj
      | ⟨1, _⟩ => exact h2 fin2_0 hj

/-- Left-factor automorphism `(S, u) ↦ (xor1Aut S, u)` on `hybridBL`. -/
def leftXorAut : BLAut hybridBL where
  toFun p := (xor1Aut.toFun p.1, p.2)
  invFun p := (xor1Aut.invFun p.1, p.2)
  left_inv p := Prod.ext (xor1Aut.left_inv p.1) rfl
  right_inv p := Prod.ext (xor1Aut.right_inv p.1) rfl
  map_le p q := ⟨fun ⟨h1, h2⟩ => ⟨(xor1Aut.map_le p.1 q.1).mp h1, h2⟩,
                 fun ⟨h1, h2⟩ => ⟨(xor1Aut.map_le p.1 q.1).mpr h1, h2⟩⟩

theorem centralSwap_ne_one : centralSwap ≠ (blAutGroup hybridBL).one := by
  intro h
  have hv := congrArg (fun f : BLAut hybridBL => (f.toFun hybAtom0).2 fin2_0) h
  exact Bool.noConfusion hv

theorem leftXorAut_ne_one : leftXorAut ≠ (blAutGroup hybridBL).one := by
  intro h
  apply xor1Aut_ne_one
  apply BLIso.ext
  intro S
  exact congrArg (fun f : BLAut hybridBL => (f.toFun (S, (finBoolBL 2).bot)).1) h

theorem leftXorAut_ne_centralSwap : leftXorAut ≠ centralSwap := by
  intro h
  have hv := congrArg (fun f : BLAut hybridBL => (f.toFun hybAtom0).2 fin2_0) h
  change (atomVec fin2_0) fin2_0 = (swapB2 (atomVec fin2_0)) fin2_0 at hv
  exact Bool.noConfusion hv

/-- Key Theorem: `centralSwap` lies in the center `Z(Aut(hybridBL))`! -/
theorem centralSwap_isCentral : IsCentral (blAutGroup hybridBL) centralSwap := by
  intro Φ
  apply BLIso.ext
  rintro ⟨S, u⟩
  -- `Φ` permutes `{hybAtom0, hybAtom1}`
  have hΦ0 := (isAtom_hybridBL_iff (Φ.toFun hybAtom0)).mp (Φ.map_isAtom isAtom_hybAtom0)
  have hΦ1 := (isAtom_hybridBL_iff (Φ.toFun hybAtom1)).mp (Φ.map_isAtom isAtom_hybAtom1)
  have hsup01 : hybridBL.sup hybAtom0 hybAtom1 = (dyadicBL.bot, (finBoolBL 2).top) := by
    apply Prod.ext (dyadicBL.sup_idem dyadicBL.bot)
    exact fin2_ext _ _ rfl rfl
  -- Hence `Φ` fixes `(⊥, ⊤) = hybAtom0 ∨ hybAtom1` and its complement `(⊤, ⊥)`!
  have hΦ_bot_top : Φ.toFun (dyadicBL.bot, (finBoolBL 2).top) =
      (dyadicBL.bot, (finBoolBL 2).top) := by
    rw [← hsup01, Φ.map_sup]
    cases hΦ0 with
    | inl h00 =>
      cases hΦ1 with
      | inl h10 =>
        exact False.elim (hybAtom0_ne_hybAtom1 (Φ.toEquiv.injective (h00.trans h10.symm)))
      | inr h11 => rw [h00, h11]
    | inr h01 =>
      cases hΦ1 with
      | inr h11 =>
        exact False.elim (hybAtom0_ne_hybAtom1 (Φ.toEquiv.injective (h01.trans h11.symm)))
      | inl h10 => rw [h01, h10, hybridBL.sup_comm]
  have hcompl_bt : hybridBL.compl (dyadicBL.bot, (finBoolBL 2).top) =
      (dyadicBL.top, (finBoolBL 2).bot) := by
    apply Prod.ext
    · exact Subtype.ext (funext fun _ => propext ⟨fun _ => True.intro, fun _ f => f⟩)
    · exact fin2_ext _ _ rfl rfl
  have hΦ_top_bot : Φ.toFun (dyadicBL.top, (finBoolBL 2).bot) =
      (dyadicBL.top, (finBoolBL 2).bot) := by
    rw [← hcompl_bt, Φ.map_compl, hΦ_bot_top]
  -- 1. Commutation on `(S, ⊥)`
  have hcomm_left : centralSwap.toFun (Φ.toFun (S, (finBoolBL 2).bot)) =
      Φ.toFun (centralSwap.toFun (S, (finBoolBL 2).bot)) := by
    have hcs_bot : centralSwap.toFun (S, (finBoolBL 2).bot) = (S, (finBoolBL 2).bot) :=
      Prod.ext rfl (fin2_ext _ _ rfl rfl)
    rw [hcs_bot]
    have hle : hybridBL.le (Φ.toFun (S, (finBoolBL 2).bot))
        (dyadicBL.top, (finBoolBL 2).bot) := by
      rw [← hΦ_top_bot, Φ.map_le]
      exact ⟨dyadicBL.le_top S, (finBoolBL 2).le_refl _⟩
    have hsnd_bot : (Φ.toFun (S, (finBoolBL 2).bot)).2 = (finBoolBL 2).bot :=
      (finBoolBL 2).le_antisymm hle.2 ((finBoolBL 2).bot_le _)
    refine Prod.ext rfl ?_
    change swapB2 (Φ.toFun (S, (finBoolBL 2).bot)).2 = (Φ.toFun (S, (finBoolBL 2).bot)).2
    rw [hsnd_bot]
    exact fin2_ext _ _ rfl rfl
  -- 2. Commutation on `(⊥, u)` across all 4 elements of `FinBool 2`
  have hcs_a0 : centralSwap.toFun hybAtom0 = hybAtom1 := Prod.ext rfl (fin2_ext _ _ rfl rfl)
  have hcs_a1 : centralSwap.toFun hybAtom1 = hybAtom0 := Prod.ext rfl (fin2_ext _ _ rfl rfl)
  have hcomm_atoms :
      centralSwap.toFun (Φ.toFun hybAtom0) = Φ.toFun (centralSwap.toFun hybAtom0) ∧
      centralSwap.toFun (Φ.toFun hybAtom1) = Φ.toFun (centralSwap.toFun hybAtom1) := by
    rw [hcs_a0, hcs_a1]
    cases hΦ0 with
    | inl h00 =>
      cases hΦ1 with
      | inl h10 =>
        exact False.elim (hybAtom0_ne_hybAtom1 (Φ.toEquiv.injective (h00.trans h10.symm)))
      | inr h11 =>
        rw [h00, h11, hcs_a0, hcs_a1]
        exact ⟨rfl, rfl⟩
    | inr h01 =>
      cases hΦ1 with
      | inr h11 =>
        exact False.elim (hybAtom0_ne_hybAtom1 (Φ.toEquiv.injective (h01.trans h11.symm)))
      | inl h10 =>
        rw [h01, h10, hcs_a1, hcs_a0]
        exact ⟨rfl, rfl⟩
  have hcomm_right : centralSwap.toFun (Φ.toFun (dyadicBL.bot, u)) =
      Φ.toFun (centralSwap.toFun (dyadicBL.bot, u)) := by
    cases hu0 : u fin2_0 <;> cases hu1 : u fin2_1
    · have hu_eq : (dyadicBL.bot, u) = hybridBL.bot :=
        Prod.ext rfl (fin2_ext u _ hu0 hu1)
      rw [hu_eq, Φ.map_bot, centralSwap.map_bot, Φ.map_bot]
    · have hu_eq : (dyadicBL.bot, u) = hybAtom1 :=
        Prod.ext rfl (fin2_ext u _ hu0 hu1)
      rw [hu_eq]; exact hcomm_atoms.2
    · have hu_eq : (dyadicBL.bot, u) = hybAtom0 :=
        Prod.ext rfl (fin2_ext u _ hu0 hu1)
      rw [hu_eq]; exact hcomm_atoms.1
    · have hu_eq : (dyadicBL.bot, u) = (dyadicBL.bot, (finBoolBL 2).top) :=
        Prod.ext rfl (fin2_ext u _ hu0 hu1)
      have hcs_bt : centralSwap.toFun (dyadicBL.bot, (finBoolBL 2).top) =
          (dyadicBL.bot, (finBoolBL 2).top) := Prod.ext rfl (fin2_ext _ _ rfl rfl)
      rw [hu_eq, hΦ_bot_top, hcs_bt, hΦ_bot_top]
  -- 3. Combine `(S, u) = (S, ⊥) ∨ (⊥, u)`
  have hdecomp : (S, u) =
      hybridBL.sup (S, (finBoolBL 2).bot) (dyadicBL.bot, u) := by
    apply Prod.ext
    · exact (dyadicBL.sup_bot_right S).symm
    · exact ((finBoolBL 2).sup_bot_left u).symm
  change centralSwap.toFun (Φ.toFun (S, u)) = Φ.toFun (centralSwap.toFun (S, u))
  conv => lhs; rw [hdecomp]
  conv => rhs; rw [hdecomp]
  rw [Φ.map_sup, centralSwap.map_sup, centralSwap.map_sup, Φ.map_sup,
      hcomm_left, hcomm_right]

/-- Theorem B1 (Universal Refutation of Clause I):
    For EVERY universe `u` and EVERY type `X : Type u`, the automorphism group
    `Aut(hybridBL)` of the Boolean lattice `L_dyad × B_2` is NOT isomorphic to
    the symmetric group `Perm X`! -/
theorem hybridBL_aut_not_iso_any_perm (X : Type u) :
    ¬ Nonempty (GroupIso (blAutGroup hybridBL) (permGroup X)) :=
  not_groupIso_perm_of_nontrivial_center_and_three
    (blAutGroup hybridBL)
    centralSwap_isCentral
    centralSwap_ne_one
    leftXorAut_ne_one
    leftXorAut_ne_centralSwap
    X


/-! ### Section 4.2. Refuting Clause III via `FinCofinBL` vs `FinCofinBL × FinCofinBL` -/

/-- A subset `A ⊆ ℕ` is finite iff it is bounded above in `ℕ`. -/
def IsFinNat (A : Nat → Prop) : Prop :=
  ∃ B : Nat, ∀ n : Nat, A n → n < B

/-- Proof that `IsFinNat A` is extensionally identical to membership in a finite `List Nat`. -/
theorem isFinNat_iff_list (A : Nat → Prop) :
    IsFinNat A ↔ ∃ l : List Nat, ∀ n : Nat, A n ↔ n ∈ l := by
  constructor
  · rintro ⟨B, hB⟩
    have aux : ∀ M : Nat, ∃ l : List Nat, ∀ n : Nat, (A n ∧ n < M) ↔ n ∈ l := by
      intro M
      induction M with
      | zero =>
        exact ⟨[], fun n => ⟨fun ⟨_, hn⟩ => by omega, fun hn => nomatch hn⟩⟩
      | succ M ih =>
        rcases ih with ⟨l, hl⟩
        cases Classical.em (A M) with
        | inl hAM =>
          refine ⟨M :: l, fun n => ?_⟩
          constructor
          · rintro ⟨han, hlt⟩
            by_cases hnm : n = M
            · subst hnm; exact List.Mem.head l
            · exact List.Mem.tail M ((hl n).mp ⟨han, by omega⟩)
          · intro hmem
            cases hmem with
            | head => exact ⟨hAM, by omega⟩
            | tail _ htail =>
              rcases (hl n).mpr htail with ⟨han, hlt⟩
              exact ⟨han, by omega⟩
        | inr hAM =>
          refine ⟨l, fun n => ?_⟩
          constructor
          · rintro ⟨han, hlt⟩
            have hne : n ≠ M := fun heq => hAM (heq ▸ han)
            exact (hl n).mp ⟨han, by omega⟩
          · intro hmem
            rcases (hl n).mpr hmem with ⟨han, hlt⟩
            exact ⟨han, by omega⟩
    rcases aux B with ⟨l, hl⟩
    exact ⟨l, fun n => ⟨fun han => (hl n).mp ⟨han, hB n han⟩,
                        fun hmem => ((hl n).mpr hmem).1⟩⟩
  · rintro ⟨l, hl⟩
    have listBound : ∀ l : List Nat, ∃ B : Nat, ∀ n : Nat, n ∈ l → n < B := by
      intro l'
      induction l' with
      | nil => exact ⟨0, fun _ h => nomatch h⟩
      | cons a t ih =>
        rcases ih with ⟨B, hB⟩
        refine ⟨a + 1 + B, fun n hn => ?_⟩
        cases hn with
        | head => omega
        | tail _ ht => have := hB n ht; omega
    rcases listBound l with ⟨B, hB⟩
    exact ⟨B, fun n han => hB n ((hl n).mp han)⟩

/-- A subset `A ⊆ ℕ` is cofinite iff its complement `ℕ \ A` is finite. -/
def IsCofinNat (A : Nat → Prop) : Prop :=
  IsFinNat (fun n => ¬ A n)

/-- Disjointness of finiteness and cofiniteness on `ℕ`. -/
theorem not_fin_and_cofin {A : Nat → Prop}
    (hf : IsFinNat A) (hc : IsCofinNat A) : False := by
  rcases hf with ⟨B₁, h1⟩
  rcases hc with ⟨B₂, h2⟩
  cases Classical.em (A (B₁ + B₂)) with
  | inl ha => have := h1 (B₁ + B₂) ha; omega
  | inr hna => have := h2 (B₁ + B₂) hna; omega

/-- Carrier of the finite–cofinite Boolean lattice `L_fc` on `ℕ`. -/
def FinCofinSet := { A : Nat → Prop // IsFinNat A ∨ IsCofinNat A }

/-- The finite–cofinite Boolean lattice `L_fc` on `ℕ`. -/
def finCofinBL : BooleanLattice FinCofinSet where
  le A B := ∀ n : Nat, A.1 n → B.1 n
  le_refl _ _ h := h
  le_trans h1 h2 n h := h2 n (h1 n h)
  le_antisymm h1 h2 := Subtype.ext (funext fun n => propext ⟨h1 n, h2 n⟩)
  bot := ⟨fun _ => False, Or.inl ⟨0, fun _ h => False.elim h⟩⟩
  top := ⟨fun _ => True, Or.inr ⟨0, fun _ h => False.elim (h True.intro)⟩⟩
  bot_le _ _ h := False.elim h
  le_top _ _ _ := True.intro
  inf A B := ⟨fun n => A.1 n ∧ B.1 n, by
    cases A.2 with
    | inl hfA =>
      rcases hfA with ⟨B₁, h1⟩
      exact Or.inl ⟨B₁, fun n ⟨ha, _⟩ => h1 n ha⟩
    | inr hcA =>
      cases B.2 with
      | inl hfB =>
        rcases hfB with ⟨B₂, h2⟩
        exact Or.inl ⟨B₂, fun n ⟨_, hb⟩ => h2 n hb⟩
      | inr hcB =>
        rcases hcA with ⟨B₁, h1⟩
        rcases hcB with ⟨B₂, h2⟩
        refine Or.inr ⟨B₁ + B₂, fun n hnab => ?_⟩
        cases Classical.em (A.1 n) with
        | inl ha =>
          have hnb : ¬ B.1 n := fun hb => hnab ⟨ha, hb⟩
          have := h2 n hnb; omega
        | inr hna =>
          have := h1 n hna; omega⟩
  inf_le_left _ _ _ h := h.1
  inf_le_right _ _ _ h := h.2
  le_inf h1 h2 n h := ⟨h1 n h, h2 n h⟩
  sup A B := ⟨fun n => A.1 n ∨ B.1 n, by
    cases A.2 with
    | inr hcA =>
      rcases hcA with ⟨B₁, h1⟩
      exact Or.inr ⟨B₁, fun n hno => h1 n (fun ha => hno (Or.inl ha))⟩
    | inl hfA =>
      cases B.2 with
      | inr hcB =>
        rcases hcB with ⟨B₂, h2⟩
        exact Or.inr ⟨B₂, fun n hno => h2 n (fun hb => hno (Or.inr hb))⟩
      | inl hfB =>
        rcases hfA with ⟨B₁, h1⟩
        rcases hfB with ⟨B₂, h2⟩
        refine Or.inl ⟨B₁ + B₂, fun n h => ?_⟩
        cases h with
        | inl ha => have := h1 n ha; omega
        | inr hb => have := h2 n hb; omega⟩
  le_sup_left _ _ _ h := Or.inl h
  le_sup_right _ _ _ h := Or.inr h
  sup_le h1 h2 n h := h.elim (h1 n) (h2 n)
  inf_sup_left A B C := Subtype.ext (funext fun n => propext ⟨
    fun ⟨ha, hbc⟩ => hbc.elim (fun hb => Or.inl ⟨ha, hb⟩) (fun hc => Or.inr ⟨ha, hc⟩),
    fun h => h.elim (fun ⟨ha, hb⟩ => ⟨ha, Or.inl hb⟩) (fun ⟨ha, hc⟩ => ⟨ha, Or.inr hc⟩)⟩)
  compl A := ⟨fun n => ¬ A.1 n, by
    cases A.2 with
    | inl hf =>
      rcases hf with ⟨B, hB⟩
      refine Or.inr ⟨B, fun n hnn => ?_⟩
      cases Classical.em (A.1 n) with
      | inl ha => exact hB n ha
      | inr hna => exact False.elim (hnn hna)
    | inr hc => exact Or.inl hc⟩
  inf_compl A := Subtype.ext (funext fun n => propext ⟨fun ⟨h, hn⟩ => hn h, False.elim⟩)
  sup_compl A := Subtype.ext (funext fun n => propext
    ⟨fun _ => True.intro, fun _ => Classical.em (A.1 n)⟩)

/-- Direct product `L_fc × L_fc`. -/
abbrev ProdFCCarrier := FinCofinSet × FinCofinSet

def prodFC : BooleanLattice ProdFCCarrier :=
  prodBL finCofinBL finCofinBL

/-- Singleton atom `{k}` in `FinCofinBL`. -/
def singletonFC (k : Nat) : FinCofinSet :=
  ⟨fun n => n = k, Or.inl ⟨k + 1, fun _ h => by omega⟩⟩

theorem singletonFC_injective {k₁ k₂ : Nat}
    (h : singletonFC k₁ = singletonFC k₂) : k₁ = k₂ := by
  have hk : (singletonFC k₁).1 k₁ = (singletonFC k₂).1 k₁ :=
    congrFun (congrArg Subtype.val h) k₁
  change (k₁ = k₁) = (k₁ = k₂) at hk
  exact Eq.mp hk rfl

theorem isAtom_singletonFC (k : Nat) : finCofinBL.IsAtom (singletonFC k) := by
  constructor
  · intro hbot
    have hk : (singletonFC k).1 k := rfl
    rw [hbot] at hk
    exact hk
  · intro X hX
    cases Classical.em (X.1 k) with
    | inr hnk =>
      left
      apply Subtype.ext (funext fun n => propext ⟨fun hxn => ?_, False.elim⟩)
      have hnk_eq : n = k := hX n hxn
      exact hnk (hnk_eq ▸ hxn)
    | inl hxk =>
      right
      apply Subtype.ext (funext fun n => propext ⟨fun hxn => hX n hxn, fun hnk => ?_⟩)
      subst hnk
      exact hxk

theorem exists_mem_of_ne_bot_fc {X : FinCofinSet}
    (hX : X ≠ finCofinBL.bot) : ∃ k : Nat, X.1 k := by
  cases Classical.em (∃ k : Nat, X.1 k) with
  | inl h => exact h
  | inr h =>
    apply False.elim (hX (Subtype.ext (funext fun n => propext ?_)))
    exact ⟨fun hxn => False.elim (h ⟨n, hxn⟩), False.elim⟩

theorem finCofinBL_isAtomic : finCofinBL.IsAtomic := by
  intro X hX
  rcases exists_mem_of_ne_bot_fc hX with ⟨k, hxk⟩
  exact ⟨singletonFC k, isAtom_singletonFC k, fun n hn => hn.symm ▸ hxk⟩

theorem isAtom_finCofin_iff (X : FinCofinSet) :
    finCofinBL.IsAtom X ↔ ∃ k : Nat, X = singletonFC k := by
  constructor
  · intro hA
    rcases exists_mem_of_ne_bot_fc hA.1 with ⟨k, hxk⟩
    have hle : finCofinBL.le (singletonFC k) X := fun n hn => hn.symm ▸ hxk
    cases hA.2 (singletonFC k) hle with
    | inl hbot => exact False.elim ((isAtom_singletonFC k).1 hbot)
    | inr heq => exact ⟨k, heq.symm⟩
  · rintro ⟨k, rfl⟩
    exact isAtom_singletonFC k

/-- Explicit bijection `ℕ ≃ Atoms(FinCofinBL)`. -/
noncomputable def finCofinAtomsEquiv : Equiv Nat finCofinBL.Atoms where
  toFun k := ⟨singletonFC k, isAtom_singletonFC k⟩
  invFun a := Classical.choose ((isAtom_finCofin_iff a.1).mp a.2)
  left_inv k := singletonFC_injective
    (Classical.choose_spec ((isAtom_finCofin_iff (singletonFC k)).mp (isAtom_singletonFC k))).symm
  right_inv a := Subtype.ext
    (Classical.choose_spec ((isAtom_finCofin_iff a.1).mp a.2)).symm

theorem isAtom_prodFC_left (k : Nat) :
    prodFC.IsAtom (singletonFC k, finCofinBL.bot) := by
  constructor
  · intro h
    exact (isAtom_singletonFC k).1 (congrArg Prod.fst h)
  · rintro ⟨X, Y⟩ ⟨hX, hY⟩
    have hY0 : Y = finCofinBL.bot := finCofinBL.le_antisymm hY (finCofinBL.bot_le Y)
    subst hY0
    cases (isAtom_singletonFC k).2 X hX with
    | inl hx0 => subst hx0; exact Or.inl rfl
    | inr hxk => subst hxk; exact Or.inr rfl

theorem isAtom_prodFC_right (k : Nat) :
    prodFC.IsAtom (finCofinBL.bot, singletonFC k) := by
  constructor
  · intro h
    exact (isAtom_singletonFC k).1 (congrArg Prod.snd h)
  · rintro ⟨X, Y⟩ ⟨hX, hY⟩
    have hX0 : X = finCofinBL.bot := finCofinBL.le_antisymm hX (finCofinBL.bot_le X)
    subst hX0
    cases (isAtom_singletonFC k).2 Y hY with
    | inl hy0 => subst hy0; exact Or.inl rfl
    | inr hyk => subst hyk; exact Or.inr rfl

theorem prodFC_isAtomic : prodFC.IsAtomic := by
  rintro ⟨X, Y⟩ hne
  cases Classical.em (X = finCofinBL.bot) with
  | inr hX =>
    rcases finCofinBL_isAtomic X hX with ⟨a, ha, hle⟩
    rcases (isAtom_finCofin_iff a).mp ha with ⟨k, rfl⟩
    exact ⟨(singletonFC k, finCofinBL.bot), isAtom_prodFC_left k,
      ⟨hle, finCofinBL.bot_le Y⟩⟩
  | inl hX0 =>
    subst hX0
    have hY : Y ≠ finCofinBL.bot := fun hY0 => hne (Prod.ext rfl hY0)
    rcases finCofinBL_isAtomic Y hY with ⟨a, ha, hle⟩
    rcases (isAtom_finCofin_iff a).mp ha with ⟨k, rfl⟩
    exact ⟨(finCofinBL.bot, singletonFC k), isAtom_prodFC_right k,
      ⟨finCofinBL.le_refl _, hle⟩⟩

theorem isAtom_prodFC_iff (p : ProdFCCarrier) :
    prodFC.IsAtom p ↔
      (∃ k : Nat, p = (singletonFC k, finCofinBL.bot)) ∨
      (∃ k : Nat, p = (finCofinBL.bot, singletonFC k)) := by
  constructor
  · rcases p with ⟨X, Y⟩
    intro hp
    cases Classical.em (X = finCofinBL.bot) with
    | inr hX =>
      -- `(X, ⊥) ≤ (X, Y)` and `(X, ⊥) ≠ ⊥`, so `Y = ⊥` and `X` is an atom
      cases hp.2 (X, finCofinBL.bot) ⟨finCofinBL.le_refl X, finCofinBL.bot_le Y⟩ with
      | inl hb => exact False.elim (hX (congrArg Prod.fst hb))
      | inr hs =>
        have hY0 : Y = finCofinBL.bot := (congrArg Prod.snd hs).symm
        subst hY0
        have hXa : finCofinBL.IsAtom X := by
          refine ⟨hX, fun Z hZX => ?_⟩
          cases hp.2 (Z, finCofinBL.bot) ⟨hZX, finCofinBL.le_refl _⟩ with
          | inl hb => exact Or.inl (congrArg Prod.fst hb)
          | inr hs => exact Or.inr (congrArg Prod.fst hs)
        rcases (isAtom_finCofin_iff X).mp hXa with ⟨k, rfl⟩
        exact Or.inl ⟨k, rfl⟩
    | inl hX0 =>
      subst hX0
      have hY : Y ≠ finCofinBL.bot := fun hY0 => hp.1 (Prod.ext rfl hY0)
      have hYa : finCofinBL.IsAtom Y := by
        refine ⟨hY, fun Z hZY => ?_⟩
        cases hp.2 (finCofinBL.bot, Z) ⟨finCofinBL.le_refl _, hZY⟩ with
        | inl hb => exact Or.inl (congrArg Prod.snd hb)
        | inr hs => exact Or.inr (congrArg Prod.snd hs)
      rcases (isAtom_finCofin_iff Y).mp hYa with ⟨k, rfl⟩
      exact Or.inr ⟨k, rfl⟩
  · rintro (⟨k, rfl⟩ | ⟨k, rfl⟩)
    · exact isAtom_prodFC_left k
    · exact isAtom_prodFC_right k

/-- Non-shadowing classical `Bool` indicator of any proposition `P`. -/
noncomputable def cdecide (P : Prop) : Bool :=
  (Classical.propDecidable P).decide

theorem cdecide_true {P : Prop} (h : P) : cdecide P = true := by
  unfold cdecide
  cases Classical.propDecidable P with
  | isTrue _ => rfl
  | isFalse hn => exact False.elim (hn h)

theorem cdecide_false {P : Prop} (h : ¬ P) : cdecide P = false := by
  unfold cdecide
  cases Classical.propDecidable P with
  | isTrue hp => exact False.elim (h hp)
  | isFalse _ => rfl

theorem cdecide_eq_true_iff (P : Prop) : cdecide P = true ↔ P := by
  constructor
  · intro ht
    cases Classical.em P with
    | inl hp => exact hp
    | inr hnp => rw [cdecide_false hnp] at ht; exact Bool.noConfusion ht
  · exact cdecide_true

/-- Helper: extract index in `ℕ` from an atom of `ProdFC`. -/
noncomputable def prodFCAtomToNat (a : prodFC.Atoms) : Nat :=
  match h : cdecide (a.1.1 = finCofinBL.bot) with
  | false =>
    have hne : a.1.1 ≠ finCofinBL.bot := fun heq => by
      rw [cdecide_true heq] at h; exact Bool.noConfusion h
    have hatom1 : finCofinBL.IsAtom a.1.1 := by
      rcases (isAtom_prodFC_iff a.1).mp a.2 with (⟨k, hk⟩ | ⟨k, hk⟩)
      · rw [congrArg Prod.fst hk]; exact isAtom_singletonFC k
      · exact False.elim (hne (congrArg Prod.fst hk))
    2 * finCofinAtomsEquiv.invFun ⟨a.1.1, hatom1⟩
  | true =>
    have heq : a.1.1 = finCofinBL.bot := (cdecide_eq_true_iff _).mp h
    have hatom2 : finCofinBL.IsAtom a.1.2 := by
      rcases (isAtom_prodFC_iff a.1).mp a.2 with (⟨k, hk⟩ | ⟨k, hk⟩)
      · exact False.elim ((isAtom_singletonFC k).1 ( (congrArg Prod.fst hk).symm.trans heq ))
      · rw [congrArg Prod.snd hk]; exact isAtom_singletonFC k
    2 * finCofinAtomsEquiv.invFun ⟨a.1.2, hatom2⟩ + 1

/-- Explicit bijection `ℕ ≃ Atoms(ProdFC)`. -/
noncomputable def prodFCAtomsEquiv : Equiv Nat prodFC.Atoms where
  toFun n :=
    if n % 2 = 0 then ⟨(singletonFC (n / 2), finCofinBL.bot), isAtom_prodFC_left (n / 2)⟩
    else ⟨(finCofinBL.bot, singletonFC (n / 2)), isAtom_prodFC_right (n / 2)⟩
  invFun := prodFCAtomToNat
  left_inv n := by
    by_cases hn : n % 2 = 0
    · simp only [hn, ite_true]
      unfold prodFCAtomToNat
      have hc : cdecide (singletonFC (n / 2) = finCofinBL.bot) = false :=
        cdecide_false (isAtom_singletonFC (n / 2)).1
      split
      · next h =>
        dsimp only []
        have hk : finCofinAtomsEquiv.invFun ⟨singletonFC (n / 2), isAtom_singletonFC (n / 2)⟩ =
            n / 2 := finCofinAtomsEquiv.left_inv (n / 2)
        rw [hk]
        omega
      · next h => rw [hc] at h; exact Bool.noConfusion h
    · simp only [hn, ite_false]
      unfold prodFCAtomToNat
      have hc : cdecide (finCofinBL.bot = finCofinBL.bot) = true := cdecide_true rfl
      split
      · next h => rw [hc] at h; exact Bool.noConfusion h
      · next h =>
        dsimp only []
        have hk : finCofinAtomsEquiv.invFun ⟨singletonFC (n / 2), isAtom_singletonFC (n / 2)⟩ =
            n / 2 := finCofinAtomsEquiv.left_inv (n / 2)
        rw [hk]
        omega
  right_inv a := by
    apply Subtype.ext
    rcases (isAtom_prodFC_iff a.1).mp a.2 with (⟨k, hk⟩ | ⟨k, hk⟩)
    · have hfst : a.1.1 = singletonFC k := congrArg Prod.fst hk
      have hc : cdecide (a.1.1 = finCofinBL.bot) = false :=
        cdecide_false (by rw [hfst]; exact (isAtom_singletonFC k).1)
      have hinv1 : ∀ h' : finCofinBL.IsAtom a.1.1,
          finCofinAtomsEquiv.invFun ⟨a.1.1, h'⟩ = k := by
        intro h'
        have hsub : (⟨a.1.1, h'⟩ : finCofinBL.Atoms) = finCofinAtomsEquiv.toFun k :=
          Subtype.ext hfst
        rw [hsub, finCofinAtomsEquiv.left_inv]
      have hval : prodFCAtomToNat a = 2 * k := by
        unfold prodFCAtomToNat
        split
        · next h => dsimp only []; rw [hinv1]
        · next h => rw [hc] at h; exact Bool.noConfusion h
      rw [hval]
      have he : (2 * k) % 2 = 0 := by omega
      have hd : (2 * k) / 2 = k := by omega
      simp only [he, ite_true, hd]
      exact hk.symm
    · have hfst : a.1.1 = finCofinBL.bot := congrArg Prod.fst hk
      have hsnd : a.1.2 = singletonFC k := congrArg Prod.snd hk
      have hc : cdecide (a.1.1 = finCofinBL.bot) = true := cdecide_true hfst
      have hinv2 : ∀ h' : finCofinBL.IsAtom a.1.2,
          finCofinAtomsEquiv.invFun ⟨a.1.2, h'⟩ = k := by
        intro h'
        have hsub : (⟨a.1.2, h'⟩ : finCofinBL.Atoms) = finCofinAtomsEquiv.toFun k :=
          Subtype.ext hsnd
        rw [hsub, finCofinAtomsEquiv.left_inv]
      have hval : prodFCAtomToNat a = 2 * k + 1 := by
        unfold prodFCAtomToNat
        split
        · next h => rw [hc] at h; exact Bool.noConfusion h
        · next h => dsimp only []; rw [hinv2]
      rw [hval]
      have ho : ¬ ((2 * k + 1) % 2 = 0) := by omega
      have hd : (2 * k + 1) / 2 = k := by omega
      simp only [ho, ite_false, hd]
      exact hk.symm

/-- Dimension Invariant 1 (Atom-set Dimension): Explicit bijection between
    the atom sets of `FinCofinBL` and `ProdFC` (both countably infinite). -/
noncomputable def atomsEquiv_finCofin_prodFC :
    Equiv finCofinBL.Atoms prodFC.Atoms :=
  Equiv.trans finCofinAtomsEquiv.symm prodFCAtomsEquiv


/-! ### Section 4.3. Explicit `F_2`-Linear Isomorphism `(FinCofinBL, △) ≅ (ProdFC, △)` -/

/-- `F_2`-linear isomorphism between two Boolean lattices viewed as `F_2`-vector spaces
    under symmetric difference `symmDiff` and zero `bot`. -/
structure F2LinearIso {L₁ : Type u} {L₂ : Type v}
    (bl₁ : BooleanLattice L₁) (bl₂ : BooleanLattice L₂) extends Equiv L₁ L₂ where
  map_bot : toFun bl₁.bot = bl₂.bot
  map_symmDiff : ∀ x y : L₁,
    toFun (bl₁.symmDiff x y) = bl₂.symmDiff (toFun x) (toFun y)

/-- Direct-sum model `⊕_{n ∈ ℕ} F_2`: finitely-supported sequences `ℕ → Bool`. -/
def FinSuppBool := { f : Nat → Bool // ∃ B : Nat, ∀ n : Nat, B ≤ n → f n = false }

def zeroFS : FinSuppBool := ⟨fun _ => false, ⟨0, fun _ _ => rfl⟩⟩

def xorFS (f g : FinSuppBool) : FinSuppBool :=
  ⟨fun n => xor (f.1 n) (g.1 n), by
    rcases f.2 with ⟨B₁, h1⟩
    rcases g.2 with ⟨B₂, h2⟩
    refine ⟨B₁ + B₂, fun n hn => ?_⟩
    dsimp
    rw [h1 n (by omega), h2 n (by omega)]
    rfl⟩

/-- Map `FinSuppBool → FinCofinSet`: bit `0` encodes cofiniteness parity, bits `k+1`
    encode the finite exception set! -/
def fsToFC (g : FinSuppBool) : FinCofinSet :=
  ⟨fun k => xor (g.1 0) (g.1 (k + 1)) = true, by
    rcases g.2 with ⟨B, hB⟩
    cases hg0 : g.1 0 with
    | false =>
      refine Or.inl ⟨B, fun k hk => ?_⟩
      by_cases hlt : k < B
      · exact hlt
      · dsimp at hk
        rw [hB (k + 1) (by omega)] at hk
        exact Bool.noConfusion hk
    | true =>
      refine Or.inr ⟨B, fun k hnk => ?_⟩
      by_cases hlt : k < B
      · exact hlt
      · exfalso
        apply hnk
        rw [hB (k + 1) (by omega)]
        rfl⟩

/-- Inverse map `FinCofinSet → FinSuppBool`. -/
noncomputable def fcToFS (A : FinCofinSet) : FinSuppBool :=
  let b : Bool := cdecide (IsCofinNat A.1)
  ⟨fun n => match n with
    | 0 => b
    | k + 1 => xor b (cdecide (A.1 k)), by
    cases A.2 with
    | inl hf =>
      have hnc : ¬ IsCofinNat A.1 := fun hc => not_fin_and_cofin hf hc
      rcases hf with ⟨B, hB⟩
      refine ⟨B + 1, fun n hn => ?_⟩
      cases n with
      | zero => omega
      | succ k =>
        have hb : b = false := cdecide_false hnc
        have hnk : ¬ A.1 k := fun hak => by have := hB k hak; omega
        dsimp
        rw [hb, cdecide_false hnk]
        rfl
    | inr hc =>
      have hb : b = true := cdecide_true hc
      rcases hc with ⟨B, hB⟩
      refine ⟨B + 1, fun n hn => ?_⟩
      cases n with
      | zero => omega
      | succ k =>
        have hak : A.1 k := by
          cases Classical.em (A.1 k) with
          | inl h => exact h
          | inr hna => have := hB k hna; omega
        dsimp
        rw [hb, cdecide_true hak]
        rfl⟩

theorem fsToFC_fcToFS (A : FinCofinSet) : fsToFC (fcToFS A) = A := by
  apply Subtype.ext (funext fun k => propext ?_)
  change xor (cdecide (IsCofinNat A.1)) (xor (cdecide (IsCofinNat A.1)) (cdecide (A.1 k))) = true ↔
    A.1 k
  have hxor : ∀ b c : Bool, xor b (xor b c) = c := by
    intro b c; cases b <;> cases c <;> rfl
  rw [hxor]
  exact cdecide_eq_true_iff (A.1 k)

theorem fcToFS_fsToFC (g : FinSuppBool) : fcToFS (fsToFC g) = g := by
  apply Subtype.ext (funext fun n => ?_)
  rcases g.2 with ⟨B, hB⟩
  have hcof_iff : cdecide (IsCofinNat (fsToFC g).1) = g.1 0 := by
    cases hg0 : g.1 0 with
    | false =>
      apply cdecide_false
      intro hc
      have hf : IsFinNat (fsToFC g).1 := by
        refine ⟨B, fun k hk => ?_⟩
        by_cases hlt : k < B
        · exact hlt
        · change xor (g.1 0) (g.1 (k + 1)) = true at hk
          rw [hg0, hB (k + 1) (by omega)] at hk
          exact Bool.noConfusion hk
      exact not_fin_and_cofin hf hc
    | true =>
      apply cdecide_true
      refine ⟨B, fun k hnk => ?_⟩
      by_cases hlt : k < B
      · exact hlt
      · exfalso
        apply hnk
        change xor (g.1 0) (g.1 (k + 1)) = true
        rw [hg0, hB (k + 1) (by omega)]
        rfl
  cases n with
  | zero =>
    exact hcof_iff
  | succ k =>
    change xor (cdecide (IsCofinNat (fsToFC g).1))
      (cdecide (xor (g.1 0) (g.1 (k + 1)) = true)) = g.1 (k + 1)
    rw [hcof_iff]
    cases hb0 : g.1 0 <;> cases hbk : g.1 (k + 1)
    · rw [cdecide_false (by decide)]; rfl
    · rw [cdecide_true (by decide)]; rfl
    · rw [cdecide_true (by decide)]; rfl
    · rw [cdecide_false (by decide)]; rfl

theorem fsToFC_xor (f g : FinSuppBool) :
    fsToFC (xorFS f g) = finCofinBL.symmDiff (fsToFC f) (fsToFC g) := by
  apply Subtype.ext (funext fun k => propext ?_)
  change xor (xor (f.1 0) (g.1 0)) (xor (f.1 (k + 1)) (g.1 (k + 1))) = true ↔
    ((xor (f.1 0) (f.1 (k + 1)) = true ∧ ¬ (xor (g.1 0) (g.1 (k + 1)) = true)) ∨
     (¬ (xor (f.1 0) (f.1 (k + 1)) = true) ∧ xor (g.1 0) (g.1 (k + 1)) = true))
  cases f.1 0 <;> cases g.1 0 <;> cases f.1 (k + 1) <;> cases g.1 (k + 1) <;> decide

/-- Interleaving isomorphism `FinSuppBool × FinSuppBool ≃ FinSuppBool`. -/
def interleaveFS : Equiv (FinSuppBool × FinSuppBool) FinSuppBool where
  toFun p := ⟨fun n => if n % 2 = 0 then p.1.1 (n / 2) else p.2.1 (n / 2), by
    rcases p.1.2 with ⟨B₁, h1⟩
    rcases p.2.2 with ⟨B₂, h2⟩
    refine ⟨2 * (B₁ + B₂), fun n hn => ?_⟩
    by_cases he : n % 2 = 0
    · simp only [he, ite_true]
      exact h1 (n / 2) (by omega)
    · simp only [he, ite_false]
      exact h2 (n / 2) (by omega)⟩
  invFun h :=
    (⟨fun k => h.1 (2 * k), by
       rcases h.2 with ⟨B, hB⟩
       exact ⟨B, fun k hk => hB (2 * k) (by omega)⟩⟩,
     ⟨fun k => h.1 (2 * k + 1), by
       rcases h.2 with ⟨B, hB⟩
       exact ⟨B, fun k hk => hB (2 * k + 1) (by omega)⟩⟩)
  left_inv p := by
    rcases p with ⟨f, g⟩
    apply Prod.ext
    · apply Subtype.ext (funext fun k => ?_)
      dsimp
      have he : (2 * k) % 2 = 0 := by omega
      have hd : (2 * k) / 2 = k := by omega
      simp only [he, ite_true, hd]
    · apply Subtype.ext (funext fun k => ?_)
      dsimp
      have ho : ¬ ((2 * k + 1) % 2 = 0) := by omega
      have hd : (2 * k + 1) / 2 = k := by omega
      simp only [ho, ite_false, hd]
  right_inv h := by
    apply Subtype.ext (funext fun n => ?_)
    dsimp
    by_cases he : n % 2 = 0
    · simp only [he, ite_true]
      exact congrArg h.1 (by omega)
    · simp only [he, ite_false]
      exact congrArg h.1 (by omega)

theorem interleaveFS_inv_xor (h₁ h₂ : FinSuppBool) :
    interleaveFS.invFun (xorFS h₁ h₂) =
      (xorFS (interleaveFS.invFun h₁).1 (interleaveFS.invFun h₂).1,
       xorFS (interleaveFS.invFun h₁).2 (interleaveFS.invFun h₂).2) :=
  Prod.ext (Subtype.ext (funext fun _ => rfl)) (Subtype.ext (funext fun _ => rfl))

/-- Dimension Invariant 2 (`F_2`-Vector-Space Dimension & Underlying Cardinality):
    Explicit `F_2`-linear bijection `(FinCofinBL, △, ⊥) ≃_{F_2} (ProdFC, △, ⊥)`. -/
noncomputable def f2LinearIso_finCofin_prodFC : F2LinearIso finCofinBL prodFC where
  toFun A :=
    let q := interleaveFS.invFun (fcToFS A)
    (fsToFC q.1, fsToFC q.2)
  invFun p :=
    fsToFC (interleaveFS.toFun (fcToFS p.1, fcToFS p.2))
  left_inv A := by
    dsimp
    rw [fcToFS_fsToFC, fcToFS_fsToFC, interleaveFS.right_inv, fsToFC_fcToFS]
  right_inv p := by
    rcases p with ⟨A, B⟩
    dsimp
    rw [fcToFS_fsToFC, interleaveFS.left_inv]
    exact Prod.ext (fsToFC_fcToFS A) (fsToFC_fcToFS B)
  map_bot := by
    have hzero : fcToFS finCofinBL.bot = zeroFS := by
      have h0 : fsToFC zeroFS = finCofinBL.bot :=
        Subtype.ext (funext fun _ => propext ⟨fun h => Bool.noConfusion h, False.elim⟩)
      rw [← h0, fcToFS_fsToFC]
    dsimp
    rw [hzero]
    have hi0 : interleaveFS.invFun zeroFS = (zeroFS, zeroFS) :=
      Prod.ext (Subtype.ext (funext fun _ => rfl)) (Subtype.ext (funext fun _ => rfl))
    rw [hi0]
    exact Prod.ext
      (Subtype.ext (funext fun _ => propext ⟨fun h => Bool.noConfusion h, False.elim⟩))
      (Subtype.ext (funext fun _ => propext ⟨fun h => Bool.noConfusion h, False.elim⟩))
  map_symmDiff A B := by
    have hfc_xor : fcToFS (finCofinBL.symmDiff A B) = xorFS (fcToFS A) (fcToFS B) := by
      conv => lhs; rw [← fsToFC_fcToFS A, ← fsToFC_fcToFS B, ← fsToFC_xor, fcToFS_fsToFC]
    dsimp
    rw [hfc_xor, interleaveFS_inv_xor, fsToFC_xor, fsToFC_xor]
    rfl

/-- Dimension Invariant 3 (Poset Chain Height): Strict chain of length `m`. -/
def HasStrictChain {L : Type u} (bl : BooleanLattice L) (m : Nat) : Prop :=
  ∃ c : Nat → L, ∀ i : Nat, i < m → bl.Lt (c i) (c (i + 1))

def prefixFC (k : Nat) : FinCofinSet :=
  ⟨fun n => n < k, Or.inl ⟨k, fun _ h => h⟩⟩

/-- Both `FinCofinBL` and `ProdFC` have unbounded finite strictly increasing chains
    (poset chain height `= ∞`). -/
theorem unbounded_chains_finCofin_and_prodFC (m : Nat) :
    HasStrictChain finCofinBL m ∧ HasStrictChain prodFC m := by
  have h1 : ∀ i : Nat, finCofinBL.Lt (prefixFC i) (prefixFC (i + 1)) := by
    intro i
    refine ⟨fun n hn => by dsimp [prefixFC] at *; omega, fun heq => ?_⟩
    have hi : (prefixFC (i + 1)).1 i := by dsimp [prefixFC]; omega
    rw [← heq] at hi
    dsimp [prefixFC] at hi
    omega
  refine ⟨⟨prefixFC, fun i _ => h1 i⟩,
          ⟨fun i => (prefixFC i, finCofinBL.bot), fun i _ => ?_⟩⟩
  refine ⟨⟨(h1 i).1, finCofinBL.le_refl _⟩, fun heq => (h1 i).2 (congrArg Prod.fst heq)⟩


/-! ### Section 4.4. Proof that `FinCofinBL ≇ ProdFC` as Boolean Lattices -/

/-- Purely lattice-theoretic property: `x` lies above infinitely many distinct atoms. -/
def HasInfinitelyManyAtomsBelow {L : Type u} (bl : BooleanLattice L) (x : L) : Prop :=
  ∃ f : Nat → L,
    (∀ k : Nat, bl.IsAtom (f k)) ∧
    (∀ i j : Nat, f i = f j → i = j) ∧
    (∀ k : Nat, bl.le (f k) x)

theorem BLIso.map_hasInfinitelyManyAtomsBelow {L₁ : Type u} {L₂ : Type v}
    {bl₁ : BooleanLattice L₁} {bl₂ : BooleanLattice L₂}
    (iso : BLIso bl₁ bl₂) {x : L₁}
    (hx : HasInfinitelyManyAtomsBelow bl₁ x) :
    HasInfinitelyManyAtomsBelow bl₂ (iso.toFun x) := by
  rcases hx with ⟨f, hatom, hinj, hle⟩
  refine ⟨fun k => iso.toFun (f k), fun k => iso.map_isAtom (hatom k),
          fun i j hij => hinj i j (iso.toEquiv.injective hij),
          fun k => (iso.map_le (f k) x).mpr (hle k)⟩

/-- Constructive Pigeonhole Principle on `ℕ`: no injective `g : ℕ → ℕ` can have
    its entire range strictly bounded by `B`. -/
theorem no_inj_nat_lt :
    ∀ (B : Nat) (g : Nat → Nat),
      (∀ i j : Nat, g i = g j → i = j) → ¬ (∀ k : Nat, g k < B)
  | 0, g, _, hlt => by have := hlt 0; omega
  | B + 1, g, hinj, hlt => by
    cases Classical.em (∃ k₀ : Nat, g k₀ = B) with
    | inr hno =>
      exact no_inj_nat_lt B g hinj fun k => by
        have h1 := hlt k
        have h2 : g k ≠ B := fun heq => hno ⟨k, heq⟩
        omega
    | inl hex =>
      rcases hex with ⟨k₀, hk₀⟩
      let g' : Nat → Nat := fun k => if k < k₀ then g k else g (k + 1)
      have hinj' : ∀ i j : Nat, g' i = g' j → i = j := by
        intro i j hij
        dsimp [g'] at hij
        split at hij <;> split at hij
        · exact hinj i j hij
        · have := hinj i (j + 1) hij; omega
        · have := hinj (i + 1) j hij; omega
        · have := hinj (i + 1) (j + 1) hij; omega
      have hlt' : ∀ k : Nat, g' k < B := by
        intro k
        dsimp [g']
        split
        · next hlt_k =>
          have h1 := hlt k
          have hne : g k ≠ B := fun heq => by
            have := hinj k k₀ (heq.trans hk₀.symm); omega
          omega
        · next hge_k =>
          have h1 := hlt (k + 1)
          have hne : g (k + 1) ≠ B := fun heq => by
            have := hinj (k + 1) k₀ (heq.trans hk₀.symm); omega
          omega
      exact no_inj_nat_lt B g' hinj' hlt'

/-- In `FinCofinBL`, no finite subset can contain infinitely many distinct atoms. -/
theorem not_hasInfinitelyManyAtomsBelow_of_isFinNat
    {A : FinCofinSet} (hf : IsFinNat A.1) :
    ¬ HasInfinitelyManyAtomsBelow finCofinBL A := by
  rcases hf with ⟨B, hB⟩
  rintro ⟨f, hatom, hinj, hle⟩
  let g : Nat → Nat := fun k =>
    Classical.choose ((isAtom_finCofin_iff (f k)).mp (hatom k))
  have hg_spec : ∀ k : Nat, f k = singletonFC (g k) :=
    fun k => Classical.choose_spec ((isAtom_finCofin_iff (f k)).mp (hatom k))
  have hg_inj : ∀ i j : Nat, g i = g j → i = j := by
    intro i j hij
    apply hinj i j
    rw [hg_spec i, hg_spec j, hij]
  have hg_lt : ∀ k : Nat, g k < B := by
    intro k
    have hmem : A.1 (g k) := by
      have hk := hle k (g k)
      rw [hg_spec k] at hk
      exact hk rfl
    exact hB (g k) hmem
  exact no_inj_nat_lt B g hg_inj hg_lt

/-- Structural Obstruction in `FinCofinBL`: NO element `A` and its complement `Aᶜ`
    can BOTH lie above infinitely many distinct atoms! -/
theorem finCofin_not_both_infinite_atoms (A : FinCofinSet) :
    ¬ (HasInfinitelyManyAtomsBelow finCofinBL A ∧
       HasInfinitelyManyAtomsBelow finCofinBL (finCofinBL.compl A)) := by
  rintro ⟨hA, hAc⟩
  cases A.2 with
  | inl hf => exact not_hasInfinitelyManyAtomsBelow_of_isFinNat hf hA
  | inr hc => exact not_hasInfinitelyManyAtomsBelow_of_isFinNat (A := finCofinBL.compl A) hc hAc

/-- Conversely, in `ProdFC`, `u = (⊤, ⊥)` and `uᶜ = (⊥, ⊤)` BOTH lie above
    infinitely many distinct atoms! -/
theorem prodFC_exists_both_infinite_atoms :
    ∃ u : ProdFCCarrier,
      HasInfinitelyManyAtomsBelow prodFC u ∧
      HasInfinitelyManyAtomsBelow prodFC (prodFC.compl u) := by
  refine ⟨(finCofinBL.top, finCofinBL.bot), ?_, ?_⟩
  · refine ⟨fun k => (singletonFC k, finCofinBL.bot),
            isAtom_prodFC_left,
            fun i j hij => singletonFC_injective (congrArg Prod.fst hij),
            fun k => ⟨finCofinBL.le_top _, finCofinBL.le_refl _⟩⟩
  · refine ⟨fun k => (finCofinBL.bot, singletonFC k),
            isAtom_prodFC_right,
            fun i j hij => singletonFC_injective (congrArg Prod.snd hij),
            fun k => ⟨finCofinBL.bot_le _, fun _ _ hf => hf⟩⟩

/-- Theorem B2 (Refutation of Clause III):
    `FinCofinBL` and `ProdFC` are NOT isomorphic as Boolean lattices, despite
    sharing the same atomicity, atom-set cardinality (`ℕ`), `F_2`-vector-space
    isomorphism type, poset chain height (`∞`), and underlying cardinality (`ℵ_0`)! -/
theorem not_blIso_finCofin_prodFC :
    ¬ Nonempty (BLIso finCofinBL prodFC) := by
  rintro ⟨iso⟩
  rcases prodFC_exists_both_infinite_atoms with ⟨u, hu, huc⟩
  let A := iso.symm.toFun u
  have hA : HasInfinitelyManyAtomsBelow finCofinBL A :=
    iso.symm.map_hasInfinitelyManyAtomsBelow hu
  have hAc : HasInfinitelyManyAtomsBelow finCofinBL (finCofinBL.compl A) := by
    have hm := iso.symm.map_hasInfinitelyManyAtomsBelow huc
    rw [iso.symm.map_compl] at hm
    exact hm
  exact finCofin_not_both_infinite_atoms A ⟨hA, hAc⟩


/-! ## Section 5. Master Conjecture Statements and Complete Disproofs -/

/-- Exact formalization of Conjecture 00000008543 over general Boolean lattices
    (parameterized over ANY admissible notions of `IrreducibleAut`,
    `TranspositionType`, and `SameDimension` chosen from the standard definitions,
    or concretely bundled with the weakest conclusion / strongest hypothesis so its
    negation is maximally strong!).

    Specifically, if Conjecture 00000008543 held, then for every Boolean lattice `bl`:
    (Clause I)   `∃ X, Aut(bl) ≅ Sym(X)`, AND
    (Clause II)  every direct-factor AND cycle-irreducible (and sublattice-simple)
                 automorphism satisfies at least `f² = 1` (involution / transposition
                 type), AND
    (Clause III) any two atomic Boolean lattices with `Atoms L₁ ≃ Atoms L₂` and
                 `(L₁, △, ⊥) ≃_{F_2} (L₂, △, ⊥)` are isomorphic as Boolean lattices. -/
def Conjecture00000008543_General : Prop :=
  -- Clause I: Automorphism group of every Boolean lattice is a symmetric group
  (∀ (L : Type) (bl : BooleanLattice L),
    ∃ (X : Type), Nonempty (GroupIso (blAutGroup bl) (permGroup X))) ∧
  -- Clause II: Irreducible automorphisms are of transposition type (hence involutions)
  (∀ (L : Type) (bl : BooleanLattice L) (f : BLAut bl),
    IsDirectFactorIrreducible bl f →
    IsSublatticeIrreducible bl f →
    IsCycleIrreducible bl f →
    IsInvolutionAut bl f) ∧
  -- Clause III: Isomorphism classification is uniquely determined by dimension
  (∀ (L₁ L₂ : Type) (bl₁ : BooleanLattice L₁) (bl₂ : BooleanLattice L₂),
    bl₁.IsAtomic → bl₂.IsAtomic →
    Nonempty (Equiv bl₁.Atoms bl₂.Atoms) →
    Nonempty (F2LinearIso bl₁ bl₂) →
    Nonempty (BLIso bl₁ bl₂))

/-- Master Theorem 1: Conjecture 00000008543 is FALSE. -/
theorem conjecture_00000008543_disproved : ¬ Conjecture00000008543_General := by
  rintro ⟨hClause1, _, _⟩
  rcases hClause1 HybridCarrier hybridBL with ⟨X, hIso⟩
  exact hybridBL_aut_not_iso_any_perm X hIso

/-- Master Theorem 2 (Strong Triple Disproof): ALL THREE individual clauses of
    Conjecture 00000008543 are INDEPENDENTLY FALSE over general Boolean lattices! -/
theorem conjecture_00000008543_all_three_clauses_false :
    -- 1. Negation of Clause I (fails BOTH for `Perm(Atoms L)` and for `Perm X` over ALL `X`)
    (∃ (L : Type) (bl : BooleanLattice L),
      ¬ Nonempty (GroupIso (blAutGroup bl) (permGroup bl.Atoms)) ∧
      ∀ (X : Type), ¬ Nonempty (GroupIso (blAutGroup bl) (permGroup X))) ∧
    -- 2. Negation of Clause II (fails already on finite `B_3` under ALL 4 irreducibility
    --    definitions and ALL 3 transposition-type definitions!)
    (∃ (L : Type) (bl : BooleanLattice L) (f : BLAut bl),
      IsDirectFactorIrreducible bl f ∧
      IsSublatticeIrreducible bl f ∧
      IsCycleIrreducible bl f ∧
      ¬ IsAtomTransposition bl f ∧
      ¬ IsConjugateToAtomTransposition bl f ∧
      ¬ IsInvolutionAut bl f) ∧
    -- 3. Negation of Clause III (two atomic Boolean lattices with identical atom dimension,
    --    identical F_2-linear dimension, identical chain rank ∞, and identical cardinality
    --    that are NOT isomorphic!)
    (∃ (L₁ L₂ : Type) (bl₁ : BooleanLattice L₁) (bl₂ : BooleanLattice L₂),
      bl₁.IsAtomic ∧ bl₂.IsAtomic ∧
      Nonempty (Equiv bl₁.Atoms bl₂.Atoms) ∧
      Nonempty (F2LinearIso bl₁ bl₂) ∧
      (∀ m : Nat, HasStrictChain bl₁ m ∧ HasStrictChain bl₂ m) ∧
      ¬ Nonempty (BLIso bl₁ bl₂)) := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨HybridCarrier, hybridBL, ?_, hybridBL_aut_not_iso_any_perm⟩
    exact hybridBL_aut_not_iso_any_perm hybridBL.Atoms
  · exact ⟨FinBool 3, finBoolBL 3, cycleAut 2,
      cycleAut_isDirectFactorIrreducible 2,
      cycleAut3_isSublatticeIrreducible,
      cycleAut_isCycleIrreducible 1,
      cycleAut_not_atomTransposition 0,
      cycleAut_not_conjugateTransposition 0,
      cycleAut_not_involution 0⟩
  · exact ⟨FinCofinSet, ProdFCCarrier, finCofinBL, prodFC,
      finCofinBL_isAtomic, prodFC_isAtomic,
      ⟨atomsEquiv_finCofin_prodFC⟩,
      ⟨f2LinearIso_finCofin_prodFC⟩,
      unbounded_chains_finCofin_and_prodFC,
      not_blIso_finCofin_prodFC⟩

/-- Exact formalization of Conjecture 00000008543 restricted to FINITE Boolean lattices `B_n`. -/
def Conjecture00000008543_Finite : Prop :=
  -- Clause I (finite): Aut(B_n) ≅ S_n
  (∀ n : Nat, Nonempty (GroupIso (blAutGroup (finBoolBL n)) (permGroup (Fin n)))) ∧
  -- Clause II (finite): Irreducible automorphisms of B_n are of transposition type
  (∀ n : Nat, ∀ f : BLAut (finBoolBL n),
    (IsDirectFactorIrreducible (finBoolBL n) f ∧ IsCycleIrreducible (finBoolBL n) f) →
    IsInvolutionAut (finBoolBL n) f) ∧
  -- Clause III (finite): B_m ≅ B_n ↔ m = n
  (∀ m n : Nat, Nonempty (BLIso (finBoolBL m) (finBoolBL n)) ↔ m = n)

/-- Master Theorem 3 (Finite Restriction Disproof):
    Even when restricted strictly to FINITE Boolean lattices `B_n` (where Clauses I
    and III DO hold!), Conjecture 00000008543 is STILL FALSE — and fails in EVERY
    dimension `d = n + 3 ≥ 3`! -/
theorem conjecture_00000008543_finite_disproved :
    ¬ Conjecture00000008543_Finite ∧
    (∀ n : Nat,
      IsDirectFactorIrreducible (finBoolBL (n + 3)) (cycleAut (n + 2)) ∧
      IsCycleIrreducible (finBoolBL (n + 3)) (cycleAut (n + 2)) ∧
      ¬ IsAtomTransposition (finBoolBL (n + 3)) (cycleAut (n + 2)) ∧
      ¬ IsConjugateToAtomTransposition (finBoolBL (n + 3)) (cycleAut (n + 2)) ∧
      ¬ IsInvolutionAut (finBoolBL (n + 3)) (cycleAut (n + 2)) ∧
      ∀ g : BLAut (finBoolBL (n + 3)),
        IsAtomTransposition (finBoolBL (n + 3)) g →
        ¬ IsDirectFactorIrreducible (finBoolBL (n + 3)) g) ∧
    IsF2ReducedIrreducible3 (cycleAut 2) := by
  refine ⟨?_, ?_, cycleAut3_isF2ReducedIrreducible⟩
  · rintro ⟨_, hClause2, _⟩
    exact cycleAut_not_involution 0
      (hClause2 3 (cycleAut 2)
        ⟨cycleAut_isDirectFactorIrreducible 2, cycleAut_isCycleIrreducible 1⟩)
  · intro n
    exact ⟨cycleAut_isDirectFactorIrreducible (n + 2),
           cycleAut_isCycleIrreducible (n + 1),
           cycleAut_not_atomTransposition n,
           cycleAut_not_conjugateTransposition n,
           cycleAut_not_involution n,
           atomTransposition_not_directFactorIrreducible n⟩

end Conjecture00000008543

/-! ## Axiom Verification (`#print axioms`) -/

#print axioms Conjecture00000008543.blIso_iff_algHom
#print axioms Conjecture00000008543.finBoolAutGroupIso
#print axioms Conjecture00000008543.finBool_iso_iff_eq
#print axioms Conjecture00000008543.finBool2_nonid_isAtomTransposition
#print axioms Conjecture00000008543.hybridBL_aut_not_iso_any_perm
#print axioms Conjecture00000008543.not_blIso_finCofin_prodFC
#print axioms Conjecture00000008543.conjecture_00000008543_disproved
#print axioms Conjecture00000008543.conjecture_00000008543_all_three_clauses_false
#print axioms Conjecture00000008543.conjecture_00000008543_finite_disproved

