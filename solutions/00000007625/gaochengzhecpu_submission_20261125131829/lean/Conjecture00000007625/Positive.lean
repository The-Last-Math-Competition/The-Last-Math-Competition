/-
  Conjecture 00000007625 — Positive Regime: Central Block Uniqueness & K^t

  Proves:
  1. General Wedderburn-Artin Central Block Theorem (`central_block_minimal_ideals_exactCard`,
     `central_block_central_prim_exactCard`, `central_block_decomp_uniqueness`):
     In any unital ring R admitting a decomposition 1 = c_1 + ... + c_t into
     pairwise orthogonal simple central blocks:
       (a) The minimal nonzero two-sided ideals of R have exact cardinality t.
       (b) The central primitive idempotents of R have exact cardinality t.
       (c) Every central primitive orthogonal decomposition of 1 has exact
           length t, and the unordered set {c_1, ..., c_t} is unique (card 1).
  2. Concrete Non-Vacuity Family (`F3PowRing (m + 1)` for all m : Nat, and
     explicit Clifford isomorphism `Cl_{1,0}(F_3) ≅ F_3 × F_3`):
     In split commutative semisimple algebras F_3^n, every idempotent is
     central, minimal left ideals coincide with minimal two-sided ideals, and
     every primitive orthogonal idempotent decomposition has length n equal to
     both minimal-ideal counts.
-/

import Conjecture00000007625.Basic

namespace Conjecture00000007625

/-! ## 1. Abstract Central Block Uniqueness & Minimal Two-Sided Ideal Count -/

def BlockIdeal {α : Type u} (R : UnitalRing α) (c : α) : α → Prop :=
  fun x => R.mul x c = x

def IsSimpleCentralBlock {α : Type u} (R : UnitalRing α) (c : α) : Prop :=
  IsCentralIdempotent R c ∧ c ≠ R.zero ∧
    ∀ I : α → Prop,
      IsTwoSidedIdeal R I →
      (∃ x : α, I x ∧ R.mul x c ≠ R.zero) →
      I c

theorem blockIdeal_isTwoSidedIdeal {α : Type u} (R : UnitalRing α) {c : α}
    (hc : IsCentral R c) : IsTwoSidedIdeal R (BlockIdeal R c) := by
  have hAdd : IsAddSubgroup R (BlockIdeal R c) := by
    refine ⟨R.zero_mul c, ?_, ?_⟩
    · intro a b ha hb
      unfold BlockIdeal at *
      rw [R.right_distrib, ha, hb]
    · intro a ha
      unfold BlockIdeal at *
      rw [R.neg_mul, ha]
  refine ⟨⟨hAdd, ?_⟩, ⟨hAdd, ?_⟩⟩
  · intro r x hx
    unfold BlockIdeal at *
    rw [R.mul_assoc, hx]
  · intro x r hx
    unfold BlockIdeal at *
    rw [R.mul_assoc, ← hc r, ← R.mul_assoc, hx]

theorem blockIdeal_isMinimalTwoSidedIdeal {α : Type u} (R : UnitalRing α) {c : α}
    (hB : IsSimpleCentralBlock R c) :
    IsMinimalTwoSidedIdeal R (BlockIdeal R c) := by
  obtain ⟨⟨hcidem, hccent⟩, hcne, hsimp⟩ := hB
  refine ⟨blockIdeal_isTwoSidedIdeal R hccent, ⟨c, hcidem, hcne⟩, ?_⟩
  intro J hJ ⟨x, hxJ, hxne⟩ hsub y hy
  have hxc : R.mul x c ≠ R.zero := by
    rw [hsub x hxJ]
    exact hxne
  have hcJ : J c := hsimp J hJ ⟨x, hxJ, hxc⟩
  have hyc : R.mul y c = y := hy
  rw [← hyc]
  exact hJ.1.2 y c hcJ

theorem centralIdemp_mul_simpleBlock {α : Type u} (R : UnitalRing α) {c z : α}
    (hB : IsSimpleCentralBlock R c) (hz : IsCentralIdempotent R z) :
    R.mul z c = R.zero ∨ R.mul z c = c := by
  obtain ⟨⟨hcidem, hccent⟩, _, hsimp⟩ := hB
  obtain ⟨hzidem, hzcent⟩ := hz
  let w : α := R.mul z c
  by_cases hw : w = R.zero
  · exact Or.inl hw
  · right
    have hwcent : IsCentral R w := by
      intro x
      dsimp [w]
      rw [R.mul_assoc, hccent x, ← R.mul_assoc, hzcent x, R.mul_assoc]
    have hwc : R.mul w c = w := by
      dsimp [w]
      rw [R.mul_assoc, hcidem]
    have hwidem : IsIdempotent R w := by
      dsimp [IsIdempotent, w]
      rw [R.mul_assoc, ← R.mul_assoc c z c, hccent z, R.mul_assoc z c c,
          hcidem, ← R.mul_assoc z z c, hzidem]
    have hIw_ideal : IsTwoSidedIdeal R (BlockIdeal R w) :=
      blockIdeal_isTwoSidedIdeal R hwcent
    have hc_in_Iw : BlockIdeal R w c := by
      apply hsimp (BlockIdeal R w) hIw_ideal
      refine ⟨w, hwidem, ?_⟩
      rw [hwc]
      exact hw
    unfold BlockIdeal at hc_in_Iw
    have hcw : R.mul c w = w := by
      dsimp [w]
      rw [← R.mul_assoc, hccent z, R.mul_assoc, hcidem]
    exact hcw.symm.trans hc_in_Iw

theorem simpleBlock_isCentralPrimitive {α : Type u} (R : UnitalRing α) {c : α}
    (hB : IsSimpleCentralBlock R c) :
    IsCentralPrimitiveIdempotent R c := by
  refine ⟨hB.1, hB.2.1, ?_⟩
  intro ⟨f, g, hfci, hfne, _, hgne, hfg_orth, hfg_sum⟩
  have hfc : R.mul f c = f := by
    rw [← hfg_sum, R.left_distrib, hfci.1, hfg_orth.1, R.add_zero]
  cases centralIdemp_mul_simpleBlock R hB hfci with
  | inl hz =>
    rw [hfc] at hz
    exact hfne hz
  | inr heq =>
    rw [hfc] at heq
    subst heq
    have hg0 : g = R.zero := by
      apply R.add_left_cancel (a := f)
      rw [hfg_sum, R.add_zero]
    exact hgne hg0

theorem centralPrim_eq_some_block {α : Type u} (R : UnitalRing α) {t : Nat}
    {c : Fin t → α} (hdecomp : IsOrthIdempDecomp R t c)
    (hblocks : ∀ j : Fin t, IsSimpleCentralBlock R (c j))
    {d : α} (hd : IsCentralPrimitiveIdempotent R d) :
    ∃ j : Fin t, c j = d := by
  obtain ⟨hdci, hdne, hdprim⟩ := hd
  have hsum : finSum R t (fun j => R.mul d (c j)) = d := by
    rw [← mul_finSum, hdecomp.2.2, R.mul_one]
  have hnz_sum : finSum R t (fun j => R.mul d (c j)) ≠ R.zero := by
    rw [hsum]; exact hdne
  obtain ⟨j, hjne⟩ := exists_nonzero_of_finSum_ne_zero R hnz_sum
  have hdc : R.mul d (c j) = c j := by
    cases centralIdemp_mul_simpleBlock R (hblocks j) hdci with
    | inl h0 => exact absurd h0 hjne
    | inr h1 => exact h1
  let f : α := c j
  let g : α := R.sub d f
  by_cases hg0 : g = R.zero
  · exact ⟨j, (R.sub_eq_zero.mp hg0).symm⟩
  · exfalso
    apply hdprim
    have hfci : IsCentralIdempotent R f := (hblocks j).1
    have hfne : f ≠ R.zero := (hblocks j).2.1
    have hcd : R.mul f d = f := by
      dsimp [f]
      rw [(hblocks j).1.2 d, hdc]
    have hfg1 : R.mul f g = R.zero := by
      dsimp [g]
      rw [R.mul_sub, hcd, hfci.1, R.sub_self]
    have hgf1 : R.mul g f = R.zero := by
      dsimp [g]
      rw [R.sub_mul, hdc, hfci.1, R.sub_self]
    have hgidem : IsIdempotent R g := by
      unfold IsIdempotent
      calc
        R.mul g g = R.mul g (R.sub d f) := rfl
        _ = R.sub (R.mul g d) (R.mul g f) := R.mul_sub g d f
        _ = R.sub (R.mul g d) R.zero := by rw [hgf1]
        _ = R.mul g d := by unfold UnitalRing.sub; rw [R.neg_zero, R.add_zero]
        _ = R.sub (R.mul d d) (R.mul f d) := R.sub_mul d f d
        _ = R.sub d f := by rw [hdci.1, hcd]
        _ = g := rfl
    have hgcent : IsCentral R g := by
      intro x
      dsimp [g, UnitalRing.sub]
      rw [R.right_distrib, R.left_distrib, hdci.2 x, R.neg_mul, R.mul_neg, hfci.2 x]
    exact ⟨f, g, hfci, hfne, ⟨hgidem, hgcent⟩, hg0, ⟨hfg1, hgf1⟩, R.add_sub_cancel_left f d⟩

theorem central_block_minimal_ideals_exactCard {α : Type u} (R : UnitalRing α)
    {t : Nat} {c : Fin t → α} (hdecomp : IsOrthIdempDecomp R t c)
    (hblocks : ∀ j : Fin t, IsSimpleCentralBlock R (c j)) :
    ExactCard (IsMinimalTwoSidedIdeal R) t := by
  refine ⟨fun j => BlockIdeal R (c j), ?_, ?_, ?_⟩
  · intro j
    exact blockIdeal_isMinimalTwoSidedIdeal R (hblocks j)
  · intro i j hij
    apply Classical.byContradiction
    intro hne
    have hci : BlockIdeal R (c i) (c i) := (hdecomp.1 i).1
    have hij' : BlockIdeal R (c i) = BlockIdeal R (c j) := hij
    rw [hij'] at hci
    unfold BlockIdeal at hci
    rw [(hdecomp.2.1 i j hne).1] at hci
    exact (hdecomp.1 i).2 hci.symm
  · intro I hI
    obtain ⟨hI_two, ⟨x, hxI, hxne⟩, hI_min⟩ := hI
    have hsum : finSum R t (fun j => R.mul x (c j)) = x := by
      rw [← mul_finSum, hdecomp.2.2, R.mul_one]
    have hnz : finSum R t (fun j => R.mul x (c j)) ≠ R.zero := by
      rw [hsum]; exact hxne
    obtain ⟨j, hjne⟩ := exists_nonzero_of_finSum_ne_zero R hnz
    have hcj_in_I : I (c j) := (hblocks j).2.2 I hI_two ⟨x, hxI, hjne⟩
    have hsub : ∀ y : α, BlockIdeal R (c j) y → I y := by
      intro y hy
      rw [← hy]
      exact hI_two.1.2 y (c j) hcj_in_I
    have hsup : ∀ y : α, I y → BlockIdeal R (c j) y :=
      hI_min (BlockIdeal R (c j))
        (blockIdeal_isTwoSidedIdeal R (hblocks j).1.2)
        ⟨c j, (hdecomp.1 j).1, (hdecomp.1 j).2⟩
        hsub
    refine ⟨j, ?_⟩
    funext y
    exact propext ⟨hsub y, hsup y⟩

theorem central_block_central_prim_exactCard {α : Type u} (R : UnitalRing α)
    {t : Nat} {c : Fin t → α} (hdecomp : IsOrthIdempDecomp R t c)
    (hblocks : ∀ j : Fin t, IsSimpleCentralBlock R (c j)) :
    ExactCard (IsCentralPrimitiveIdempotent R) t := by
  refine ⟨c, ?_, ?_, ?_⟩
  · intro j
    exact simpleBlock_isCentralPrimitive R (hblocks j)
  · intro i j hij
    apply Classical.byContradiction
    intro hne
    have hmul : R.mul (c i) (c j) = R.zero := (hdecomp.2.1 i j hne).1
    rw [← hij, (hdecomp.1 i).1] at hmul
    exact (hdecomp.1 i).2 hmul
  · intro d hd
    exact centralPrim_eq_some_block R hdecomp hblocks hd

theorem central_block_decomp_uniqueness {α : Type u} (R : UnitalRing α)
    {t : Nat} {c : Fin t → α} (hdecomp : IsOrthIdempDecomp R t c)
    (hblocks : ∀ j : Fin t, IsSimpleCentralBlock R (c j)) :
    (∀ (s : Nat) (d : Fin s → α),
      IsCentralPrimDecomp R s d →
      s = t ∧ (fun x => ∃ i : Fin s, x = d i) = (fun x => ∃ j : Fin t, x = c j)) ∧
    ExactCard (IsUnordCentralPrimDecomp R) 1 := by
  have hc_prim : IsCentralPrimDecomp R t c :=
    ⟨hdecomp, fun j => simpleBlock_isCentralPrimitive R (hblocks j)⟩
  have hmain : ∀ (s : Nat) (d : Fin s → α),
      IsCentralPrimDecomp R s d →
      s = t ∧ (fun x => ∃ i : Fin s, x = d i) = (fun x => ∃ j : Fin t, x = c j) := by
    intro s d hd
    have hd_inj : ∀ i₁ i₂ : Fin s, d i₁ = d i₂ → i₁ = i₂ := by
      intro i₁ i₂ heq
      apply Classical.byContradiction
      intro hne
      have h0 : R.mul (d i₁) (d i₂) = R.zero := (hd.1.2.1 i₁ i₂ hne).1
      rw [← heq, (hd.1.1 i₁).1] at h0
      exact (hd.1.1 i₁).2 h0
    have hset : (fun x => ∃ i : Fin s, x = d i) = (fun x => ∃ j : Fin t, x = c j) := by
      funext x
      apply propext
      constructor
      · intro ⟨i, hxi⟩
        subst hxi
        obtain ⟨j, hj⟩ := centralPrim_eq_some_block R hdecomp hblocks (hd.2 i)
        exact ⟨j, hj.symm⟩
      · intro ⟨j, hxj⟩
        subst hxj
        have hsum : finSum R s (fun i => R.mul (c j) (d i)) = c j := by
          rw [← mul_finSum, hd.1.2.2, R.mul_one]
        have hnz : finSum R s (fun i => R.mul (c j) (d i)) ≠ R.zero := by
          rw [hsum]; exact (hdecomp.1 j).2
        obtain ⟨i, hine⟩ := exists_nonzero_of_finSum_ne_zero R hnz
        obtain ⟨k, hk⟩ := centralPrim_eq_some_block R hdecomp hblocks (hd.2 i)
        rw [← hk] at hine
        by_cases hjk : j = k
        · subst hjk
          exact ⟨i, hk⟩
        · exact absurd (hdecomp.2.1 j k hjk).1 hine
    have hcard_s : ExactCard (IsCentralPrimitiveIdempotent R) s := by
      refine ⟨d, hd.2, hd_inj, ?_⟩
      intro x hx
      obtain ⟨j, hj⟩ := centralPrim_eq_some_block R hdecomp hblocks hx
      have hin : ∃ j' : Fin t, x = c j' := ⟨j, hj.symm⟩
      have hin_s : ∃ i : Fin s, x = d i := by
        have hiff := congrFun hset x
        exact Eq.mpr hiff hin
      obtain ⟨i, hi⟩ := hin_s
      exact ⟨i, hi.symm⟩
    have hcard_t := central_block_central_prim_exactCard R hdecomp hblocks
    exact ⟨exactCard_unique hcard_s hcard_t, hset⟩
  refine ⟨hmain, ?_⟩
  refine ⟨fun _ => (fun x => ∃ j : Fin t, x = c j), ?_, ?_, ?_⟩
  · intro _
    exact ⟨t, c, hc_prim, rfl⟩
  · intro i j _
    exact Fin.ext (by omega)
  · intro S ⟨s, d, hd, hS⟩
    refine ⟨⟨0, Nat.zero_lt_one⟩, ?_⟩
    rw [hS, (hmain s d hd).2]

/-! ## 2. Finite Prime Field F_3 and Split Commutative Semisimple Family F_3^n -/

inductive F3 where
  | c0
  | c1
  | c2
  deriving DecidableEq, Repr

namespace F3

def add : F3 → F3 → F3
  | c0, y => y
  | c1, c0 => c1
  | c1, c1 => c2
  | c1, c2 => c0
  | c2, c0 => c2
  | c2, c1 => c0
  | c2, c2 => c1

def neg : F3 → F3
  | c0 => c0
  | c1 => c2
  | c2 => c1

def mul : F3 → F3 → F3
  | c0, _ => c0
  | c1, y => y
  | c2, c0 => c0
  | c2, c1 => c2
  | c2, c2 => c1

def inv : F3 → F3
  | c0 => c0
  | c1 => c1
  | c2 => c2

@[simp] theorem c0_add (x : F3) : add c0 x = x := rfl
@[simp] theorem add_c0 (x : F3) : add x c0 = x := by cases x <;> rfl
@[simp] theorem c0_mul (x : F3) : mul c0 x = c0 := rfl
@[simp] theorem mul_c0 (x : F3) : mul x c0 = c0 := by cases x <;> rfl
@[simp] theorem c1_mul (x : F3) : mul c1 x = x := rfl
@[simp] theorem mul_c1 (x : F3) : mul x c1 = x := by cases x <;> rfl

theorem inv_mul_cancel {x : F3} (hx : x ≠ c0) : mul (inv x) x = c1 := by
  cases x with
  | c0 => exact absurd rfl hx
  | c1 => rfl
  | c2 => rfl

theorem mul_inv_cancel {x : F3} (hx : x ≠ c0) : mul x (inv x) = c1 := by
  cases x with
  | c0 => exact absurd rfl hx
  | c1 => rfl
  | c2 => rfl

end F3

instance instDecidableForallF3 (P : F3 → Prop) [∀ x, Decidable (P x)] :
    Decidable (∀ x : F3, P x) :=
  if h0 : P F3.c0 then
    if h1 : P F3.c1 then
      if h2 : P F3.c2 then
        isTrue (fun x => by cases x; exact h0; exact h1; exact h2)
      else isFalse (fun h => h2 (h F3.c2))
    else isFalse (fun h => h1 (h F3.c1))
  else isFalse (fun h => h0 (h F3.c0))

def F3Ring : UnitalRing F3 where
  zero := F3.c0
  one := F3.c1
  add := F3.add
  neg := F3.neg
  mul := F3.mul
  add_assoc := fun a b c => by cases a <;> cases b <;> cases c <;> rfl
  add_comm := fun a b => by cases a <;> cases b <;> rfl
  zero_add := fun a => by cases a <;> rfl
  add_left_neg := fun a => by cases a <;> rfl
  mul_assoc := fun a b c => by cases a <;> cases b <;> cases c <;> rfl
  one_mul := fun a => by cases a <;> rfl
  mul_one := fun a => by cases a <;> rfl
  left_distrib := fun a b c => by cases a <;> cases b <;> cases c <;> rfl
  right_distrib := fun a b c => by cases a <;> cases b <;> cases c <;> rfl
  one_ne_zero := by decide

def F3CommRing : CommUnitalRing F3 :=
  { F3Ring with mul_comm := fun a b => by cases a <;> cases b <;> rfl }

def F3FieldRing : FieldRing F3 :=
  { F3CommRing with
    inv := F3.inv
    mul_inv_cancel := fun _ ha => F3.mul_inv_cancel ha }

def F3DomainRing : DomainRing F3 := F3FieldRing.toDomainRing

def F3Pow (n : Nat) : Type := Fin n → F3

def F3PowRing (n : Nat) [NeZero n] : UnitalRing (F3Pow n) where
  zero := fun _ => F3.c0
  one := fun _ => F3.c1
  add := fun x y i => F3.add (x i) (y i)
  neg := fun x i => F3.neg (x i)
  mul := fun x y i => F3.mul (x i) (y i)
  add_assoc := fun a b c => by funext i; exact F3Ring.add_assoc (a i) (b i) (c i)
  add_comm := fun a b => by funext i; exact F3Ring.add_comm (a i) (b i)
  zero_add := fun a => by funext i; exact F3Ring.zero_add (a i)
  add_left_neg := fun a => by funext i; exact F3Ring.add_left_neg (a i)
  mul_assoc := fun a b c => by funext i; exact F3Ring.mul_assoc (a i) (b i) (c i)
  one_mul := fun a => by funext i; exact F3Ring.one_mul (a i)
  mul_one := fun a => by funext i; exact F3Ring.mul_one (a i)
  left_distrib := fun a b c => by funext i; exact F3Ring.left_distrib (a i) (b i) (c i)
  right_distrib := fun a b c => by funext i; exact F3Ring.right_distrib (a i) (b i) (c i)
  one_ne_zero := by
    intro h
    have i0 : Fin n := ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩
    exact F3Ring.one_ne_zero (congrFun h i0)

theorem f3Pow_mul_comm (n : Nat) [NeZero n] (x y : F3Pow n) :
    (F3PowRing n).mul x y = (F3PowRing n).mul y x := by
  funext i
  exact F3CommRing.mul_comm (x i) (y i)

def coordProj (n : Nat) (j : Fin n) : F3Pow n :=
  fun i => if i = j then F3.c1 else F3.c0

theorem finSum_f3Pow_apply (n : Nat) [NeZero n] :
    ∀ (k : Nat) (f : Fin k → F3Pow n) (i : Fin n),
      finSum (F3PowRing n) k f i = finSum F3Ring k (fun j => f j i)
  | 0, _, _ => rfl
  | k + 1, f, i => by
    simp only [finSum]
    change F3.add (f ⟨0, Nat.zero_lt_succ k⟩ i)
      (finSum (F3PowRing n) k (fun j => f j.succ) i) = _
    rw [finSum_f3Pow_apply n k (fun j => f j.succ) i]
    rfl

theorem coordProj_orthDecomp (n : Nat) [NeZero n] :
    IsOrthIdempDecomp (F3PowRing n) n (coordProj n) := by
  refine ⟨?_, ?_, ?_⟩
  · intro j
    refine ⟨?_, ?_⟩
    · funext i
      dsimp [F3PowRing, coordProj]
      by_cases hij : i = j <;> simp [hij]
    · intro h0
      have hj : coordProj n j j = F3.c0 := congrFun h0 j
      dsimp [coordProj] at hj
      simp at hj
  · intro j₁ j₂ hne
    constructor
    · funext i
      dsimp [F3PowRing, coordProj]
      by_cases h1 : i = j₁
      · subst h1; simp [hne]
      · simp [h1]
    · funext i
      dsimp [F3PowRing, coordProj]
      by_cases h2 : i = j₂
      · subst h2; simp [hne.symm]
      · simp [h2]
  · funext i
    rw [finSum_f3Pow_apply n n (coordProj n) i]
    rw [finSum_single F3Ring i (fun j => coordProj n j i)]
    · dsimp [coordProj, F3PowRing]
      simp
    · intro j hji
      dsimp [coordProj, F3Ring]
      have hij : i ≠ j := fun h => hji h.symm
      simp [hij]

theorem coordProj_simpleCentralBlock (n : Nat) [NeZero n] (j : Fin n) :
    IsSimpleCentralBlock (F3PowRing n) (coordProj n j) := by
  have hd := coordProj_orthDecomp n
  refine ⟨⟨(hd.1 j).1, fun x => f3Pow_mul_comm n (coordProj n j) x⟩, (hd.1 j).2, ?_⟩
  intro I hI ⟨x, hxI, hxne⟩
  have hxj : x j ≠ F3.c0 := by
    intro h0
    apply hxne
    funext i
    dsimp [F3PowRing, coordProj]
    by_cases hij : i = j
    · subst hij; simp [h0]
    · simp [hij]
  let scale : F3Pow n := fun i => if i = j then F3.inv (x j) else F3.c0
  have heq : (F3PowRing n).mul scale x = coordProj n j := by
    funext i
    dsimp [F3PowRing, scale, coordProj]
    by_cases hij : i = j
    · subst hij
      simp [F3.inv_mul_cancel hxj]
    · simp [hij]
  rw [← heq]
  exact hI.1.2 scale x hxI

theorem comm_prim_iff_centralPrim {α : Type u} (R : UnitalRing α)
    (hcomm : ∀ a b : α, R.mul a b = R.mul b a) (e : α) :
    IsPrimitiveIdempotent R e ↔ IsCentralPrimitiveIdempotent R e := by
  constructor
  · intro ⟨⟨heidem, hene⟩, hnotsplit⟩
    refine ⟨⟨heidem, fun x => hcomm e x⟩, hene, ?_⟩
    intro ⟨f, g, ⟨hfidem, _⟩, hfne, ⟨hgidem, _⟩, hgne, horth, hsum⟩
    exact hnotsplit ⟨f, g, ⟨hfidem, hfne⟩, ⟨hgidem, hgne⟩, horth, hsum⟩
  · intro ⟨⟨heidem, _⟩, hene, hnotsplit⟩
    refine ⟨⟨heidem, hene⟩, ?_⟩
    intro ⟨f, g, ⟨hfidem, hfne⟩, ⟨hgidem, hgne⟩, horth, hsum⟩
    exact hnotsplit ⟨f, g, ⟨hfidem, fun x => hcomm f x⟩, hfne,
      ⟨hgidem, fun x => hcomm g x⟩, hgne, horth, hsum⟩

theorem comm_minLeft_iff_minTwoSided {α : Type u} (R : UnitalRing α)
    (hcomm : ∀ a b : α, R.mul a b = R.mul b a) (L : α → Prop) :
    IsMinimalLeftIdeal R L ↔ IsMinimalTwoSidedIdeal R L := by
  have hLiff : ∀ M : α → Prop, IsLeftIdeal R M ↔ IsTwoSidedIdeal R M := by
    intro M
    constructor
    · intro hL
      exact ⟨hL, ⟨hL.1, fun x r hx => by rw [hcomm x r]; exact hL.2 r x hx⟩⟩
    · intro hT
      exact hT.1
  constructor
  · intro ⟨hL, hNz, hMin⟩
    refine ⟨(hLiff L).mp hL, hNz, ?_⟩
    intro J hJ hJnz hsub
    exact hMin J ((hLiff J).mpr hJ) hJnz hsub
  · intro ⟨hT, hNz, hMin⟩
    refine ⟨(hLiff L).mpr hT, hNz, ?_⟩
    intro M hM hMnz hsub
    exact hMin M ((hLiff M).mp hM) hMnz hsub

/-- **Positive Non-Vacuity Theorem on `F_3^(m+1)`**:
    In the split commutative semisimple algebra `F_3^(m+1)`, minimal two-sided
    ideals, minimal left ideals, primitive idempotents, and the length of every
    primitive orthogonal idempotent decomposition of `1` ALL equal `m + 1`, and
    the unordered primitive decomposition of `1` is unique (card `1`). -/
theorem f3Pow_positive_theorem (m : Nat) :
    let R := F3PowRing (m + 1)
    ExactCard (IsMinimalTwoSidedIdeal R) (m + 1) ∧
    ExactCard (IsMinimalLeftIdeal R) (m + 1) ∧
    ExactCard (IsPrimitiveIdempotent R) (m + 1) ∧
    (∃ e : Fin (m + 1) → F3Pow (m + 1), IsPrimOrthDecomp R (m + 1) e) ∧
    (∀ (r : Nat) (e : Fin r → F3Pow (m + 1)), IsPrimOrthDecomp R r e → r = m + 1) ∧
    ExactCard (IsUnordPrimOrthDecomp R) 1 := by
  intro R
  have hd := coordProj_orthDecomp (m + 1)
  have hb := coordProj_simpleCentralBlock (m + 1)
  have hcomm := f3Pow_mul_comm (m + 1)
  have htwo := central_block_minimal_ideals_exactCard R hd hb
  have hcprim := central_block_central_prim_exactCard R hd hb
  have huniq := central_block_decomp_uniqueness R hd hb
  have hleft : ExactCard (IsMinimalLeftIdeal R) (m + 1) := by
    obtain ⟨f, hf1, hf2, hf3⟩ := htwo
    exact ⟨f, fun i => (comm_minLeft_iff_minTwoSided R hcomm (f i)).mpr (hf1 i), hf2,
      fun L hL => hf3 L ((comm_minLeft_iff_minTwoSided R hcomm L).mp hL)⟩
  have hprim : ExactCard (IsPrimitiveIdempotent R) (m + 1) := by
    obtain ⟨f, hf1, hf2, hf3⟩ := hcprim
    exact ⟨f, fun i => (comm_prim_iff_centralPrim R hcomm (f i)).mpr (hf1 i), hf2,
      fun e he => hf3 e ((comm_prim_iff_centralPrim R hcomm e).mp he)⟩
  have hex : ∃ e : Fin (m + 1) → F3Pow (m + 1), IsPrimOrthDecomp R (m + 1) e := by
    refine ⟨coordProj (m + 1), hd, fun j => ?_⟩
    exact (comm_prim_iff_centralPrim R hcomm (coordProj (m + 1) j)).mpr
      (simpleBlock_isCentralPrimitive R (hb j))
  have hlen : ∀ (r : Nat) (e : Fin r → F3Pow (m + 1)), IsPrimOrthDecomp R r e → r = m + 1 := by
    intro r e he
    have hc : IsCentralPrimDecomp R r e :=
      ⟨he.1, fun i => (comm_prim_iff_centralPrim R hcomm (e i)).mp (he.2 i)⟩
    exact (huniq.1 r e hc).1
  have hunord : ExactCard (IsUnordPrimOrthDecomp R) 1 := by
    obtain ⟨f, hf1, hf2, hf3⟩ := huniq.2
    refine ⟨f, ?_, hf2, ?_⟩
    · intro i
      obtain ⟨r, c, hc, hS⟩ := hf1 i
      exact ⟨r, c, ⟨hc.1, fun k => (comm_prim_iff_centralPrim R hcomm (c k)).mpr (hc.2 k)⟩, hS⟩
    · intro S ⟨r, e, he, hS⟩
      exact hf3 S ⟨r, e, ⟨he.1, fun k => (comm_prim_iff_centralPrim R hcomm (e k)).mp (he.2 k)⟩, hS⟩
  exact ⟨htwo, hleft, hprim, hex, hlen, hunord⟩

/-! ## 3. Explicit Split Clifford Algebra Isomorphism `Cl_{1,0}(F_3) ≅ F_3 × F_3` -/

structure Cl10F3 where
  s : F3
  v : F3
  deriving DecidableEq, Repr

def Cl10F3Ring : UnitalRing Cl10F3 where
  zero := ⟨F3.c0, F3.c0⟩
  one := ⟨F3.c1, F3.c0⟩
  add := fun x y => ⟨F3.add x.s y.s, F3.add x.v y.v⟩
  neg := fun x => ⟨F3.neg x.s, F3.neg x.v⟩
  mul := fun x y =>
    ⟨F3.add (F3.mul x.s y.s) (F3.mul x.v y.v),
     F3.add (F3.mul x.s y.v) (F3.mul x.v y.s)⟩
  add_assoc := fun ⟨as, av⟩ ⟨bs, bv⟩ ⟨cs, cv⟩ => by
    cases as <;> cases av <;> cases bs <;> cases bv <;> cases cs <;> cases cv <;> rfl
  add_comm := fun ⟨as, av⟩ ⟨bs, bv⟩ => by
    cases as <;> cases av <;> cases bs <;> cases bv <;> rfl
  zero_add := fun ⟨as, av⟩ => by
    cases as <;> cases av <;> rfl
  add_left_neg := fun ⟨as, av⟩ => by
    cases as <;> cases av <;> rfl
  mul_assoc := fun ⟨as, av⟩ ⟨bs, bv⟩ ⟨cs, cv⟩ => by
    cases as <;> cases av <;> cases bs <;> cases bv <;> cases cs <;> cases cv <;> rfl
  one_mul := fun ⟨as, av⟩ => by
    cases as <;> cases av <;> rfl
  mul_one := fun ⟨as, av⟩ => by
    cases as <;> cases av <;> rfl
  left_distrib := fun ⟨as, av⟩ ⟨bs, bv⟩ ⟨cs, cv⟩ => by
    cases as <;> cases av <;> cases bs <;> cases bv <;> cases cs <;> cases cv <;> rfl
  right_distrib := fun ⟨as, av⟩ ⟨bs, bv⟩ ⟨cs, cv⟩ => by
    cases as <;> cases av <;> cases bs <;> cases bv <;> cases cs <;> cases cv <;> rfl
  one_ne_zero := by decide

/-- Explicit Clifford isomorphism `Cl_{1,0}(F_3) ≅ F_3 × F_3` (`s + v*e ↦ (s+v, s-v)`). -/
def cl10_f3_iso_f3Pow2 : RingIso Cl10F3Ring (F3PowRing 2) where
  toFun := fun x i =>
    match i with
    | ⟨0, _⟩ => F3.add x.s x.v
    | ⟨1, _⟩ => F3.add x.s (F3.neg x.v)
  invFun := fun f =>
    ⟨F3.mul F3.c2 (F3.add (f ⟨0, by decide⟩) (f ⟨1, by decide⟩)),
     F3.mul F3.c2 (F3.add (f ⟨0, by decide⟩) (F3.neg (f ⟨1, by decide⟩)))⟩
  left_inv := fun ⟨s, v⟩ => by
    cases s <;> cases v <;> rfl
  right_inv := fun f => by
    funext i
    let i0 : Fin 2 := ⟨0, by decide⟩
    let i1 : Fin 2 := ⟨1, by decide⟩
    match i with
    | ⟨0, h0⟩ =>
      have hi : (⟨0, h0⟩ : Fin 2) = i0 := rfl
      rw [hi]
      cases h_u : f i0 <;> cases h_w : f i1 <;> simp [i0, i1, h_u, h_w, F3.add, F3.neg, F3.mul]
    | ⟨1, h1⟩ =>
      have hi : (⟨1, h1⟩ : Fin 2) = i1 := rfl
      rw [hi]
      cases h_u : f i0 <;> cases h_w : f i1 <;> simp [i0, i1, h_u, h_w, F3.add, F3.neg, F3.mul]
    | ⟨k + 2, hk⟩ => omega
  map_zero := by
    funext i
    match i with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
    | ⟨k + 2, hk⟩ => omega
  map_one := by
    funext i
    match i with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
    | ⟨k + 2, hk⟩ => omega
  map_add := fun ⟨as, av⟩ ⟨bs, bv⟩ => by
    funext i
    match i with
    | ⟨0, _⟩ => cases as <;> cases av <;> cases bs <;> cases bv <;> rfl
    | ⟨1, _⟩ => cases as <;> cases av <;> cases bs <;> cases bv <;> rfl
    | ⟨k + 2, hk⟩ => omega
  map_mul := fun ⟨as, av⟩ ⟨bs, bv⟩ => by
    funext i
    match i with
    | ⟨0, _⟩ => cases as <;> cases av <;> cases bs <;> cases bv <;> rfl
    | ⟨1, _⟩ => cases as <;> cases av <;> cases bs <;> cases bv <;> rfl
    | ⟨k + 2, hk⟩ => omega

end Conjecture00000007625
