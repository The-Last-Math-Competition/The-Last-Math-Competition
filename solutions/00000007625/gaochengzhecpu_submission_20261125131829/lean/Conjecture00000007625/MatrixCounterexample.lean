/-
  Conjecture 00000007625 — Noncommutative Matrix & Split Clifford Refutation

  Proves:
  1. Characteristic-free idempotent & primitivity theory on `Mat2 α` over any
     integral domain `D`:
       - Nontrivial idempotent iff `tr(e) = 1 ∧ det(e) = 0`.
       - Any two nonzero orthogonal idempotents sum to `I_2`.
       - Every nontrivial idempotent is primitive; `I_2` is not primitive.
       - Every primitive orthogonal idempotent decomposition of `I_2` has
         exact length `2`.
  2. Simplicity & center theory on `Mat2 α` over any field `K`:
       - `Mat2 K` is a simple ring (`ExactCard IsMinimalTwoSidedIdeal 1`).
       - `Z(Mat2 K) = K · I_2`, so `ExactCard IsCentralPrimitiveIdempotent 1`.
       - Immediate universal refutation over every field `K`: length `2 ≠ 1`.
  3. Master Six-Way Exact Cardinality Separation on `M_2(F_3) ≅ Cl_{1,1}(F_3)`:
       - Minimal two-sided ideals / central primitive blocks: `1`
       - Primitive orthogonal decomposition length:           `2`
       - Minimal left ideals:                                 `4`
       - Unordered primitive orthogonal decompositions:       `6`
       - Ordered primitive decompositions / prim. idempotents:`12`
       - Total idempotents:                                   `14`
     Disjointness `{2, 6, 12, 14} ∩ {1, 4} = ∅` refutes Clause 1 under every
     possible reading of both "count law of idempotent decompositions" and
     "minimal-ideal count".
  4. Infinite Family on `M_2(ℤ)` (and any characteristic-zero field `M_2(K)`):
     `e_t = [[1, t], [0, 0]]`, `f_t = [[0, -t], [0, 1]]` (`t ∈ ℤ`) yields
     infinitely many pairwise distinct unordered primitive decompositions.
-/

import Conjecture00000007625.Basic
import Conjecture00000007625.Positive

namespace Conjecture00000007625

/-! ## 1. 2×2 Matrix Ring `Mat2 α` over an Arbitrary Unital Ring -/

structure Mat2 (α : Type u) where
  a : α
  b : α
  c : α
  d : α
  deriving DecidableEq, Repr

theorem Mat2.ext {α : Type u} {x y : Mat2 α}
    (ha : x.a = y.a) (hb : x.b = y.b) (hc : x.c = y.c) (hd : x.d = y.d) : x = y := by
  cases x; cases y; dsimp at ha hb hc hd; subst ha hb hc hd; rfl

theorem add_four_swap {α : Type u} (R : UnitalRing α) (p q r s : α) :
    R.add (R.add p q) (R.add r s) = R.add (R.add p r) (R.add q s) := by
  calc
    R.add (R.add p q) (R.add r s)
      = R.add p (R.add q (R.add r s)) := R.add_assoc p q (R.add r s)
    _ = R.add p (R.add (R.add q r) s) := by rw [← R.add_assoc q r s]
    _ = R.add p (R.add (R.add r q) s) := by rw [R.add_comm q r]
    _ = R.add p (R.add r (R.add q s)) := by rw [R.add_assoc r q s]
    _ = R.add (R.add p r) (R.add q s) := (R.add_assoc p r (R.add q s)).symm

def Mat2Ring {α : Type u} (R : UnitalRing α) : UnitalRing (Mat2 α) where
  zero := ⟨R.zero, R.zero, R.zero, R.zero⟩
  one := ⟨R.one, R.zero, R.zero, R.one⟩
  add := fun x y => ⟨R.add x.a y.a, R.add x.b y.b, R.add x.c y.c, R.add x.d y.d⟩
  neg := fun x => ⟨R.neg x.a, R.neg x.b, R.neg x.c, R.neg x.d⟩
  mul := fun x y =>
    ⟨R.add (R.mul x.a y.a) (R.mul x.b y.c),
     R.add (R.mul x.a y.b) (R.mul x.b y.d),
     R.add (R.mul x.c y.a) (R.mul x.d y.c),
     R.add (R.mul x.c y.b) (R.mul x.d y.d)⟩
  add_assoc := fun x y z =>
    Mat2.ext (R.add_assoc x.a y.a z.a) (R.add_assoc x.b y.b z.b)
      (R.add_assoc x.c y.c z.c) (R.add_assoc x.d y.d z.d)
  add_comm := fun x y =>
    Mat2.ext (R.add_comm x.a y.a) (R.add_comm x.b y.b)
      (R.add_comm x.c y.c) (R.add_comm x.d y.d)
  zero_add := fun x =>
    Mat2.ext (R.zero_add x.a) (R.zero_add x.b) (R.zero_add x.c) (R.zero_add x.d)
  add_left_neg := fun x =>
    Mat2.ext (R.add_left_neg x.a) (R.add_left_neg x.b)
      (R.add_left_neg x.c) (R.add_left_neg x.d)
  mul_assoc := fun x y z => by
    have entry : ∀ (u1 u2 v1 v2 v3 v4 w1 w2 : α),
        R.add (R.mul (R.add (R.mul u1 v1) (R.mul u2 v3)) w1)
              (R.mul (R.add (R.mul u1 v2) (R.mul u2 v4)) w2) =
        R.add (R.mul u1 (R.add (R.mul v1 w1) (R.mul v2 w2)))
              (R.mul u2 (R.add (R.mul v3 w1) (R.mul v4 w2))) := by
      intro u1 u2 v1 v2 v3 v4 w1 w2
      rw [R.right_distrib, R.right_distrib, R.left_distrib, R.left_distrib]
      rw [R.mul_assoc, R.mul_assoc, R.mul_assoc, R.mul_assoc]
      exact add_four_swap R _ _ _ _
    exact Mat2.ext
      (entry x.a x.b y.a y.b y.c y.d z.a z.c)
      (entry x.a x.b y.a y.b y.c y.d z.b z.d)
      (entry x.c x.d y.a y.b y.c y.d z.a z.c)
      (entry x.c x.d y.a y.b y.c y.d z.b z.d)
  one_mul := fun x =>
    Mat2.ext
      (by dsimp; rw [R.one_mul, R.zero_mul, R.add_zero])
      (by dsimp; rw [R.one_mul, R.zero_mul, R.add_zero])
      (by dsimp; rw [R.zero_mul, R.one_mul, R.zero_add])
      (by dsimp; rw [R.zero_mul, R.one_mul, R.zero_add])
  mul_one := fun x =>
    Mat2.ext
      (by dsimp; rw [R.mul_one, R.mul_zero, R.add_zero])
      (by dsimp; rw [R.mul_zero, R.mul_one, R.zero_add])
      (by dsimp; rw [R.mul_one, R.mul_zero, R.add_zero])
      (by dsimp; rw [R.mul_zero, R.mul_one, R.zero_add])
  left_distrib := fun x y z => by
    have entry : ∀ (u1 u2 v1 w1 v2 w2 : α),
        R.add (R.mul u1 (R.add v1 w1)) (R.mul u2 (R.add v2 w2)) =
        R.add (R.add (R.mul u1 v1) (R.mul u2 v2))
              (R.add (R.mul u1 w1) (R.mul u2 w2)) := by
      intro u1 u2 v1 w1 v2 w2
      rw [R.left_distrib, R.left_distrib]
      exact add_four_swap R _ _ _ _
    exact Mat2.ext
      (entry x.a x.b y.a z.a y.c z.c)
      (entry x.a x.b y.b z.b y.d z.d)
      (entry x.c x.d y.a z.a y.c z.c)
      (entry x.c x.d y.b z.b y.d z.d)
  right_distrib := fun x y z => by
    have entry : ∀ (u1 v1 u2 v2 w1 w2 : α),
        R.add (R.mul (R.add u1 v1) w1) (R.mul (R.add u2 v2) w2) =
        R.add (R.add (R.mul u1 w1) (R.mul u2 w2))
              (R.add (R.mul v1 w1) (R.mul v2 w2)) := by
      intro u1 v1 u2 v2 w1 w2
      rw [R.right_distrib, R.right_distrib]
      exact add_four_swap R _ _ _ _
    exact Mat2.ext
      (entry x.a y.a x.b y.b z.a z.c)
      (entry x.a y.a x.b y.b z.b z.d)
      (entry x.c y.c x.d y.d z.a z.c)
      (entry x.c y.c x.d y.d z.b z.d)
  one_ne_zero := fun h => R.one_ne_zero (congrArg Mat2.a h)

/-! ## 2. Characteristic-Free Idempotent & Primitivity Theory over Any Domain -/

section DomainTheory

variable {α : Type u} (D : DomainRing α)

theorem domain_idemp_zero_or_one {x : α} (hx : D.mul x x = x) :
    x = D.zero ∨ x = D.one := by
  let R := D.toUnitalRing
  have hmul : R.mul x (R.sub x R.one) = R.zero := by
    rw [R.mul_sub, hx, R.mul_one, R.sub_self]
  cases D.eq_zero_or_eq_zero_of_mul_eq_zero x (R.sub x R.one) hmul with
  | inl h0 => exact Or.inl h0
  | inr h1 => exact Or.inr (R.sub_eq_zero.mp h1)

theorem domain_mul_eq_self_imp_one {u v : α} (hu : u ≠ D.zero)
    (huv : D.mul u v = u) : v = D.one := by
  let R := D.toUnitalRing
  have hmul : R.mul u (R.sub v R.one) = R.zero := by
    rw [R.mul_sub, huv, R.mul_one, R.sub_self]
  cases D.eq_zero_or_eq_zero_of_mul_eq_zero u (R.sub v R.one) hmul with
  | inl h0 => exact absurd h0 hu
  | inr h1 => exact R.sub_eq_zero.mp h1

theorem mat2_nontriv_idemp_iff (m : Mat2 α) :
    let R := D.toUnitalRing
    let M := Mat2Ring R
    (IsIdempotent M m ∧ m ≠ M.zero ∧ m ≠ M.one) ↔
      (R.add m.a m.d = R.one ∧ R.mul m.a m.d = R.mul m.b m.c) := by
  let R := D.toUnitalRing
  let M := Mat2Ring R
  constructor
  · intro ⟨hm, hne0, hne1⟩
    have ha_eq : R.add (R.mul m.a m.a) (R.mul m.b m.c) = m.a := congrArg Mat2.a hm
    have hb_eq : R.add (R.mul m.a m.b) (R.mul m.b m.d) = m.b := congrArg Mat2.b hm
    have hc_eq : R.add (R.mul m.c m.a) (R.mul m.d m.c) = m.c := congrArg Mat2.c hm
    have hd_eq : R.add (R.mul m.c m.b) (R.mul m.d m.d) = m.d := congrArg Mat2.d hm
    by_cases hb : m.b ≠ R.zero
    · have htr1 : R.add m.a m.d = R.one := by
        apply domain_mul_eq_self_imp_one D hb
        calc
          R.mul m.b (R.add m.a m.d)
            = R.add (R.mul m.b m.a) (R.mul m.b m.d) := R.left_distrib m.b m.a m.d
          _ = R.add (R.mul m.a m.b) (R.mul m.b m.d) := by rw [D.mul_comm m.b m.a]
          _ = m.b := hb_eq
      have hdet : R.mul m.a m.d = R.mul m.b m.c := by
        apply R.add_left_cancel (a := R.mul m.a m.a)
        calc
          R.add (R.mul m.a m.a) (R.mul m.a m.d)
            = R.mul m.a (R.add m.a m.d) := (R.left_distrib m.a m.a m.d).symm
          _ = m.a := by rw [htr1, R.mul_one]
          _ = R.add (R.mul m.a m.a) (R.mul m.b m.c) := ha_eq.symm
      exact ⟨htr1, hdet⟩
    · have hb0 : m.b = R.zero := Classical.byContradiction (fun h => hb h)
      by_cases hc : m.c ≠ R.zero
      · have htr1 : R.add m.a m.d = R.one := by
          apply domain_mul_eq_self_imp_one D hc
          calc
            R.mul m.c (R.add m.a m.d)
              = R.add (R.mul m.c m.a) (R.mul m.c m.d) := R.left_distrib m.c m.a m.d
            _ = R.add (R.mul m.c m.a) (R.mul m.d m.c) := by rw [D.mul_comm m.c m.d]
            _ = m.c := hc_eq
        have hdet : R.mul m.a m.d = R.mul m.b m.c := by
          apply R.add_left_cancel (a := R.mul m.a m.a)
          calc
            R.add (R.mul m.a m.a) (R.mul m.a m.d)
              = R.mul m.a (R.add m.a m.d) := (R.left_distrib m.a m.a m.d).symm
            _ = m.a := by rw [htr1, R.mul_one]
            _ = R.add (R.mul m.a m.a) (R.mul m.b m.c) := ha_eq.symm
        exact ⟨htr1, hdet⟩
      · have hc0 : m.c = R.zero := Classical.byContradiction (fun h => hc h)
        rw [hb0, R.zero_mul, R.add_zero] at ha_eq
        rw [hc0, R.zero_mul, R.zero_add] at hd_eq
        cases domain_idemp_zero_or_one D ha_eq with
        | inl ha0 =>
          cases domain_idemp_zero_or_one D hd_eq with
          | inl hd0 =>
            exfalso; apply hne0
            cases m; dsimp at ha0 hb0 hc0 hd0; subst ha0 hb0 hc0 hd0; rfl
          | inr hd1 =>
            rw [ha0, hd1, hb0, R.zero_add, R.zero_mul, R.zero_mul]
            exact ⟨rfl, rfl⟩
        | inr ha1 =>
          cases domain_idemp_zero_or_one D hd_eq with
          | inl hd0 =>
            rw [ha1, hd0, hb0, R.add_zero, R.mul_zero, R.zero_mul]
            exact ⟨rfl, rfl⟩
          | inr hd1 =>
            exfalso; apply hne1
            cases m; dsimp at ha1 hb0 hc0 hd1; subst ha1 hb0 hc0 hd1; rfl
  · intro ⟨htr, hdet⟩
    have hidem : IsIdempotent M m := by
      unfold IsIdempotent
      cases m with
      | mk a b c d =>
        dsimp at htr hdet
        dsimp [M, Mat2Ring]
        have e1 : R.add (R.mul a a) (R.mul b c) = a := by
          rw [← hdet, ← R.left_distrib, htr, R.mul_one]
        have e2 : R.add (R.mul a b) (R.mul b d) = b := by
          rw [D.mul_comm a b, ← R.left_distrib, htr, R.mul_one]
        have e3 : R.add (R.mul c a) (R.mul d c) = c := by
          rw [D.mul_comm d c, ← R.left_distrib, htr, R.mul_one]
        have e4 : R.add (R.mul c b) (R.mul d d) = d := by
          rw [D.mul_comm c b, ← hdet, ← R.right_distrib, htr, R.one_mul]
        exact Mat2.ext e1 e2 e3 e4
    have hne0 : m ≠ M.zero := by
      intro hz
      rw [hz] at htr
      dsimp [M, Mat2Ring] at htr
      rw [R.zero_add] at htr
      exact R.one_ne_zero htr.symm
    have hne1 : m ≠ M.one := by
      intro h1
      rw [h1] at hdet
      dsimp [M, Mat2Ring] at hdet
      rw [R.one_mul, R.zero_mul] at hdet
      exact R.one_ne_zero hdet
    exact ⟨hidem, hne0, hne1⟩

theorem mat2_orth_idemp_sum_eq_one {f g : Mat2 α}
    (hf : IsNonzeroIdempotent (Mat2Ring D.toUnitalRing) f)
    (hg : IsNonzeroIdempotent (Mat2Ring D.toUnitalRing) g)
    (horth : AreOrthogonal (Mat2Ring D.toUnitalRing) f g) :
    (Mat2Ring D.toUnitalRing).add f g = (Mat2Ring D.toUnitalRing).one := by
  let R := D.toUnitalRing
  let M := Mat2Ring R
  have hf_ne1 : f ≠ M.one := by
    intro hf1
    have hg0 : g = M.zero := by
      calc
        g = M.mul M.one g := (M.one_mul g).symm
        _ = M.mul f g := by rw [hf1]
        _ = M.zero := horth.1
    exact hg.2 hg0
  have hg_ne1 : g ≠ M.one := by
    intro hg1
    have hf0 : f = M.zero := by
      calc
        f = M.mul f M.one := (M.mul_one f).symm
        _ = M.mul f g := by rw [hg1]
        _ = M.zero := horth.1
    exact hf.2 hf0
  have hf_tr : R.add f.a f.d = R.one :=
    ((mat2_nontriv_idemp_iff D f).mp ⟨hf.1, hf.2, hf_ne1⟩).1
  have hg_tr : R.add g.a g.d = R.one :=
    ((mat2_nontriv_idemp_iff D g).mp ⟨hg.1, hg.2, hg_ne1⟩).1
  let h : Mat2 α := M.add f g
  have hh_idem : IsIdempotent M h := by
    unfold IsIdempotent
    dsimp [h]
    rw [M.left_distrib, M.right_distrib, M.right_distrib]
    rw [hf.1, hg.1, horth.1, horth.2, M.add_zero, M.zero_add]
  have hh_ne0 : h ≠ M.zero := by
    intro hh0
    have hf0 : f = M.zero := by
      calc
        f = M.add (M.mul f f) (M.mul f g) := by rw [hf.1, horth.1, M.add_zero]
        _ = M.mul f h := (M.left_distrib f f g).symm
        _ = M.zero := by rw [hh0, M.mul_zero]
    exact hf.2 hf0
  apply Classical.byContradiction
  intro hh_ne1
  have hh_tr : R.add h.a h.d = R.one :=
    ((mat2_nontriv_idemp_iff D h).mp ⟨hh_idem, hh_ne0, hh_ne1⟩).1
  have h11_eq_1 : R.add R.one R.one = R.one := by
    calc
      R.add R.one R.one
        = R.add (R.add f.a f.d) (R.add g.a g.d) := by rw [hf_tr, hg_tr]
      _ = R.add (R.add f.a g.a) (R.add f.d g.d) := add_four_swap R f.a f.d g.a g.d
      _ = R.add h.a h.d := rfl
      _ = R.one := hh_tr
  have h10 : R.one = R.zero := by
    apply R.add_left_cancel (a := R.one)
    rw [h11_eq_1, R.add_zero]
  exact R.one_ne_zero h10

def mat2E11 {α : Type u} (R : UnitalRing α) : Mat2 α := ⟨R.one, R.zero, R.zero, R.zero⟩
def mat2E22 {α : Type u} (R : UnitalRing α) : Mat2 α := ⟨R.zero, R.zero, R.zero, R.one⟩

theorem mat2E11_orth_E22 {α : Type u} (R : UnitalRing α) :
    AreOrthogonal (Mat2Ring R) (mat2E11 R) (mat2E22 R) := by
  constructor <;> dsimp [Mat2Ring, mat2E11, mat2E22] <;>
    exact Mat2.ext
      (by simp [R.zero_add, R.add_zero, R.zero_mul, R.mul_zero, R.one_mul, R.mul_one])
      (by simp [R.zero_add, R.add_zero, R.zero_mul, R.mul_zero, R.one_mul, R.mul_one])
      (by simp [R.zero_add, R.add_zero, R.zero_mul, R.mul_zero, R.one_mul, R.mul_one])
      (by simp [R.zero_add, R.add_zero, R.zero_mul, R.mul_zero, R.one_mul, R.mul_one])

theorem mat2E11_add_E22 {α : Type u} (R : UnitalRing α) :
    (Mat2Ring R).add (mat2E11 R) (mat2E22 R) = (Mat2Ring R).one :=
  Mat2.ext (R.add_zero R.one) (R.add_zero R.zero) (R.add_zero R.zero) (R.zero_add R.one)

theorem mat2_one_not_primitive :
    ¬ IsPrimitiveIdempotent (Mat2Ring D.toUnitalRing) (Mat2Ring D.toUnitalRing).one := by
  let R := D.toUnitalRing
  let M := Mat2Ring R
  intro ⟨_, hnotsplit⟩
  apply hnotsplit
  have h11 : IsNonzeroIdempotent M (mat2E11 R) := by
    refine ⟨?_, fun hz => R.one_ne_zero (congrArg Mat2.a hz)⟩
    exact ((mat2_nontriv_idemp_iff D (mat2E11 R)).mpr
      ⟨R.add_zero R.one, by change R.mul R.one R.zero = R.mul R.zero R.zero; rw [R.mul_zero, R.mul_zero]⟩).1
  have h22 : IsNonzeroIdempotent M (mat2E22 R) := by
    refine ⟨?_, fun hz => R.one_ne_zero (congrArg Mat2.d hz)⟩
    exact ((mat2_nontriv_idemp_iff D (mat2E22 R)).mpr
      ⟨R.zero_add R.one, by change R.mul R.zero R.one = R.mul R.zero R.zero; rw [R.zero_mul, R.mul_zero]⟩).1
  exact ⟨mat2E11 R, mat2E22 R, h11, h22, mat2E11_orth_E22 R, mat2E11_add_E22 R⟩

theorem mat2_prim_idemp_iff (m : Mat2 α) :
    let R := D.toUnitalRing
    let M := Mat2Ring R
    IsPrimitiveIdempotent M m ↔
      (R.add m.a m.d = R.one ∧ R.mul m.a m.d = R.mul m.b m.c) := by
  let R := D.toUnitalRing
  let M := Mat2Ring R
  constructor
  · intro hprim
    have hne1 : m ≠ M.one := by
      intro hm1
      rw [hm1] at hprim
      exact mat2_one_not_primitive D hprim
    exact (mat2_nontriv_idemp_iff D m).mp ⟨hprim.1.1, hprim.1.2, hne1⟩
  · intro hcond
    obtain ⟨hidem, hne0, hne1⟩ := (mat2_nontriv_idemp_iff D m).mpr hcond
    refine ⟨⟨hidem, hne0⟩, ?_⟩
    intro ⟨f, g, hf, hg, horth, hsum⟩
    have hf_plus_g : M.add f g = M.one := mat2_orth_idemp_sum_eq_one D hf hg horth
    exact hne1 (hsum.symm.trans hf_plus_g)

theorem mat2_std_prim_decomp :
    IsPrimOrthDecomp (Mat2Ring D.toUnitalRing) 2
      (fun i => match i with
        | ⟨0, _⟩ => mat2E11 D.toUnitalRing
        | ⟨1, _⟩ => mat2E22 D.toUnitalRing) := by
  let R := D.toUnitalRing
  let M := Mat2Ring R
  let e : Fin 2 → Mat2 α := fun i =>
    match i with
    | ⟨0, _⟩ => mat2E11 R
    | ⟨1, _⟩ => mat2E22 R
  have hp0 : IsPrimitiveIdempotent M (mat2E11 R) :=
    (mat2_prim_idemp_iff D (mat2E11 R)).mpr
      ⟨R.add_zero R.one, by change R.mul R.one R.zero = R.mul R.zero R.zero; rw [R.mul_zero, R.mul_zero]⟩
  have hp1 : IsPrimitiveIdempotent M (mat2E22 R) :=
    (mat2_prim_idemp_iff D (mat2E22 R)).mpr
      ⟨R.zero_add R.one, by change R.mul R.zero R.one = R.mul R.zero R.zero; rw [R.zero_mul, R.mul_zero]⟩
  have hprim : ∀ i : Fin 2, IsPrimitiveIdempotent M (e i) := by
    intro i
    match i with
    | ⟨0, _⟩ => exact hp0
    | ⟨1, _⟩ => exact hp1
    | ⟨k + 2, hk⟩ => omega
  have horth12 := mat2E11_orth_E22 R
  refine ⟨⟨fun i => (hprim i).1, ?_, ?_⟩, hprim⟩
  · intro i j hne
    match i, j with
    | ⟨0, _⟩, ⟨0, _⟩ => exact absurd rfl hne
    | ⟨1, _⟩, ⟨1, _⟩ => exact absurd rfl hne
    | ⟨0, _⟩, ⟨1, _⟩ => exact horth12
    | ⟨1, _⟩, ⟨0, _⟩ => exact ⟨horth12.2, horth12.1⟩
    | ⟨k + 2, hk⟩, _ => omega
    | _, ⟨k + 2, hk⟩ => omega
  · simp only [finSum]
    rw [M.add_zero]
    exact mat2E11_add_E22 R

theorem mat2_prim_decomp_length_eq_two {r : Nat} {e : Fin r → Mat2 α}
    (he : IsPrimOrthDecomp (Mat2Ring D.toUnitalRing) r e) : r = 2 := by
  let R := D.toUnitalRing
  let M := Mat2Ring R
  match r with
  | 0 =>
    have h01 : M.zero = M.one := he.1.2.2
    exact absurd h01.symm M.one_ne_zero
  | 1 =>
    have hsum : e ⟨0, Nat.zero_lt_one⟩ = M.one := by
      have h := he.1.2.2
      simp only [finSum] at h
      rw [M.add_zero] at h
      exact h
    have hp := he.2 ⟨0, Nat.zero_lt_one⟩
    rw [hsum] at hp
    exact absurd hp (mat2_one_not_primitive D)
  | 2 => rfl
  | k + 3 =>
    let i0 : Fin (k + 3) := ⟨0, by omega⟩
    let i1 : Fin (k + 3) := ⟨1, by omega⟩
    let i2 : Fin (k + 3) := ⟨2, by omega⟩
    have h01 : i0 ≠ i1 := fun h => by
      have hv : (0 : Nat) = 1 := congrArg Fin.val h
      exact absurd hv (by decide)
    have h02 : i0 ≠ i2 := fun h => by
      have hv : (0 : Nat) = 2 := congrArg Fin.val h
      exact absurd hv (by decide)
    have h12 : i1 ≠ i2 := fun h => by
      have hv : (1 : Nat) = 2 := congrArg Fin.val h
      exact absurd hv (by decide)
    have hsum01 : M.add (e i0) (e i1) = M.one :=
      mat2_orth_idemp_sum_eq_one D (he.1.1 i0) (he.1.1 i1) (he.1.2.1 i0 i1 h01)
    have he2_zero : e i2 = M.zero := by
      calc
        e i2 = M.mul M.one (e i2) := (M.one_mul (e i2)).symm
        _ = M.mul (M.add (e i0) (e i1)) (e i2) := by rw [hsum01]
        _ = M.add (M.mul (e i0) (e i2)) (M.mul (e i1) (e i2)) :=
            M.right_distrib (e i0) (e i1) (e i2)
        _ = M.zero := by
            rw [(he.1.2.1 i0 i2 h02).1, (he.1.2.1 i1 i2 h12).1, M.add_zero]
    exact absurd he2_zero (he.1.1 i2).2

end DomainTheory

/-! ## 3. Simplicity & Center Theory of `Mat2 α` over Any Field -/

section FieldTheory

variable {α : Type u} (K : FieldRing α)

theorem mat2_conj_a {α : Type u} (R : UnitalRing α) (m : Mat2 α) :
    let M := Mat2Ring R
    let E11 : Mat2 α := ⟨R.one, R.zero, R.zero, R.zero⟩
    let E12 : Mat2 α := ⟨R.zero, R.one, R.zero, R.zero⟩
    let E21 : Mat2 α := ⟨R.zero, R.zero, R.one, R.zero⟩
    M.add (M.mul (M.mul E11 m) E11) (M.mul (M.mul E21 m) E12) = ⟨m.a, R.zero, R.zero, m.a⟩ := by
  dsimp [Mat2Ring]
  exact Mat2.ext
    (by simp [R.zero_add, R.add_zero, R.zero_mul, R.mul_zero, R.one_mul, R.mul_one])
    (by simp [R.zero_add, R.add_zero, R.zero_mul, R.mul_zero, R.one_mul, R.mul_one])
    (by simp [R.zero_add, R.add_zero, R.zero_mul, R.mul_zero, R.one_mul, R.mul_one])
    (by simp [R.zero_add, R.add_zero, R.zero_mul, R.mul_zero, R.one_mul, R.mul_one])

theorem mat2_conj_b {α : Type u} (R : UnitalRing α) (m : Mat2 α) :
    let M := Mat2Ring R
    let E11 : Mat2 α := ⟨R.one, R.zero, R.zero, R.zero⟩
    let E21 : Mat2 α := ⟨R.zero, R.zero, R.one, R.zero⟩
    let E22 : Mat2 α := ⟨R.zero, R.zero, R.zero, R.one⟩
    M.add (M.mul (M.mul E11 m) E21) (M.mul (M.mul E21 m) E22) = ⟨m.b, R.zero, R.zero, m.b⟩ := by
  dsimp [Mat2Ring]
  exact Mat2.ext
    (by simp [R.zero_add, R.add_zero, R.zero_mul, R.mul_zero, R.one_mul, R.mul_one])
    (by simp [R.zero_add, R.add_zero, R.zero_mul, R.mul_zero, R.one_mul, R.mul_one])
    (by simp [R.zero_add, R.add_zero, R.zero_mul, R.mul_zero, R.one_mul, R.mul_one])
    (by simp [R.zero_add, R.add_zero, R.zero_mul, R.mul_zero, R.one_mul, R.mul_one])

theorem mat2_conj_c {α : Type u} (R : UnitalRing α) (m : Mat2 α) :
    let M := Mat2Ring R
    let E11 : Mat2 α := ⟨R.one, R.zero, R.zero, R.zero⟩
    let E12 : Mat2 α := ⟨R.zero, R.one, R.zero, R.zero⟩
    let E22 : Mat2 α := ⟨R.zero, R.zero, R.zero, R.one⟩
    M.add (M.mul (M.mul E12 m) E11) (M.mul (M.mul E22 m) E12) = ⟨m.c, R.zero, R.zero, m.c⟩ := by
  dsimp [Mat2Ring]
  exact Mat2.ext
    (by simp [R.zero_add, R.add_zero, R.zero_mul, R.mul_zero, R.one_mul, R.mul_one])
    (by simp [R.zero_add, R.add_zero, R.zero_mul, R.mul_zero, R.one_mul, R.mul_one])
    (by simp [R.zero_add, R.add_zero, R.zero_mul, R.mul_zero, R.one_mul, R.mul_one])
    (by simp [R.zero_add, R.add_zero, R.zero_mul, R.mul_zero, R.one_mul, R.mul_one])

theorem mat2_conj_d {α : Type u} (R : UnitalRing α) (m : Mat2 α) :
    let M := Mat2Ring R
    let E12 : Mat2 α := ⟨R.zero, R.one, R.zero, R.zero⟩
    let E21 : Mat2 α := ⟨R.zero, R.zero, R.one, R.zero⟩
    let E22 : Mat2 α := ⟨R.zero, R.zero, R.zero, R.one⟩
    M.add (M.mul (M.mul E12 m) E21) (M.mul (M.mul E22 m) E22) = ⟨m.d, R.zero, R.zero, m.d⟩ := by
  dsimp [Mat2Ring]
  exact Mat2.ext
    (by simp [R.zero_add, R.add_zero, R.zero_mul, R.mul_zero, R.one_mul, R.mul_one])
    (by simp [R.zero_add, R.add_zero, R.zero_mul, R.mul_zero, R.one_mul, R.mul_one])
    (by simp [R.zero_add, R.add_zero, R.zero_mul, R.mul_zero, R.one_mul, R.mul_one])
    (by simp [R.zero_add, R.add_zero, R.zero_mul, R.mul_zero, R.one_mul, R.mul_one])

theorem mat2_scalar_mul_inv {α : Type u} (R : UnitalRing α) {u s : α}
    (hus : R.mul u s = R.one) :
    (Mat2Ring R).mul ⟨u, R.zero, R.zero, u⟩ ⟨s, R.zero, R.zero, s⟩ = (Mat2Ring R).one := by
  dsimp [Mat2Ring]
  exact Mat2.ext
    (by simp [hus, R.zero_add, R.add_zero, R.zero_mul, R.mul_zero])
    (by simp [R.zero_add, R.add_zero, R.zero_mul, R.mul_zero])
    (by simp [R.zero_add, R.add_zero, R.zero_mul, R.mul_zero])
    (by simp [hus, R.zero_add, R.add_zero, R.zero_mul, R.mul_zero])

theorem mat2_isSimpleRing : IsSimpleRing (Mat2Ring K.toUnitalRing) := by
  let R := K.toUnitalRing
  let M := Mat2Ring R
  intro I hI ⟨m, hmI, hmne⟩ x
  let E11 : Mat2 α := ⟨R.one, R.zero, R.zero, R.zero⟩
  let E12 : Mat2 α := ⟨R.zero, R.one, R.zero, R.zero⟩
  let E21 : Mat2 α := ⟨R.zero, R.zero, R.one, R.zero⟩
  let E22 : Mat2 α := ⟨R.zero, R.zero, R.zero, R.one⟩
  have scalar_one : ∀ (s : α), s ≠ R.zero → I ⟨s, R.zero, R.zero, s⟩ → I M.one := by
    intro s hs hsI
    have his : R.mul (K.inv s) s = R.one := by
      rw [K.mul_comm, K.mul_inv_cancel s hs]
    rw [← mat2_scalar_mul_inv R his]
    exact hI.1.2 ⟨K.inv s, R.zero, R.zero, K.inv s⟩ _ hsI
  have hI_one : I M.one := by
    by_cases ha : m.a ≠ R.zero
    · apply scalar_one m.a ha
      rw [← mat2_conj_a R m]
      exact hI.1.1.2.1 _ _ (hI.2.2 _ E11 (hI.1.2 E11 m hmI)) (hI.2.2 _ E12 (hI.1.2 E21 m hmI))
    · have ha0 : m.a = R.zero := Classical.byContradiction (fun h => ha h)
      by_cases hb : m.b ≠ R.zero
      · apply scalar_one m.b hb
        rw [← mat2_conj_b R m]
        exact hI.1.1.2.1 _ _ (hI.2.2 _ E21 (hI.1.2 E11 m hmI)) (hI.2.2 _ E22 (hI.1.2 E21 m hmI))
      · have hb0 : m.b = R.zero := Classical.byContradiction (fun h => hb h)
        by_cases hc : m.c ≠ R.zero
        · apply scalar_one m.c hc
          rw [← mat2_conj_c R m]
          exact hI.1.1.2.1 _ _ (hI.2.2 _ E11 (hI.1.2 E12 m hmI)) (hI.2.2 _ E12 (hI.1.2 E22 m hmI))
        · have hc0 : m.c = R.zero := Classical.byContradiction (fun h => hc h)
          have hd : m.d ≠ R.zero := by
            intro hd0; apply hmne
            cases m; dsimp at ha0 hb0 hc0 hd0; subst ha0 hb0 hc0 hd0; rfl
          apply scalar_one m.d hd
          rw [← mat2_conj_d R m]
          exact hI.1.1.2.1 _ _ (hI.2.2 _ E21 (hI.1.2 E12 m hmI)) (hI.2.2 _ E22 (hI.1.2 E22 m hmI))
  have hx : M.mul x M.one = x := M.mul_one x
  rw [← hx]
  exact hI.1.2 x M.one hI_one

theorem mat2_minimal_two_sided_exactCard_one :
    ExactCard (IsMinimalTwoSidedIdeal (Mat2Ring K.toUnitalRing)) 1 :=
  simpleRing_exactCard_minimal_two_sided_one (Mat2Ring K.toUnitalRing) (mat2_isSimpleRing K)

theorem mat2_center_helper {α : Type u} (R : UnitalRing α)
    (hcomm : ∀ u v : α, R.mul u v = R.mul v u) (m : Mat2 α) :
    IsCentral (Mat2Ring R) m ↔ (m.b = R.zero ∧ m.c = R.zero ∧ m.a = m.d) := by
  constructor
  · intro hc
    have h11 := hc ⟨R.one, R.zero, R.zero, R.zero⟩
    have hb0 : m.b = R.zero := by
      have h := congrArg Mat2.b h11
      dsimp [Mat2Ring] at h
      simp [R.zero_add, R.add_zero, R.zero_mul, R.mul_zero, R.one_mul, R.mul_one] at h
      exact h.symm
    have hc0 : m.c = R.zero := by
      have h := congrArg Mat2.c h11
      dsimp [Mat2Ring] at h
      simp [R.zero_add, R.add_zero, R.zero_mul, R.mul_zero, R.one_mul, R.mul_one] at h
      exact h
    have h12 := hc ⟨R.zero, R.one, R.zero, R.zero⟩
    have had : m.a = m.d := by
      have h := congrArg Mat2.b h12
      dsimp [Mat2Ring] at h
      simp [R.zero_add, R.add_zero, R.zero_mul, R.mul_zero, R.one_mul, R.mul_one] at h
      exact h
    exact ⟨hb0, hc0, had⟩
  · intro ⟨hb0, hc0, had⟩ x
    cases m with
    | mk a b c d =>
      dsimp at hb0 hc0 had
      subst hb0 hc0 had
      dsimp [Mat2Ring]
      exact Mat2.ext
        (by simp [R.zero_add, R.add_zero, R.zero_mul, R.mul_zero, hcomm a])
        (by simp [R.zero_add, R.add_zero, R.zero_mul, R.mul_zero, hcomm a])
        (by simp [R.zero_add, R.add_zero, R.zero_mul, R.mul_zero, hcomm a])
        (by simp [R.zero_add, R.add_zero, R.zero_mul, R.mul_zero, hcomm a])

theorem mat2_center_iff (m : Mat2 α) :
    IsCentral (Mat2Ring K.toUnitalRing) m ↔
      (m.b = K.zero ∧ m.c = K.zero ∧ m.a = m.d) :=
  mat2_center_helper K.toUnitalRing K.mul_comm m

theorem mat2_central_prim_iff (m : Mat2 α) :
    IsCentralPrimitiveIdempotent (Mat2Ring K.toUnitalRing) m ↔
      m = (Mat2Ring K.toUnitalRing).one := by
  let R := K.toUnitalRing
  let M := Mat2Ring R
  have classify_cidemp : ∀ z : Mat2 α, IsCentralIdempotent M z → z = M.zero ∨ z = M.one := by
    intro z ⟨hzidem, hzcent⟩
    obtain ⟨hb0, hc0, had⟩ := (mat2_center_iff K z).mp hzcent
    have ha_idem : R.mul z.a z.a = z.a := by
      have h : R.add (R.mul z.a z.a) (R.mul z.b z.c) = z.a := congrArg Mat2.a hzidem
      rw [hb0, R.zero_mul, R.add_zero] at h
      exact h
    cases domain_idemp_zero_or_one K.toDomainRing ha_idem with
    | inl ha0 =>
      left
      cases z; dsimp at hb0 hc0 had ha0; subst ha0; subst had hb0 hc0; rfl
    | inr ha1 =>
      right
      cases z; dsimp at hb0 hc0 had ha1; subst ha1; subst had hb0 hc0; rfl
  constructor
  · intro ⟨hzci, hzne, _⟩
    cases classify_cidemp m hzci with
    | inl h0 => exact absurd h0 hzne
    | inr h1 => exact h1
  · intro hm1
    subst hm1
    refine ⟨⟨M.one_mul M.one, fun x => by rw [M.one_mul, M.mul_one]⟩, M.one_ne_zero, ?_⟩
    intro ⟨f, g, hfci, hfne, hgci, hgne, horth, _⟩
    cases classify_cidemp f hfci with
    | inl hf0 => exact hfne hf0
    | inr hf1 =>
      cases classify_cidemp g hgci with
      | inl hg0 => exact hgne hg0
      | inr hg1 =>
        have h10 : M.one = M.zero := by
          have h := horth.1
          rw [hf1, hg1, M.one_mul] at h
          exact h
        exact M.one_ne_zero h10

theorem mat2_central_prim_exactCard_one :
    ExactCard (IsCentralPrimitiveIdempotent (Mat2Ring K.toUnitalRing)) 1 := by
  let M := Mat2Ring K.toUnitalRing
  refine ⟨fun _ => M.one, ?_, ?_, ?_⟩
  · intro _
    exact (mat2_central_prim_iff K M.one).mpr rfl
  · intro i j _
    exact Fin.ext (by omega)
  · intro m hm
    exact ⟨⟨0, Nat.zero_lt_one⟩, ((mat2_central_prim_iff K m).mp hm).symm⟩

end FieldTheory

/-! ## 4. Split Clifford Algebra `Cl_{1,1}(F_3) ≅ M_2(F_3)` & Six-Way Separation -/

abbrev Mat2F3Ring : UnitalRing (Mat2 F3) := Mat2Ring F3Ring

/-- `Cl_{1,1}(F_3)` on basis `(1, γ_1, γ_2, γ_{12})` with `γ_1^2 = 1`,
    `γ_2^2 = -1`, `γ_1 γ_2 = γ_{12} = -γ_2 γ_1`, `γ_{12}^2 = 1`. -/
structure Cl11F3 where
  s   : F3
  v1  : F3
  v2  : F3
  v12 : F3
  deriving DecidableEq, Repr

theorem Cl11F3.ext {x y : Cl11F3}
    (hs : x.s = y.s) (h1 : x.v1 = y.v1) (h2 : x.v2 = y.v2) (h12 : x.v12 = y.v12) : x = y := by
  cases x; cases y; dsimp at hs h1 h2 h12; subst hs h1 h2 h12; rfl

def cl11ToMat2 (x : Cl11F3) : Mat2 F3 :=
  ⟨F3.add x.s x.v1,
   F3.add x.v2 x.v12,
   F3.add (F3.neg x.v2) x.v12,
   F3.add x.s (F3.neg x.v1)⟩

def mat2ToCl11 (m : Mat2 F3) : Cl11F3 :=
  ⟨F3.mul F3.c2 (F3.add m.a m.d),
   F3.mul F3.c2 (F3.add m.a (F3.neg m.d)),
   F3.mul F3.c2 (F3.add m.b (F3.neg m.c)),
   F3.mul F3.c2 (F3.add m.b m.c)⟩

theorem cl11ToMat2_left_inv (x : Cl11F3) : mat2ToCl11 (cl11ToMat2 x) = x := by
  cases x with
  | mk s v1 v2 v12 =>
    cases s <;> cases v1 <;> cases v2 <;> cases v12 <;> rfl

theorem cl11ToMat2_right_inv (m : Mat2 F3) : cl11ToMat2 (mat2ToCl11 m) = m := by
  cases m with
  | mk a b c d =>
    cases a <;> cases b <;> cases c <;> cases d <;> rfl

theorem cl11ToMat2_add (u w : Cl11F3) :
    cl11ToMat2 ⟨F3.add u.s w.s, F3.add u.v1 w.v1, F3.add u.v2 w.v2, F3.add u.v12 w.v12⟩ =
    Mat2F3Ring.add (cl11ToMat2 u) (cl11ToMat2 w) := by
  cases u with | mk us u1 u2 u12 =>
  cases w with | mk ws w1 w2 w12 =>
  exact Mat2.ext
    (by cases us <;> cases ws <;> cases u1 <;> cases w1 <;> rfl)
    (by cases u2 <;> cases w2 <;> cases u12 <;> cases w12 <;> rfl)
    (by cases u2 <;> cases w2 <;> cases u12 <;> cases w12 <;> rfl)
    (by cases us <;> cases ws <;> cases u1 <;> cases w1 <;> rfl)

theorem mat2ToCl11_add (m n : Mat2 F3) :
    mat2ToCl11 (Mat2F3Ring.add m n) =
    ⟨F3.add (mat2ToCl11 m).s (mat2ToCl11 n).s,
     F3.add (mat2ToCl11 m).v1 (mat2ToCl11 n).v1,
     F3.add (mat2ToCl11 m).v2 (mat2ToCl11 n).v2,
     F3.add (mat2ToCl11 m).v12 (mat2ToCl11 n).v12⟩ := by
  cases m with | mk ma mb mc md =>
  cases n with | mk na nb nc nd =>
  exact Cl11F3.ext
    (by cases ma <;> cases md <;> cases na <;> cases nd <;> rfl)
    (by cases ma <;> cases md <;> cases na <;> cases nd <;> rfl)
    (by cases mb <;> cases mc <;> cases nb <;> cases nc <;> rfl)
    (by cases mb <;> cases mc <;> cases nb <;> cases nc <;> rfl)

def Cl11F3Ring : UnitalRing Cl11F3 where
  zero := ⟨F3.c0, F3.c0, F3.c0, F3.c0⟩
  one := ⟨F3.c1, F3.c0, F3.c0, F3.c0⟩
  add := fun x y =>
    ⟨F3.add x.s y.s, F3.add x.v1 y.v1, F3.add x.v2 y.v2, F3.add x.v12 y.v12⟩
  neg := fun x =>
    ⟨F3.neg x.s, F3.neg x.v1, F3.neg x.v2, F3.neg x.v12⟩
  mul := fun x y => mat2ToCl11 (Mat2F3Ring.mul (cl11ToMat2 x) (cl11ToMat2 y))
  add_assoc := fun x y z =>
    Cl11F3.ext (F3Ring.add_assoc x.s y.s z.s) (F3Ring.add_assoc x.v1 y.v1 z.v1)
      (F3Ring.add_assoc x.v2 y.v2 z.v2) (F3Ring.add_assoc x.v12 y.v12 z.v12)
  add_comm := fun x y =>
    Cl11F3.ext (F3Ring.add_comm x.s y.s) (F3Ring.add_comm x.v1 y.v1)
      (F3Ring.add_comm x.v2 y.v2) (F3Ring.add_comm x.v12 y.v12)
  zero_add := fun x =>
    Cl11F3.ext (F3Ring.zero_add x.s) (F3Ring.zero_add x.v1)
      (F3Ring.zero_add x.v2) (F3Ring.zero_add x.v12)
  add_left_neg := fun x =>
    Cl11F3.ext (F3Ring.add_left_neg x.s) (F3Ring.add_left_neg x.v1)
      (F3Ring.add_left_neg x.v2) (F3Ring.add_left_neg x.v12)
  mul_assoc := fun x y z => by
    rw [cl11ToMat2_right_inv, cl11ToMat2_right_inv, Mat2F3Ring.mul_assoc]
  one_mul := fun x => by
    have h1 : cl11ToMat2 ⟨F3.c1, F3.c0, F3.c0, F3.c0⟩ = Mat2F3Ring.one := rfl
    rw [h1, Mat2F3Ring.one_mul, cl11ToMat2_left_inv]
  mul_one := fun x => by
    have h1 : cl11ToMat2 ⟨F3.c1, F3.c0, F3.c0, F3.c0⟩ = Mat2F3Ring.one := rfl
    rw [h1, Mat2F3Ring.mul_one, cl11ToMat2_left_inv]
  left_distrib := fun x y z => by
    rw [cl11ToMat2_add y z, Mat2F3Ring.left_distrib, mat2ToCl11_add]
  right_distrib := fun x y z => by
    rw [cl11ToMat2_add x y, Mat2F3Ring.right_distrib, mat2ToCl11_add]
  one_ne_zero := by decide

/-- Verify the defining Clifford relations `γ_1^2 = 1`, `γ_2^2 = -1`, `γ_1 γ_2 + γ_2 γ_1 = 0`. -/
theorem cl11_f3_defining_relations :
    let γ1 : Cl11F3 := ⟨F3.c0, F3.c1, F3.c0, F3.c0⟩
    let γ2 : Cl11F3 := ⟨F3.c0, F3.c0, F3.c1, F3.c0⟩
    Cl11F3Ring.mul γ1 γ1 = Cl11F3Ring.one ∧
    Cl11F3Ring.mul γ2 γ2 = Cl11F3Ring.neg Cl11F3Ring.one ∧
    Cl11F3Ring.add (Cl11F3Ring.mul γ1 γ2) (Cl11F3Ring.mul γ2 γ1) = Cl11F3Ring.zero := by
  decide

/-- Explicit algebra isomorphism `Cl_{1,1}(F_3) ≅ M_2(F_3)`. -/
def cl11_f3_iso_mat2_f3 : RingIso Cl11F3Ring Mat2F3Ring where
  toFun := cl11ToMat2
  invFun := mat2ToCl11
  left_inv := cl11ToMat2_left_inv
  right_inv := cl11ToMat2_right_inv
  map_zero := rfl
  map_one := rfl
  map_add := cl11ToMat2_add
  map_mul := fun _ _ => cl11ToMat2_right_inv _

/-! ### Minimal Left Ideals of `M_2(F_3)` (Exact Count = `4`) -/

def mat2F3MinLeft (k : Fin 4) : Mat2 F3 → Prop :=
  match k with
  | ⟨0, _⟩ => fun m => m.b = F3.c0 ∧ m.d = F3.c0
  | ⟨1, _⟩ => fun m => m.a = F3.c0 ∧ m.c = F3.c0
  | ⟨2, _⟩ => fun m => m.b = m.a ∧ m.d = m.c
  | ⟨3, _⟩ => fun m => m.b = F3.mul F3.c2 m.a ∧ m.d = F3.mul F3.c2 m.c

theorem mat2F3MinLeft_isMinimal (k : Fin 4) :
    IsMinimalLeftIdeal Mat2F3Ring (mat2F3MinLeft k) := by
  match k with
  | ⟨0, _⟩ =>
    refine ⟨⟨⟨⟨rfl, rfl⟩, ?_, ?_⟩, ?_⟩, ⟨⟨F3.c1, F3.c0, F3.c0, F3.c0⟩, ⟨rfl, rfl⟩, by decide⟩, ?_⟩
    · intro x y hx hy
      dsimp [mat2F3MinLeft, Mat2F3Ring, Mat2Ring] at *
      rw [hx.1, hy.1, hx.2, hy.2]; exact ⟨rfl, rfl⟩
    · intro x hx
      dsimp [mat2F3MinLeft, Mat2F3Ring, Mat2Ring] at *
      rw [hx.1, hx.2]; exact ⟨rfl, rfl⟩
    · intro r x hx
      dsimp [mat2F3MinLeft, Mat2F3Ring, Mat2Ring, F3Ring] at *
      rw [hx.1, hx.2]; exact ⟨by simp, by simp⟩
    · intro M hM ⟨x, hxM, hxne⟩ hsub y hy
      obtain ⟨hxb, hxd⟩ := hsub x hxM
      dsimp [mat2F3MinLeft] at hy hxb hxd
      by_cases hxa : x.a ≠ F3.c0
      · let r : Mat2 F3 := ⟨F3.mul y.a (F3.inv x.a), F3.c0, F3.mul y.c (F3.inv x.a), F3.c0⟩
        have hmul : Mat2F3Ring.mul r x = y := by
          cases x with | mk xa xb xc xd =>
          cases y with | mk ya yb yc yd =>
          dsimp [r] at *
          rw [hxb, hxd, hy.1, hy.2]
          cases xa with
          | c0 => exact absurd rfl hxa
          | c1 => cases xc <;> cases ya <;> cases yc <;> rfl
          | c2 => cases xc <;> cases ya <;> cases yc <;> rfl
        rw [← hmul]; exact hM.2 r x hxM
      · have hxa0 : x.a = F3.c0 := Classical.byContradiction (fun h => hxa h)
        have hxc : x.c ≠ F3.c0 := by
          intro hxc0; apply hxne
          cases x; dsimp at hxa0 hxb hxc0 hxd; subst hxa0 hxb hxc0 hxd; rfl
        let r : Mat2 F3 := ⟨F3.c0, F3.mul y.a (F3.inv x.c), F3.c0, F3.mul y.c (F3.inv x.c)⟩
        have hmul : Mat2F3Ring.mul r x = y := by
          cases x with | mk xa xb xc xd =>
          cases y with | mk ya yb yc yd =>
          dsimp [r] at *
          rw [hxa0, hxb, hxd, hy.1, hy.2]
          cases xc with
          | c0 => exact absurd rfl hxc
          | c1 => cases ya <;> cases yc <;> rfl
          | c2 => cases ya <;> cases yc <;> rfl
        rw [← hmul]; exact hM.2 r x hxM
  | ⟨1, _⟩ =>
    refine ⟨⟨⟨⟨rfl, rfl⟩, ?_, ?_⟩, ?_⟩, ⟨⟨F3.c0, F3.c1, F3.c0, F3.c0⟩, ⟨rfl, rfl⟩, by decide⟩, ?_⟩
    · intro x y hx hy
      dsimp [mat2F3MinLeft, Mat2F3Ring, Mat2Ring] at *
      rw [hx.1, hy.1, hx.2, hy.2]; exact ⟨rfl, rfl⟩
    · intro x hx
      dsimp [mat2F3MinLeft, Mat2F3Ring, Mat2Ring] at *
      rw [hx.1, hx.2]; exact ⟨rfl, rfl⟩
    · intro r x hx
      dsimp [mat2F3MinLeft, Mat2F3Ring, Mat2Ring, F3Ring] at *
      rw [hx.1, hx.2]; exact ⟨by simp, by simp⟩
    · intro M hM ⟨x, hxM, hxne⟩ hsub y hy
      obtain ⟨hxa, hxc⟩ := hsub x hxM
      dsimp [mat2F3MinLeft] at hy hxa hxc
      by_cases hxb : x.b ≠ F3.c0
      · let r : Mat2 F3 := ⟨F3.mul y.b (F3.inv x.b), F3.c0, F3.mul y.d (F3.inv x.b), F3.c0⟩
        have hmul : Mat2F3Ring.mul r x = y := by
          cases x with | mk xa xb xc xd =>
          cases y with | mk ya yb yc yd =>
          dsimp [r] at *
          rw [hxa, hxc, hy.1, hy.2]
          cases xb with
          | c0 => exact absurd rfl hxb
          | c1 => cases xd <;> cases yb <;> cases yd <;> rfl
          | c2 => cases xd <;> cases yb <;> cases yd <;> rfl
        rw [← hmul]; exact hM.2 r x hxM
      · have hxb0 : x.b = F3.c0 := Classical.byContradiction (fun h => hxb h)
        have hxd : x.d ≠ F3.c0 := by
          intro hxd0; apply hxne
          cases x; dsimp at hxa hxb0 hxc hxd0; subst hxa hxb0 hxc hxd0; rfl
        let r : Mat2 F3 := ⟨F3.c0, F3.mul y.b (F3.inv x.d), F3.c0, F3.mul y.d (F3.inv x.d)⟩
        have hmul : Mat2F3Ring.mul r x = y := by
          cases x with | mk xa xb xc xd =>
          cases y with | mk ya yb yc yd =>
          dsimp [r] at *
          rw [hxa, hxb0, hxc, hy.1, hy.2]
          cases xd with
          | c0 => exact absurd rfl hxd
          | c1 => cases yb <;> cases yd <;> rfl
          | c2 => cases yb <;> cases yd <;> rfl
        rw [← hmul]; exact hM.2 r x hxM
  | ⟨2, _⟩ =>
    refine ⟨⟨⟨⟨rfl, rfl⟩, ?_, ?_⟩, ?_⟩, ⟨⟨F3.c1, F3.c1, F3.c0, F3.c0⟩, ⟨rfl, rfl⟩, by decide⟩, ?_⟩
    · intro x y hx hy
      dsimp [mat2F3MinLeft, Mat2F3Ring, Mat2Ring] at *
      rw [hx.1, hy.1, hx.2, hy.2]; exact ⟨rfl, rfl⟩
    · intro x hx
      dsimp [mat2F3MinLeft, Mat2F3Ring, Mat2Ring] at *
      rw [hx.1, hx.2]; exact ⟨rfl, rfl⟩
    · intro r x hx
      dsimp [mat2F3MinLeft, Mat2F3Ring, Mat2Ring] at *
      rw [hx.1, hx.2]; exact ⟨rfl, rfl⟩
    · intro M hM ⟨x, hxM, hxne⟩ hsub y hy
      obtain ⟨hxb, hxd⟩ := hsub x hxM
      dsimp [mat2F3MinLeft] at hy hxb hxd
      by_cases hxa : x.a ≠ F3.c0
      · let r : Mat2 F3 := ⟨F3.mul y.a (F3.inv x.a), F3.c0, F3.mul y.c (F3.inv x.a), F3.c0⟩
        have hmul : Mat2F3Ring.mul r x = y := by
          cases x with | mk xa xb xc xd =>
          cases y with | mk ya yb yc yd =>
          dsimp [r] at *
          rw [hxb, hxd, hy.1, hy.2]
          cases xa with
          | c0 => exact absurd rfl hxa
          | c1 => cases xc <;> cases ya <;> cases yc <;> rfl
          | c2 => cases xc <;> cases ya <;> cases yc <;> rfl
        rw [← hmul]; exact hM.2 r x hxM
      · have hxa0 : x.a = F3.c0 := Classical.byContradiction (fun h => hxa h)
        have hxc : x.c ≠ F3.c0 := by
          intro hxc0; apply hxne
          cases x with | mk xa xb xc xd =>
          dsimp at hxa0 hxb hxc0 hxd
          rw [hxb, hxd, hxa0, hxc0]; rfl
        let r : Mat2 F3 := ⟨F3.c0, F3.mul y.a (F3.inv x.c), F3.c0, F3.mul y.c (F3.inv x.c)⟩
        have hmul : Mat2F3Ring.mul r x = y := by
          cases x with | mk xa xb xc xd =>
          cases y with | mk ya yb yc yd =>
          dsimp [r] at *
          rw [hxb, hxd, hxa0, hy.1, hy.2]
          cases xc with
          | c0 => exact absurd rfl hxc
          | c1 => cases ya <;> cases yc <;> rfl
          | c2 => cases ya <;> cases yc <;> rfl
        rw [← hmul]; exact hM.2 r x hxM
  | ⟨3, _⟩ =>
    refine ⟨⟨⟨⟨rfl, rfl⟩, ?_, ?_⟩, ?_⟩, ⟨⟨F3.c1, F3.c2, F3.c0, F3.c0⟩, ⟨rfl, rfl⟩, by decide⟩, ?_⟩
    · intro x y hx hy
      cases x with | mk xa xb xc xd =>
      cases y with | mk ya yb yc yd =>
      dsimp [mat2F3MinLeft] at hx hy
      dsimp [mat2F3MinLeft, Mat2F3Ring, Mat2Ring]
      rw [hx.1, hx.2, hy.1, hy.2]
      exact ⟨by cases xa <;> cases ya <;> rfl, by cases xc <;> cases yc <;> rfl⟩
    · intro x hx
      cases x with | mk xa xb xc xd =>
      dsimp [mat2F3MinLeft] at hx
      dsimp [mat2F3MinLeft, Mat2F3Ring, Mat2Ring]
      rw [hx.1, hx.2]
      exact ⟨by cases xa <;> rfl, by cases xc <;> rfl⟩
    · intro r x hx
      cases r with | mk ra rb rc rd =>
      cases x with | mk xa xb xc xd =>
      dsimp [mat2F3MinLeft] at hx
      dsimp [mat2F3MinLeft, Mat2F3Ring, Mat2Ring]
      rw [hx.1, hx.2]
      exact ⟨by cases ra <;> cases rb <;> cases xa <;> cases xc <;> rfl,
             by cases rc <;> cases rd <;> cases xa <;> cases xc <;> rfl⟩
    · intro M hM ⟨x, hxM, hxne⟩ hsub y hy
      obtain ⟨hxb, hxd⟩ := hsub x hxM
      dsimp [mat2F3MinLeft] at hy hxb hxd
      by_cases hxa : x.a ≠ F3.c0
      · let r : Mat2 F3 := ⟨F3.mul y.a (F3.inv x.a), F3.c0, F3.mul y.c (F3.inv x.a), F3.c0⟩
        have hmul : Mat2F3Ring.mul r x = y := by
          cases x with | mk xa xb xc xd =>
          cases y with | mk ya yb yc yd =>
          dsimp [r] at *
          rw [hxb, hxd, hy.1, hy.2]
          cases xa with
          | c0 => exact absurd rfl hxa
          | c1 => cases xc <;> cases ya <;> cases yc <;> rfl
          | c2 => cases xc <;> cases ya <;> cases yc <;> rfl
        rw [← hmul]; exact hM.2 r x hxM
      · have hxa0 : x.a = F3.c0 := Classical.byContradiction (fun h => hxa h)
        have hxc : x.c ≠ F3.c0 := by
          intro hxc0; apply hxne
          cases x with | mk xa xb xc xd =>
          dsimp at hxa0 hxb hxc0 hxd
          rw [hxb, hxd, hxa0, hxc0]; rfl
        let r : Mat2 F3 := ⟨F3.c0, F3.mul y.a (F3.inv x.c), F3.c0, F3.mul y.c (F3.inv x.c)⟩
        have hmul : Mat2F3Ring.mul r x = y := by
          cases x with | mk xa xb xc xd =>
          cases y with | mk ya yb yc yd =>
          dsimp [r] at *
          rw [hxb, hxd, hxa0, hy.1, hy.2]
          cases xc with
          | c0 => exact absurd rfl hxc
          | c1 => cases ya <;> cases yc <;> rfl
          | c2 => cases ya <;> cases yc <;> rfl
        rw [← hmul]; exact hM.2 r x hxM
  | ⟨n + 4, hn⟩ => omega

theorem mat2_f3_minimal_left_exactCard_four :
    ExactCard (IsMinimalLeftIdeal Mat2F3Ring) 4 := by
  refine ⟨mat2F3MinLeft, mat2F3MinLeft_isMinimal, ?_, ?_⟩
  · intro i j hij
    have test : ∀ (m : Mat2 F3), mat2F3MinLeft i m ↔ mat2F3MinLeft j m :=
      fun m => by rw [hij]
    match i, j with
    | ⟨0, _⟩, ⟨0, _⟩ => rfl
    | ⟨1, _⟩, ⟨1, _⟩ => rfl
    | ⟨2, _⟩, ⟨2, _⟩ => rfl
    | ⟨3, _⟩, ⟨3, _⟩ => rfl
    | ⟨0, _⟩, ⟨1, _⟩ =>
      have h := (test ⟨F3.c1, F3.c0, F3.c0, F3.c0⟩).mp ⟨rfl, rfl⟩
      exact absurd h.1 (by decide)
    | ⟨0, _⟩, ⟨2, _⟩ =>
      have h := (test ⟨F3.c1, F3.c0, F3.c0, F3.c0⟩).mp ⟨rfl, rfl⟩
      exact absurd h.1 (by decide)
    | ⟨0, _⟩, ⟨3, _⟩ =>
      have h := (test ⟨F3.c1, F3.c0, F3.c0, F3.c0⟩).mp ⟨rfl, rfl⟩
      exact absurd h.1 (by decide)
    | ⟨1, _⟩, ⟨0, _⟩ =>
      have h := (test ⟨F3.c1, F3.c0, F3.c0, F3.c0⟩).mpr ⟨rfl, rfl⟩
      exact absurd h.1 (by decide)
    | ⟨1, _⟩, ⟨2, _⟩ =>
      have h := (test ⟨F3.c0, F3.c1, F3.c0, F3.c0⟩).mp ⟨rfl, rfl⟩
      exact absurd h.1 (by decide)
    | ⟨1, _⟩, ⟨3, _⟩ =>
      have h := (test ⟨F3.c0, F3.c1, F3.c0, F3.c0⟩).mp ⟨rfl, rfl⟩
      exact absurd h.1 (by decide)
    | ⟨2, _⟩, ⟨0, _⟩ =>
      have h := (test ⟨F3.c1, F3.c0, F3.c0, F3.c0⟩).mpr ⟨rfl, rfl⟩
      exact absurd h.1 (by decide)
    | ⟨2, _⟩, ⟨1, _⟩ =>
      have h := (test ⟨F3.c0, F3.c1, F3.c0, F3.c0⟩).mpr ⟨rfl, rfl⟩
      exact absurd h.1 (by decide)
    | ⟨2, _⟩, ⟨3, _⟩ =>
      have h := (test ⟨F3.c1, F3.c1, F3.c0, F3.c0⟩).mp ⟨rfl, rfl⟩
      exact absurd h.1 (by decide)
    | ⟨3, _⟩, ⟨0, _⟩ =>
      have h := (test ⟨F3.c1, F3.c0, F3.c0, F3.c0⟩).mpr ⟨rfl, rfl⟩
      exact absurd h.1 (by decide)
    | ⟨3, _⟩, ⟨1, _⟩ =>
      have h := (test ⟨F3.c0, F3.c1, F3.c0, F3.c0⟩).mpr ⟨rfl, rfl⟩
      exact absurd h.1 (by decide)
    | ⟨3, _⟩, ⟨2, _⟩ =>
      have h := (test ⟨F3.c1, F3.c1, F3.c0, F3.c0⟩).mpr ⟨rfl, rfl⟩
      exact absurd h.1 (by decide)
    | ⟨n + 4, hn⟩, _ => omega
    | _, ⟨n + 4, hn⟩ => omega
  · intro L ⟨hL, ⟨m, hmL, hmne⟩, hLmin⟩
    have hex_row : ∃ u v : F3, (u ≠ F3.c0 ∨ v ≠ F3.c0) ∧ L ⟨u, v, F3.c0, F3.c0⟩ := by
      by_cases htop : m.a ≠ F3.c0 ∨ m.b ≠ F3.c0
      · refine ⟨m.a, m.b, htop, ?_⟩
        have hmul : Mat2F3Ring.mul ⟨F3.c1, F3.c0, F3.c0, F3.c0⟩ m = ⟨m.a, m.b, F3.c0, F3.c0⟩ := by
          cases m with | mk a b c d =>
          cases a <;> cases b <;> cases c <;> cases d <;> rfl
        rw [← hmul]; exact hL.2 _ m hmL
      · have ha0 : m.a = F3.c0 := Classical.byContradiction (fun h => htop (Or.inl h))
        have hb0 : m.b = F3.c0 := Classical.byContradiction (fun h => htop (Or.inr h))
        have hbot : m.c ≠ F3.c0 ∨ m.d ≠ F3.c0 := by
          apply Classical.byContradiction
          intro hnb
          have hc0 : m.c = F3.c0 := Classical.byContradiction (fun h => hnb (Or.inl h))
          have hd0 : m.d = F3.c0 := Classical.byContradiction (fun h => hnb (Or.inr h))
          apply hmne
          cases m; dsimp at ha0 hb0 hc0 hd0; subst ha0 hb0 hc0 hd0; rfl
        refine ⟨m.c, m.d, hbot, ?_⟩
        have hmul : Mat2F3Ring.mul ⟨F3.c0, F3.c1, F3.c0, F3.c0⟩ m = ⟨m.c, m.d, F3.c0, F3.c0⟩ := by
          cases m with | mk a b c d =>
          cases a <;> cases b <;> cases c <;> cases d <;> rfl
        rw [← hmul]; exact hL.2 _ m hmL
    obtain ⟨u, v, huv, hrowL⟩ := hex_row
    have match_k : ∃ k : Fin 4, mat2F3MinLeft k ⟨u, v, F3.c0, F3.c0⟩ := by
      cases u with
      | c0 =>
        cases v with
        | c0 => cases huv with | inl h => exact absurd rfl h | inr h => exact absurd rfl h
        | c1 => exact ⟨⟨1, by decide⟩, ⟨rfl, rfl⟩⟩
        | c2 => exact ⟨⟨1, by decide⟩, ⟨rfl, rfl⟩⟩
      | c1 =>
        cases v with
        | c0 => exact ⟨⟨0, by decide⟩, ⟨rfl, rfl⟩⟩
        | c1 => exact ⟨⟨2, by decide⟩, ⟨rfl, rfl⟩⟩
        | c2 => exact ⟨⟨3, by decide⟩, ⟨rfl, rfl⟩⟩
      | c2 =>
        cases v with
        | c0 => exact ⟨⟨0, by decide⟩, ⟨rfl, rfl⟩⟩
        | c1 => exact ⟨⟨3, by decide⟩, ⟨rfl, rfl⟩⟩
        | c2 => exact ⟨⟨2, by decide⟩, ⟨rfl, rfl⟩⟩
    obtain ⟨k, hk_in⟩ := match_k
    have hrow_ne : (⟨u, v, F3.c0, F3.c0⟩ : Mat2 F3) ≠ Mat2F3Ring.zero := by
      intro hz
      cases huv with
      | inl hu => exact hu (congrArg Mat2.a hz)
      | inr hv => exact hv (congrArg Mat2.b hz)
    let Inter : Mat2 F3 → Prop := fun x => L x ∧ mat2F3MinLeft k x
    have hLk := mat2F3MinLeft_isMinimal k
    have hInter_left : IsLeftIdeal Mat2F3Ring Inter :=
      ⟨⟨⟨hL.1.1, hLk.1.1.1⟩,
        fun a b ha hb => ⟨hL.1.2.1 a b ha.1 hb.1, hLk.1.1.2.1 a b ha.2 hb.2⟩,
        fun a ha => ⟨hL.1.2.2 a ha.1, hLk.1.1.2.2 a ha.2⟩⟩,
       fun r x hx => ⟨hL.2 r x hx.1, hLk.1.2 r x hx.2⟩⟩
    have hInter_nz : IsNonzeroPred Mat2F3Ring Inter :=
      ⟨⟨u, v, F3.c0, F3.c0⟩, ⟨hrowL, hk_in⟩, hrow_ne⟩
    have hsub1 : ∀ x, mat2F3MinLeft k x → Inter x :=
      hLk.2.2 Inter hInter_left hInter_nz (fun _ hx => hx.2)
    have hsub2 : ∀ x, L x → Inter x :=
      hLmin Inter hInter_left hInter_nz (fun _ hx => hx.1)
    refine ⟨k, ?_⟩
    funext x
    exact propext ⟨fun hx => (hsub1 x hx).1, fun hx => (hsub2 x hx).2⟩

/-! ### Exact Counts of Idempotents & Primitive Decompositions on `M_2(F_3)` -/

def prim12 : Fin 12 → Mat2 F3
  | ⟨0, _⟩  => ⟨F3.c1, F3.c0, F3.c0, F3.c0⟩
  | ⟨1, _⟩  => ⟨F3.c0, F3.c0, F3.c0, F3.c1⟩
  | ⟨2, _⟩  => ⟨F3.c1, F3.c1, F3.c0, F3.c0⟩
  | ⟨3, _⟩  => ⟨F3.c0, F3.c2, F3.c0, F3.c1⟩
  | ⟨4, _⟩  => ⟨F3.c1, F3.c2, F3.c0, F3.c0⟩
  | ⟨5, _⟩  => ⟨F3.c0, F3.c1, F3.c0, F3.c1⟩
  | ⟨6, _⟩  => ⟨F3.c1, F3.c0, F3.c1, F3.c0⟩
  | ⟨7, _⟩  => ⟨F3.c0, F3.c0, F3.c2, F3.c1⟩
  | ⟨8, _⟩  => ⟨F3.c1, F3.c0, F3.c2, F3.c0⟩
  | ⟨9, _⟩  => ⟨F3.c0, F3.c0, F3.c1, F3.c1⟩
  | ⟨10, _⟩ => ⟨F3.c2, F3.c1, F3.c1, F3.c2⟩
  | ⟨11, _⟩ => ⟨F3.c2, F3.c2, F3.c2, F3.c2⟩

theorem prim12_inj : ∀ i j : Fin 12, prim12 i = prim12 j → i = j := by
  decide

theorem prim12_isPrimitive : ∀ i : Fin 12, IsPrimitiveIdempotent Mat2F3Ring (prim12 i) := by
  intro i
  apply (mat2_prim_idemp_iff F3DomainRing (prim12 i)).mpr
  revert i
  decide

theorem prim12_cond_surj :
    ∀ a b c d : F3,
      F3.add a d = F3.c1 ∧ F3.mul a d = F3.mul b c →
      ∃ i : Fin 12, prim12 i = ⟨a, b, c, d⟩ := by
  decide

theorem prim12_surj : ∀ m : Mat2 F3,
    IsPrimitiveIdempotent Mat2F3Ring m → ∃ i : Fin 12, prim12 i = m := by
  intro ⟨a, b, c, d⟩ hm
  exact prim12_cond_surj a b c d ((mat2_prim_idemp_iff F3DomainRing ⟨a, b, c, d⟩).mp hm)

theorem mat2_f3_prim_idemp_exactCard_twelve :
    ExactCard (IsPrimitiveIdempotent Mat2F3Ring) 12 :=
  ⟨prim12, prim12_isPrimitive, prim12_inj, prim12_surj⟩

def idemp14 : Fin 14 → Mat2 F3 := fun i =>
  if h : i.val < 12 then
    prim12 ⟨i.val, h⟩
  else if i.val = 12 then
    Mat2F3Ring.zero
  else
    Mat2F3Ring.one

theorem idemp14_surj :
    ∀ a b c d : F3,
      IsIdempotent Mat2F3Ring ⟨a, b, c, d⟩ →
      ∃ i : Fin 14, idemp14 i = ⟨a, b, c, d⟩ := by
  decide

theorem mat2_f3_idemp_exactCard_fourteen :
    ExactCard (IsIdempotent Mat2F3Ring) 14 :=
  ⟨idemp14, by decide, by decide, fun ⟨a, b, c, d⟩ hm => idemp14_surj a b c d hm⟩

def ordDecomp12 (k : Fin 12) : Fin 2 → Mat2 F3 := fun i =>
  match i with
  | ⟨0, _⟩ => prim12 k
  | ⟨1, _⟩ => Mat2F3Ring.sub Mat2F3Ring.one (prim12 k)

theorem ordDecomp12_comp_cond :
    ∀ k : Fin 12,
      F3Ring.add (Mat2F3Ring.sub Mat2F3Ring.one (prim12 k)).a
          (Mat2F3Ring.sub Mat2F3Ring.one (prim12 k)).d = F3Ring.one ∧
      F3Ring.mul (Mat2F3Ring.sub Mat2F3Ring.one (prim12 k)).a
          (Mat2F3Ring.sub Mat2F3Ring.one (prim12 k)).d =
      F3Ring.mul (Mat2F3Ring.sub Mat2F3Ring.one (prim12 k)).b
          (Mat2F3Ring.sub Mat2F3Ring.one (prim12 k)).c := by
  decide

theorem ordDecomp12_orth01 :
    ∀ k : Fin 12,
      AreOrthogonal Mat2F3Ring (prim12 k) (Mat2F3Ring.sub Mat2F3Ring.one (prim12 k)) := by
  decide

theorem ordDecomp12_sum :
    ∀ k : Fin 12, finSum Mat2F3Ring 2 (ordDecomp12 k) = Mat2F3Ring.one := by
  decide

theorem ordDecomp12_isPrimOrth (k : Fin 12) :
    IsPrimOrthDecomp Mat2F3Ring 2 (ordDecomp12 k) := by
  have hp0 : IsPrimitiveIdempotent Mat2F3Ring (prim12 k) := prim12_isPrimitive k
  have hp1 : IsPrimitiveIdempotent Mat2F3Ring (Mat2F3Ring.sub Mat2F3Ring.one (prim12 k)) :=
    (mat2_prim_idemp_iff F3DomainRing _).mpr (ordDecomp12_comp_cond k)
  have hprim : ∀ i : Fin 2, IsPrimitiveIdempotent Mat2F3Ring (ordDecomp12 k i) := by
    intro i
    match i with
    | ⟨0, _⟩ => exact hp0
    | ⟨1, _⟩ => exact hp1
    | ⟨n + 2, hn⟩ => omega
  have horth := ordDecomp12_orth01 k
  refine ⟨⟨fun i => (hprim i).1, ?_, ordDecomp12_sum k⟩, hprim⟩
  intro i j hne
  match i, j with
  | ⟨0, _⟩, ⟨0, _⟩ => exact absurd rfl hne
  | ⟨1, _⟩, ⟨1, _⟩ => exact absurd rfl hne
  | ⟨0, _⟩, ⟨1, _⟩ => exact horth
  | ⟨1, _⟩, ⟨0, _⟩ => exact ⟨horth.2, horth.1⟩
  | ⟨n + 2, hn⟩, _ => omega
  | _, ⟨n + 2, hn⟩ => omega

theorem ordDecomp12_surj (e : Fin 2 → Mat2 F3)
    (he : IsPrimOrthDecomp Mat2F3Ring 2 e) :
    ∃ k : Fin 12, ordDecomp12 k = e := by
  obtain ⟨k, hk⟩ := prim12_surj (e ⟨0, by decide⟩) (he.2 ⟨0, by decide⟩)
  refine ⟨k, ?_⟩
  have hsum : Mat2F3Ring.add (e ⟨0, by decide⟩) (e ⟨1, by decide⟩) = Mat2F3Ring.one := by
    have hs := he.1.2.2
    simp only [finSum] at hs
    rw [Mat2F3Ring.add_zero] at hs
    exact hs
  have he1 : e ⟨1, by decide⟩ = Mat2F3Ring.sub Mat2F3Ring.one (prim12 k) := by
    apply Mat2F3Ring.add_left_cancel (a := prim12 k)
    rw [Mat2F3Ring.add_sub_cancel_left, hk, hsum]
  funext i
  match i with
  | ⟨0, _⟩ => exact hk
  | ⟨1, _⟩ => exact he1.symm
  | ⟨n + 2, hn⟩ => omega

theorem mat2_f3_ordered_decomp_exactCard_twelve :
    ExactCard (IsPrimOrthDecomp Mat2F3Ring 2) 12 := by
  refine ⟨ordDecomp12, ordDecomp12_isPrimOrth, ?_, ordDecomp12_surj⟩
  intro i j hij
  have h0 : ordDecomp12 i ⟨0, by decide⟩ = ordDecomp12 j ⟨0, by decide⟩ :=
    congrFun hij ⟨0, by decide⟩
  exact prim12_inj i j h0

def unordDecomp6 (k : Fin 6) : Mat2 F3 → Prop :=
  fun x => x = prim12 ⟨2 * k.val, by omega⟩ ∨ x = prim12 ⟨2 * k.val + 1, by omega⟩

theorem prim12_even_comp :
    ∀ k : Fin 6,
      Mat2F3Ring.sub Mat2F3Ring.one (prim12 ⟨2 * k.val, by omega⟩) =
      prim12 ⟨2 * k.val + 1, by omega⟩ := by
  decide

theorem prim12_pair_cases :
    ∀ m : Fin 12,
      (prim12 ⟨2 * (m.val / 2), by omega⟩ = prim12 m ∧
       prim12 ⟨2 * (m.val / 2) + 1, by omega⟩ =
         Mat2F3Ring.sub Mat2F3Ring.one (prim12 m)) ∨
      (prim12 ⟨2 * (m.val / 2), by omega⟩ =
         Mat2F3Ring.sub Mat2F3Ring.one (prim12 m) ∧
       prim12 ⟨2 * (m.val / 2) + 1, by omega⟩ = prim12 m) := by
  decide

theorem mat2_f3_unordered_decomp_exactCard_six :
    ExactCard (IsUnordPrimOrthDecomp Mat2F3Ring) 6 := by
  refine ⟨unordDecomp6, ?_, ?_, ?_⟩
  · intro k
    let k2 : Fin 12 := ⟨2 * k.val, by omega⟩
    let k21 : Fin 12 := ⟨2 * k.val + 1, by omega⟩
    have hcomp : Mat2F3Ring.sub Mat2F3Ring.one (prim12 k2) = prim12 k21 :=
      prim12_even_comp k
    refine ⟨2, ordDecomp12 k2, ordDecomp12_isPrimOrth k2, ?_⟩
    funext x
    apply propext
    constructor
    · intro hx
      cases hx with
      | inl h0 => exact ⟨⟨0, by decide⟩, h0⟩
      | inr h1 =>
        refine ⟨⟨1, by decide⟩, ?_⟩
        dsimp [ordDecomp12]
        rw [hcomp]
        exact h1
    · intro ⟨i, hxi⟩
      match i with
      | ⟨0, _⟩ => exact Or.inl hxi
      | ⟨1, _⟩ =>
        dsimp [ordDecomp12] at hxi
        rw [hcomp] at hxi
        exact Or.inr hxi
      | ⟨n + 2, hn⟩ => omega
  · intro i j hij
    apply Classical.byContradiction
    intro hne
    have hmem : unordDecomp6 i (prim12 ⟨2 * i.val, by omega⟩) := Or.inl rfl
    rw [hij] at hmem
    cases hmem with
    | inl heq =>
      have hidx := prim12_inj _ _ heq
      have hv : 2 * i.val = 2 * j.val := congrArg Fin.val hidx
      exact hne (Fin.ext (by omega))
    | inr heq =>
      have hidx := prim12_inj _ _ heq
      have hv : 2 * i.val = 2 * j.val + 1 := congrArg Fin.val hidx
      omega
  · intro S ⟨r, e, he, hS⟩
    have hr : r = 2 := mat2_prim_decomp_length_eq_two F3DomainRing he
    subst hr
    obtain ⟨m, hm⟩ := ordDecomp12_surj e he
    let k : Fin 6 := ⟨m.val / 2, by omega⟩
    refine ⟨k, ?_⟩
    have hset : unordDecomp6 k = (fun x => ∃ i : Fin 2, x = ordDecomp12 m i) := by
      funext x
      apply propext
      have hpair := prim12_pair_cases m
      constructor
      · intro hx
        dsimp [unordDecomp6, k] at hx
        cases hpair with
        | inl hp =>
          cases hx with
          | inl h0 => rw [hp.1] at h0; exact ⟨⟨0, by decide⟩, h0⟩
          | inr h1 => rw [hp.2] at h1; exact ⟨⟨1, by decide⟩, h1⟩
        | inr hp =>
          cases hx with
          | inl h0 => rw [hp.1] at h0; exact ⟨⟨1, by decide⟩, h0⟩
          | inr h1 => rw [hp.2] at h1; exact ⟨⟨0, by decide⟩, h1⟩
      · intro ⟨i, hxi⟩
        dsimp [unordDecomp6, k]
        match i with
        | ⟨0, _⟩ =>
          dsimp [ordDecomp12] at hxi
          cases hpair with
          | inl hp => exact Or.inl (hxi.trans hp.1.symm)
          | inr hp => exact Or.inr (hxi.trans hp.2.symm)
        | ⟨1, _⟩ =>
          dsimp [ordDecomp12] at hxi
          cases hpair with
          | inl hp => exact Or.inr (hxi.trans hp.2.symm)
          | inr hp => exact Or.inl (hxi.trans hp.1.symm)
        | ⟨n + 2, hn⟩ => omega
    rw [hS, ← hm, hset]

/-- **Master Six-Way Separation Theorem on `M_2(F_3) ≅ Cl_{1,1}(F_3)`**:
    Simultaneously establishes the exact distinct invariants `(1, 2, 4, 6, 12, 14)`
    and proves that every interpretation of the idempotent decomposition count
    strictly disagrees with both minimal two-sided and minimal left ideal counts. -/
theorem mat2_f3_master_refutation :
    ExactCard (IsMinimalTwoSidedIdeal Mat2F3Ring) 1 ∧
    ExactCard (IsCentralPrimitiveIdempotent Mat2F3Ring) 1 ∧
    (∀ (r : Nat) (e : Fin r → Mat2 F3), IsPrimOrthDecomp Mat2F3Ring r e → r = 2) ∧
    ExactCard (IsMinimalLeftIdeal Mat2F3Ring) 4 ∧
    ExactCard (IsUnordPrimOrthDecomp Mat2F3Ring) 6 ∧
    ExactCard (IsPrimOrthDecomp Mat2F3Ring 2) 12 ∧
    ExactCard (IsPrimitiveIdempotent Mat2F3Ring) 12 ∧
    ExactCard (IsIdempotent Mat2F3Ring) 14 ∧
    ¬ (∃ k, ExactCard (IsUnordPrimOrthDecomp Mat2F3Ring) k ∧
            ExactCard (IsMinimalTwoSidedIdeal Mat2F3Ring) k) ∧
    ¬ (∃ k, ExactCard (IsUnordPrimOrthDecomp Mat2F3Ring) k ∧
            ExactCard (IsMinimalLeftIdeal Mat2F3Ring) k) ∧
    ¬ (∃ k, ExactCard (IsPrimOrthDecomp Mat2F3Ring 2) k ∧
            ExactCard (IsMinimalTwoSidedIdeal Mat2F3Ring) k) ∧
    ¬ (∃ k, ExactCard (IsPrimOrthDecomp Mat2F3Ring 2) k ∧
            ExactCard (IsMinimalLeftIdeal Mat2F3Ring) k) := by
  have h_two : ExactCard (IsMinimalTwoSidedIdeal Mat2F3Ring) 1 :=
    mat2_minimal_two_sided_exactCard_one F3FieldRing
  have h_cent : ExactCard (IsCentralPrimitiveIdempotent Mat2F3Ring) 1 :=
    mat2_central_prim_exactCard_one F3FieldRing
  have h_len : ∀ (r : Nat) (e : Fin r → Mat2 F3), IsPrimOrthDecomp Mat2F3Ring r e → r = 2 :=
    fun _ _ he => mat2_prim_decomp_length_eq_two F3DomainRing he
  have h_left := mat2_f3_minimal_left_exactCard_four
  have h_unord := mat2_f3_unordered_decomp_exactCard_six
  have h_ord := mat2_f3_ordered_decomp_exactCard_twelve
  have h_prim := mat2_f3_prim_idemp_exactCard_twelve
  have h_idem := mat2_f3_idemp_exactCard_fourteen
  exact ⟨h_two, h_cent, h_len, h_left, h_unord, h_ord, h_prim, h_idem,
    exactCard_disjoint_counts h_unord h_two (by decide),
    exactCard_disjoint_counts h_unord h_left (by decide),
    exactCard_disjoint_counts h_ord h_two (by decide),
    exactCard_disjoint_counts h_ord h_left (by decide)⟩

/-! ## 5. Infinite Primitive Idempotent Decompositions in `M_2(ℤ)` -/

def IntRing : UnitalRing Int where
  zero := 0
  one := 1
  add := (· + ·)
  neg := (- ·)
  mul := (· * ·)
  add_assoc := fun _ _ _ => by omega
  add_comm := fun _ _ => by omega
  zero_add := fun _ => by omega
  add_left_neg := fun _ => by omega
  mul_assoc := Int.mul_assoc
  one_mul := Int.one_mul
  mul_one := Int.mul_one
  left_distrib := Int.mul_add
  right_distrib := Int.add_mul
  one_ne_zero := by decide

def IntCommRing : CommUnitalRing Int :=
  { IntRing with mul_comm := Int.mul_comm }

theorem int_eq_zero_or_eq_zero_of_mul_eq_zero (a b : Int) (h : a * b = 0) :
    a = 0 ∨ b = 0 := by
  cases a with
  | ofNat m =>
    cases m with
    | zero => exact Or.inl rfl
    | succ m' =>
      cases b with
      | ofNat n =>
        cases n with
        | zero => exact Or.inr rfl
        | succ n' =>
          change Int.ofNat ((m' + 1) * (n' + 1)) = Int.ofNat 0 at h
          have hnat : (m' + 1) * (n' + 1) = 0 := Int.ofNat.inj h
          have hpos : 0 < (m' + 1) * (n' + 1) := Nat.mul_pos (Nat.succ_pos m') (Nat.succ_pos n')
          omega
      | negSucc n =>
        change Int.negSucc ((m' + 1) * (n + 1) - 1) = Int.ofNat 0 at h
        exact absurd h (by intro hh; injection hh)
  | negSucc m =>
    cases b with
    | ofNat n =>
      cases n with
      | zero => exact Or.inr rfl
      | succ n' =>
        change Int.negSucc ((m + 1) * (n' + 1) - 1) = Int.ofNat 0 at h
        exact absurd h (by intro hh; injection hh)
    | negSucc n =>
      change Int.ofNat ((m + 1) * (n + 1)) = Int.ofNat 0 at h
      have hnat : (m + 1) * (n + 1) = 0 := Int.ofNat.inj h
      have hpos : 0 < (m + 1) * (n + 1) := Nat.mul_pos (Nat.succ_pos m) (Nat.succ_pos n)
      omega

def IntDomainRing : DomainRing Int :=
  { IntCommRing with
    eq_zero_or_eq_zero_of_mul_eq_zero := int_eq_zero_or_eq_zero_of_mul_eq_zero }

abbrev Mat2IntRing : UnitalRing (Mat2 Int) := Mat2Ring IntRing

def upperProj (t : Int) : Fin 2 → Mat2 Int
  | ⟨0, _⟩ => ⟨1, t, 0, 0⟩
  | ⟨1, _⟩ => ⟨0, -t, 0, 1⟩

theorem upperProj_isPrimOrthDecomp (t : Int) :
    IsPrimOrthDecomp Mat2IntRing 2 (upperProj t) := by
  have hp0 : IsPrimitiveIdempotent Mat2IntRing ⟨1, t, 0, 0⟩ := by
    apply (mat2_prim_idemp_iff IntDomainRing ⟨1, t, 0, 0⟩).mpr
    exact ⟨by change (1 : Int) + 0 = 1; omega,
           by change (1 : Int) * 0 = t * 0; rw [Int.mul_zero, Int.mul_zero]⟩
  have hp1 : IsPrimitiveIdempotent Mat2IntRing ⟨0, -t, 0, 1⟩ := by
    apply (mat2_prim_idemp_iff IntDomainRing ⟨0, -t, 0, 1⟩).mpr
    exact ⟨by change (0 : Int) + 1 = 1; omega,
           by change (0 : Int) * 1 = (-t) * 0; rw [Int.zero_mul, Int.mul_zero]⟩
  have hprim : ∀ i : Fin 2, IsPrimitiveIdempotent Mat2IntRing (upperProj t i) := by
    intro i
    match i with
    | ⟨0, _⟩ => exact hp0
    | ⟨1, _⟩ => exact hp1
    | ⟨n + 2, hn⟩ => omega
  have horth : AreOrthogonal Mat2IntRing ⟨1, t, 0, 0⟩ ⟨0, -t, 0, 1⟩ := by
    constructor
    · exact Mat2.ext
        (by change 1 * 0 + t * 0 = (0 : Int); rw [Int.mul_zero, Int.mul_zero]; omega)
        (by change 1 * (-t) + t * 1 = (0 : Int); rw [Int.one_mul, Int.mul_one]; omega)
        rfl
        (by change 0 * (-t) + 0 * 1 = (0 : Int); rw [Int.zero_mul]; rfl)
    · exact Mat2.ext
        (by change 0 * 1 + (-t) * 0 = (0 : Int); rw [Int.zero_mul, Int.mul_zero]; omega)
        (by change 0 * t + (-t) * 0 = (0 : Int); rw [Int.zero_mul, Int.mul_zero]; omega)
        rfl
        (by change 0 * t + 1 * 0 = (0 : Int); rw [Int.zero_mul]; rfl)
  refine ⟨⟨fun i => (hprim i).1, ?_, ?_⟩, hprim⟩
  · intro i j hne
    match i, j with
    | ⟨0, _⟩, ⟨0, _⟩ => exact absurd rfl hne
    | ⟨1, _⟩, ⟨1, _⟩ => exact absurd rfl hne
    | ⟨0, _⟩, ⟨1, _⟩ => exact horth
    | ⟨1, _⟩, ⟨0, _⟩ => exact ⟨horth.2, horth.1⟩
    | ⟨n + 2, hn⟩, _ => omega
    | _, ⟨n + 2, hn⟩ => omega
  · simp only [finSum]
    rw [Mat2IntRing.add_zero]
    exact Mat2.ext rfl
      (by change t + (-t) = (0 : Int); omega)
      rfl rfl

theorem upperProj_unord_inj (t s : Int)
    (heq : (fun x => ∃ i : Fin 2, x = upperProj t i) =
           (fun x => ∃ i : Fin 2, x = upperProj s i)) : t = s := by
  have hmem : ∃ i : Fin 2, (⟨1, t, 0, 0⟩ : Mat2 Int) = upperProj s i := by
    have hiff := congrFun heq ⟨1, t, 0, 0⟩
    exact Eq.mp hiff ⟨⟨0, by decide⟩, rfl⟩
  obtain ⟨i, hi⟩ := hmem
  match i with
  | ⟨0, _⟩ =>
    dsimp [upperProj] at hi
    exact congrArg Mat2.b hi
  | ⟨1, _⟩ =>
    dsimp [upperProj] at hi
    have h10 : (1 : Int) = 0 := congrArg Mat2.a hi
    exact absurd h10 (by decide)
  | ⟨n + 2, hn⟩ => omega

/-- **Infinite Decomposition Theorem**: `M_2(ℤ)` admits no finite count `k` of
    unordered primitive orthogonal idempotent decompositions of `I_2`. -/
theorem mat2_int_infinite_unord_prim_decomps (k : Nat) :
    ¬ ExactCard (IsUnordPrimOrthDecomp Mat2IntRing) k := by
  intro hk
  let fam : Fin (k + 1) → (Mat2 Int → Prop) :=
    fun j => (fun x => ∃ i : Fin 2, x = upperProj (Int.ofNat j.val) i)
  have hfam_card : ExactCard (fun S => ∃ j : Fin (k + 1), fam j = S) (k + 1) := by
    refine ⟨fam, fun j => ⟨j, rfl⟩, ?_, fun S hS => hS⟩
    intro j₁ j₂ hj
    have hts : Int.ofNat j₁.val = Int.ofNat j₂.val := upperProj_unord_inj _ _ hj
    exact Fin.ext (Int.ofNat.inj hts)
  have hsub : ∀ S, (∃ j : Fin (k + 1), fam j = S) → IsUnordPrimOrthDecomp Mat2IntRing S := by
    intro S ⟨j, hj⟩
    subst hj
    exact ⟨2, upperProj (Int.ofNat j.val), upperProj_isPrimOrthDecomp _, rfl⟩
  have hle : k + 1 ≤ k := exactCard_le_of_subset hfam_card hk hsub
  omega

end Conjecture00000007625
