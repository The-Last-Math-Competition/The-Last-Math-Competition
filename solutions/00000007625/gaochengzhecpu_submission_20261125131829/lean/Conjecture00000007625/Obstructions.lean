/-
  Conjecture 00000007625 — Division-Algebra & Non-Semisimple Obstructions

  Proves:
  1. Division-Algebra Obstruction A (`Cl_{0,1}(F_3) ≅ F_9`):
       - `Cl01F3Ring = GaussRing F3CommRing` is a simple ring with unique
         minimal two-sided ideal, unique minimal left ideal, and 2 idempotents.
       - `cl01_f3_not_iso_any_matN_f3`: for EVERY `n ≥ 1`, there is NO ring
         isomorphism between `Cl_{0,1}(F_3)` and `M_n(F_3)`.
  2. Division-Algebra Obstruction B (`Cl_{0,2}(ℤ) = H(ℤ)` and `Cl_{0,2}(K)`):
       - Built via Cayley-Dickson doubling `Quat α` over any `CommUnitalRing α`.
       - `QuatIntRing` satisfies `i^2 = j^2 = -1`, `i j + j i = 0`, `i j ≠ j i`,
         has no nonzero zero divisors, and `quatInt_not_iso_any_matN_int` proves
         it is NOT ring-isomorphic to `M_n(ℤ)` for ANY `n ≥ 1`.
       - Over any formally real field `K` (such as `ℚ` or `ℝ`), `QuatRing K` is
         a simple division ring with `m_two = m_left = 1` that is NOT
         ring-isomorphic to `M_n(K)` for ANY `n ≥ 1`.
  3. Non-Semisimple / Degenerate Clifford Obstructions:
       - `DualF3Ring = F_3[ε]/(ε^2) = Λ(F_3^1)`: unique minimal ideal `F_3 ε` is
         square-zero (`I^2 = 0`), contains zero nonzero idempotents, and `DualF3`
         is not ring-isomorphic to `M_n(F_3)` for any `n ≥ 1` (refutes Clauses 2 & 3).
       - `LocalF3Ring = F_3[x, y]/(x^2, xy, y^2)`: commutative local algebra
         where every idempotent is central (`0` and `1` only, decomposition
         length and count equal `1`), YET `ExactCard IsMinimalTwoSidedIdeal 4`
         (4 square-zero minimal ideals, refuting Clauses 1, 2, and 3 even for
         commutative rings and central idempotents).
-/

import Conjecture00000007625.Basic
import Conjecture00000007625.Positive
import Conjecture00000007625.MatrixCounterexample

namespace Conjecture00000007625

/-! ## 1. Reusable Subtraction Rearrangement Lemmas & Cayley-Dickson Construction -/

section SubRearrange

variable {α : Type u} (R : UnitalRing α)

theorem sub_four_swap (p q r s : α) :
    R.sub (R.sub p q) (R.add r s) = R.sub (R.sub p r) (R.add q s) := by
  unfold UnitalRing.sub
  rw [R.neg_add, R.neg_add]
  exact add_four_swap R p (R.neg q) (R.neg r) (R.neg s)

theorem sub_add_add_rearrange (p q r s : α) :
    R.add (R.sub p q) (R.add r s) = R.add (R.add p r) (R.sub s q) := by
  unfold UnitalRing.sub
  calc
    R.add (R.add p (R.neg q)) (R.add r s)
      = R.add (R.add p r) (R.add (R.neg q) s) := add_four_swap R p (R.neg q) r s
    _ = R.add (R.add p r) (R.add s (R.neg q)) := by rw [R.add_comm (R.neg q) s]

theorem sub_add_sub_swap (p q r s : α) :
    R.add (R.sub p q) (R.sub r s) = R.sub (R.add p r) (R.add q s) := by
  unfold UnitalRing.sub
  rw [R.neg_add]
  exact add_four_swap R p (R.neg q) r (R.neg s)

end SubRearrange

/-- Quadratic extension `α[i]/(i^2 + 1) = Cl_{0,1}(α)` over any commutative ring. -/
structure Gauss (α : Type u) where
  re : α
  im : α
  deriving DecidableEq, Repr

theorem Gauss.ext {α : Type u} {x y : Gauss α}
    (hre : x.re = y.re) (him : x.im = y.im) : x = y := by
  cases x; cases y; dsimp at hre him; subst hre him; rfl

def GaussRing {α : Type u} (C : CommUnitalRing α) : UnitalRing (Gauss α) :=
  let R := C.toUnitalRing
  { zero := ⟨R.zero, R.zero⟩
    one := ⟨R.one, R.zero⟩
    add := fun x y => ⟨R.add x.re y.re, R.add x.im y.im⟩
    neg := fun x => ⟨R.neg x.re, R.neg x.im⟩
    mul := fun x y =>
      ⟨R.sub (R.mul x.re y.re) (R.mul x.im y.im),
       R.add (R.mul x.re y.im) (R.mul x.im y.re)⟩
    add_assoc := fun x y z => by
      cases x; cases y; cases z; simp [R.add_assoc]
    add_comm := fun x y => by
      cases x; cases y; simp [R.add_comm]
    zero_add := fun x => by
      cases x; simp [R.zero_add]
    add_left_neg := fun x => by
      cases x; simp [R.add_left_neg]
    mul_assoc := fun x y z => by
      dsimp
      have hre :
          R.sub (R.mul (R.sub (R.mul x.re y.re) (R.mul x.im y.im)) z.re)
                (R.mul (R.add (R.mul x.re y.im) (R.mul x.im y.re)) z.im) =
          R.sub (R.mul x.re (R.sub (R.mul y.re z.re) (R.mul y.im z.im)))
                (R.mul x.im (R.add (R.mul y.re z.im) (R.mul y.im z.re))) := by
        rw [R.sub_mul, R.right_distrib, sub_four_swap R]
        rw [R.mul_assoc, R.mul_assoc, R.mul_assoc, R.mul_assoc]
        rw [← R.mul_sub, ← R.left_distrib, R.add_comm (R.mul y.im z.re) (R.mul y.re z.im)]
      have him :
          R.add (R.mul (R.sub (R.mul x.re y.re) (R.mul x.im y.im)) z.im)
                (R.mul (R.add (R.mul x.re y.im) (R.mul x.im y.re)) z.re) =
          R.add (R.mul x.re (R.add (R.mul y.re z.im) (R.mul y.im z.re)))
                (R.mul x.im (R.sub (R.mul y.re z.re) (R.mul y.im z.im))) := by
        rw [R.sub_mul, R.right_distrib, sub_add_add_rearrange R]
        rw [R.mul_assoc, R.mul_assoc, R.mul_assoc, R.mul_assoc]
        rw [← R.left_distrib, ← R.mul_sub]
      exact Gauss.ext hre him
    one_mul := fun ⟨a, b⟩ => by
      dsimp [UnitalRing.sub]
      simp [R.one_mul, R.zero_mul, R.neg_zero, R.add_zero, R.zero_add]
    mul_one := fun ⟨a, b⟩ => by
      dsimp [UnitalRing.sub]
      simp [R.mul_one, R.mul_zero, R.neg_zero, R.add_zero, R.zero_add]
    left_distrib := fun x y z => by
      dsimp
      have hre :
          R.sub (R.mul x.re (R.add y.re z.re)) (R.mul x.im (R.add y.im z.im)) =
          R.add (R.sub (R.mul x.re y.re) (R.mul x.im y.im))
                (R.sub (R.mul x.re z.re) (R.mul x.im z.im)) := by
        rw [R.left_distrib, R.left_distrib, ← sub_add_sub_swap R]
      have him :
          R.add (R.mul x.re (R.add y.im z.im)) (R.mul x.im (R.add y.re z.re)) =
          R.add (R.add (R.mul x.re y.im) (R.mul x.im y.re))
                (R.add (R.mul x.re z.im) (R.mul x.im z.re)) := by
        rw [R.left_distrib, R.left_distrib]
        exact add_four_swap R _ _ _ _
      exact Gauss.ext hre him
    right_distrib := fun x y z => by
      dsimp
      have hre :
          R.sub (R.mul (R.add x.re y.re) z.re) (R.mul (R.add x.im y.im) z.im) =
          R.add (R.sub (R.mul x.re z.re) (R.mul x.im z.im))
                (R.sub (R.mul y.re z.re) (R.mul y.im z.im)) := by
        rw [R.right_distrib, R.right_distrib, ← sub_add_sub_swap R]
      have him :
          R.add (R.mul (R.add x.re y.re) z.im) (R.mul (R.add x.im y.im) z.re) =
          R.add (R.add (R.mul x.re z.im) (R.mul x.im z.re))
                (R.add (R.mul y.re z.im) (R.mul y.im z.re)) := by
        rw [R.right_distrib, R.right_distrib]
        exact add_four_swap R _ _ _ _
      exact Gauss.ext hre him
    one_ne_zero := fun h => R.one_ne_zero (congrArg Gauss.re h) }

def GaussCommRing {α : Type u} (C : CommUnitalRing α) : CommUnitalRing (Gauss α) :=
  let R := C.toUnitalRing
  { GaussRing C with
    mul_comm := fun x y => by
      dsimp [GaussRing]
      exact Gauss.ext
        (by rw [C.mul_comm x.re y.re, C.mul_comm x.im y.im])
        (by rw [C.mul_comm x.re y.im, C.mul_comm x.im y.re, R.add_comm]) }

def gaussConj {α : Type u} (C : CommUnitalRing α) (z : Gauss α) : Gauss α :=
  ⟨z.re, C.neg z.im⟩

theorem gaussConj_zero {α : Type u} (C : CommUnitalRing α) :
    gaussConj C (GaussRing C).zero = (GaussRing C).zero :=
  Gauss.ext rfl C.toUnitalRing.neg_zero

theorem gaussConj_one {α : Type u} (C : CommUnitalRing α) :
    gaussConj C (GaussRing C).one = (GaussRing C).one :=
  Gauss.ext rfl C.toUnitalRing.neg_zero

theorem gaussConj_conj {α : Type u} (C : CommUnitalRing α) (z : Gauss α) :
    gaussConj C (gaussConj C z) = z :=
  Gauss.ext rfl (C.toUnitalRing.neg_neg _)

theorem gaussConj_add {α : Type u} (C : CommUnitalRing α) (x y : Gauss α) :
    gaussConj C ((GaussRing C).add x y) = (GaussRing C).add (gaussConj C x) (gaussConj C y) :=
  Gauss.ext rfl (C.toUnitalRing.neg_add x.im y.im)

theorem gaussConj_neg {α : Type u} (C : CommUnitalRing α) (x : Gauss α) :
    gaussConj C ((GaussRing C).neg x) = (GaussRing C).neg (gaussConj C x) := rfl

theorem gaussConj_sub {α : Type u} (C : CommUnitalRing α) (x y : Gauss α) :
    gaussConj C ((GaussRing C).sub x y) = (GaussRing C).sub (gaussConj C x) (gaussConj C y) := by
  unfold UnitalRing.sub
  rw [gaussConj_add, gaussConj_neg]

theorem gaussConj_mul {α : Type u} (C : CommUnitalRing α) (x y : Gauss α) :
    gaussConj C ((GaussRing C).mul x y) = (GaussRing C).mul (gaussConj C x) (gaussConj C y) := by
  let R := C.toUnitalRing
  dsimp [gaussConj, GaussRing, UnitalRing.sub]
  have hre : R.mul (R.neg x.im) (R.neg y.im) = R.mul x.im y.im := by
    rw [R.neg_mul, R.mul_neg, R.neg_neg]
  have him : R.neg (R.add (R.mul x.re y.im) (R.mul x.im y.re)) =
             R.add (R.mul x.re (R.neg y.im)) (R.mul (R.neg x.im) y.re) := by
    rw [R.neg_add, R.mul_neg, R.neg_mul]
  rw [hre, him]

theorem gauss_mul_conj {α : Type u} (C : CommUnitalRing α) (z : Gauss α) :
    (GaussRing C).mul z (gaussConj C z) =
    ⟨C.add (C.mul z.re z.re) (C.mul z.im z.im), C.zero⟩ := by
  let R := C.toUnitalRing
  dsimp [GaussRing, gaussConj, UnitalRing.sub]
  have h1 : R.neg (R.mul z.im (R.neg z.im)) = R.mul z.im z.im := by
    rw [R.mul_neg, R.neg_neg]
  have h2 : R.add (R.mul z.re (R.neg z.im)) (R.mul z.im z.re) = R.zero := by
    rw [R.mul_neg, C.mul_comm z.im z.re, R.add_left_neg]
  exact Gauss.ext (congrArg (C.add (C.mul z.re z.re)) h1) h2

/-- Quaternion algebra `Quat α = Cl_{0,2}(α)` via Cayley-Dickson doubling. -/
structure Quat (α : Type u) where
  z : Gauss α
  w : Gauss α
  deriving DecidableEq, Repr

theorem Quat.ext {α : Type u} {x y : Quat α}
    (hz : x.z = y.z) (hw : x.w = y.w) : x = y := by
  cases x; cases y; dsimp at hz hw; subst hz hw; rfl

def QuatRing {α : Type u} (C : CommUnitalRing α) : UnitalRing (Quat α) :=
  let G := GaussRing C
  let gcomm : ∀ x y : Gauss α, G.mul x y = G.mul y x := (GaussCommRing C).mul_comm
  let conj := gaussConj C
  { zero := ⟨G.zero, G.zero⟩
    one := ⟨G.one, G.zero⟩
    add := fun q1 q2 => ⟨G.add q1.z q2.z, G.add q1.w q2.w⟩
    neg := fun q => ⟨G.neg q.z, G.neg q.w⟩
    mul := fun q1 q2 =>
      ⟨G.sub (G.mul q1.z q2.z) (G.mul (conj q2.w) q1.w),
       G.add (G.mul q2.w q1.z) (G.mul q1.w (conj q2.z))⟩
    add_assoc := fun a b c =>
      Quat.ext (G.add_assoc a.z b.z c.z) (G.add_assoc a.w b.w c.w)
    add_comm := fun a b =>
      Quat.ext (G.add_comm a.z b.z) (G.add_comm a.w b.w)
    zero_add := fun a =>
      Quat.ext (G.zero_add a.z) (G.zero_add a.w)
    add_left_neg := fun a =>
      Quat.ext (G.add_left_neg a.z) (G.add_left_neg a.w)
    mul_assoc := fun q1 q2 q3 => by
      dsimp
      have hz :
          G.sub (G.mul (G.sub (G.mul q1.z q2.z) (G.mul (conj q2.w) q1.w)) q3.z)
                (G.mul (conj q3.w) (G.add (G.mul q2.w q1.z) (G.mul q1.w (conj q2.z)))) =
          G.sub (G.mul q1.z (G.sub (G.mul q2.z q3.z) (G.mul (conj q3.w) q2.w)))
                (G.mul (conj (G.add (G.mul q3.w q2.z) (G.mul q2.w (conj q3.z)))) q1.w) := by
        have hconj : conj (G.add (G.mul q3.w q2.z) (G.mul q2.w (conj q3.z))) =
            G.add (G.mul (conj q3.w) (conj q2.z)) (G.mul (conj q2.w) q3.z) := by
          dsimp [conj, G]
          rw [gaussConj_add, gaussConj_mul, gaussConj_mul, gaussConj_conj]
        rw [hconj, G.sub_mul, G.left_distrib, G.mul_sub, G.right_distrib]
        rw [sub_four_swap G]
        have t1 : G.mul (G.mul q1.z q2.z) q3.z = G.mul q1.z (G.mul q2.z q3.z) :=
          G.mul_assoc _ _ _
        have t2 : G.mul (conj q3.w) (G.mul q2.w q1.z) = G.mul q1.z (G.mul (conj q3.w) q2.w) := by
          rw [← G.mul_assoc, gcomm _ q1.z]
        have t3 : G.mul (G.mul (conj q2.w) q1.w) q3.z = G.mul (G.mul (conj q2.w) q3.z) q1.w := by
          rw [G.mul_assoc, gcomm q1.w q3.z, ← G.mul_assoc]
        have t4 : G.mul (conj q3.w) (G.mul q1.w (conj q2.z)) =
                  G.mul (G.mul (conj q3.w) (conj q2.z)) q1.w := by
          rw [gcomm q1.w (conj q2.z), G.mul_assoc]
        rw [t1, t2, t3, t4, G.add_comm (G.mul (G.mul (conj q2.w) q3.z) q1.w)]
      have hw :
          G.add (G.mul q3.w (G.sub (G.mul q1.z q2.z) (G.mul (conj q2.w) q1.w)))
                (G.mul (G.add (G.mul q2.w q1.z) (G.mul q1.w (conj q2.z))) (conj q3.z)) =
          G.add (G.mul (G.add (G.mul q3.w q2.z) (G.mul q2.w (conj q3.z))) q1.z)
                (G.mul q1.w (conj (G.sub (G.mul q2.z q3.z) (G.mul (conj q3.w) q2.w)))) := by
        have hconj : conj (G.sub (G.mul q2.z q3.z) (G.mul (conj q3.w) q2.w)) =
            G.sub (G.mul (conj q2.z) (conj q3.z)) (G.mul q3.w (conj q2.w)) := by
          dsimp [conj, G]
          rw [gaussConj_sub, gaussConj_mul, gaussConj_mul, gaussConj_conj]
        rw [hconj, G.mul_sub, G.right_distrib, G.right_distrib, G.mul_sub]
        rw [sub_add_add_rearrange G]
        have s1 : G.mul q3.w (G.mul q1.z q2.z) = G.mul (G.mul q3.w q2.z) q1.z := by
          rw [gcomm q1.z q2.z, G.mul_assoc]
        have s2 : G.mul (G.mul q2.w q1.z) (conj q3.z) = G.mul (G.mul q2.w (conj q3.z)) q1.z := by
          rw [G.mul_assoc, gcomm q1.z (conj q3.z), ← G.mul_assoc]
        have s3 : G.mul (G.mul q1.w (conj q2.z)) (conj q3.z) =
                  G.mul q1.w (G.mul (conj q2.z) (conj q3.z)) :=
          G.mul_assoc _ _ _
        have s4 : G.mul q3.w (G.mul (conj q2.w) q1.w) =
                  G.mul q1.w (G.mul q3.w (conj q2.w)) := by
          rw [← G.mul_assoc, gcomm _ q1.w]
        rw [s1, s2, s3, s4]
      exact Quat.ext hz hw
    one_mul := fun ⟨z, w⟩ => by
      dsimp [conj, G, UnitalRing.sub]
      exact Quat.ext
        (by rw [(GaussRing C).one_mul, (GaussRing C).mul_zero,
                (GaussRing C).neg_zero, (GaussRing C).add_zero])
        (by rw [(GaussRing C).mul_one, (GaussRing C).zero_mul,
                (GaussRing C).add_zero])
    mul_one := fun ⟨z, w⟩ => by
      dsimp [conj, G, UnitalRing.sub]
      apply Quat.ext <;> dsimp
      · rw [gaussConj_zero C, (GaussRing C).mul_one, (GaussRing C).zero_mul,
            (GaussRing C).neg_zero, (GaussRing C).add_zero]
      · rw [gaussConj_one C, (GaussRing C).zero_mul, (GaussRing C).mul_one,
            (GaussRing C).zero_add]
    left_distrib := fun q1 q2 q3 => by
      dsimp
      have hz :
          G.sub (G.mul q1.z (G.add q2.z q3.z)) (G.mul (conj (G.add q2.w q3.w)) q1.w) =
          G.add (G.sub (G.mul q1.z q2.z) (G.mul (conj q2.w) q1.w))
                (G.sub (G.mul q1.z q3.z) (G.mul (conj q3.w) q1.w)) := by
        dsimp [conj, G]
        rw [gaussConj_add, G.left_distrib, G.right_distrib, ← sub_add_sub_swap G]
      have hw :
          G.add (G.mul (G.add q2.w q3.w) q1.z) (G.mul q1.w (conj (G.add q2.z q3.z))) =
          G.add (G.add (G.mul q2.w q1.z) (G.mul q1.w (conj q2.z)))
                (G.add (G.mul q3.w q1.z) (G.mul q1.w (conj q3.z))) := by
        dsimp [conj, G]
        rw [gaussConj_add, G.right_distrib, G.left_distrib]
        exact add_four_swap G _ _ _ _
      exact Quat.ext hz hw
    right_distrib := fun q1 q2 q3 => by
      dsimp
      have hz :
          G.sub (G.mul (G.add q1.z q2.z) q3.z) (G.mul (conj q3.w) (G.add q1.w q2.w)) =
          G.add (G.sub (G.mul q1.z q3.z) (G.mul (conj q3.w) q1.w))
                (G.sub (G.mul q2.z q3.z) (G.mul (conj q3.w) q2.w)) := by
        rw [G.right_distrib, G.left_distrib, ← sub_add_sub_swap G]
      have hw :
          G.add (G.mul q3.w (G.add q1.z q2.z)) (G.mul (G.add q1.w q2.w) (conj q3.z)) =
          G.add (G.add (G.mul q3.w q1.z) (G.mul q1.w (conj q3.z)))
                (G.add (G.mul q3.w q2.z) (G.mul q2.w (conj q3.z))) := by
        rw [G.left_distrib, G.right_distrib]
        exact add_four_swap G _ _ _ _
      exact Quat.ext hz hw
    one_ne_zero := fun h => G.one_ne_zero (congrArg Quat.z h) }

def quatConj {α : Type u} (C : CommUnitalRing α) (q : Quat α) : Quat α :=
  ⟨gaussConj C q.z, (GaussRing C).neg q.w⟩

def quatNormSq {α : Type u} (C : CommUnitalRing α) (q : Quat α) : α :=
  C.add (C.add (C.mul q.z.re q.z.re) (C.mul q.z.im q.z.im))
        (C.add (C.mul q.w.re q.w.re) (C.mul q.w.im q.w.im))

theorem quat_conj_mul_self {α : Type u} (C : CommUnitalRing α) (q : Quat α) :
    (QuatRing C).mul (quatConj C q) q =
    ⟨⟨quatNormSq C q, C.zero⟩, ⟨C.zero, C.zero⟩⟩ := by
  let G := GaussRing C
  let gcomm : ∀ x y : Gauss α, G.mul x y = G.mul y x := (GaussCommRing C).mul_comm
  dsimp [QuatRing, quatConj, UnitalRing.sub]
  have hz : G.add (G.mul (gaussConj C q.z) q.z)
              (G.neg (G.mul (gaussConj C q.w) (G.neg q.w))) =
            ⟨quatNormSq C q, C.zero⟩ := by
    rw [G.mul_neg, G.neg_neg, gcomm (gaussConj C q.z) q.z,
        gcomm (gaussConj C q.w) q.w]
    dsimp [G]
    rw [gauss_mul_conj C q.z, gauss_mul_conj C q.w]
    dsimp [GaussRing, quatNormSq]
    rw [C.toUnitalRing.add_zero]
  have hw : G.add (G.mul q.w (gaussConj C q.z))
              (G.mul (G.neg q.w) (gaussConj C q.z)) = G.zero := by
    rw [G.neg_mul, G.add_right_neg]
  exact Quat.ext hz hw

theorem quat_mul_conj_self {α : Type u} (C : CommUnitalRing α) (q : Quat α) :
    (QuatRing C).mul q (quatConj C q) =
    ⟨⟨quatNormSq C q, C.zero⟩, ⟨C.zero, C.zero⟩⟩ := by
  let G := GaussRing C
  let gcomm : ∀ x y : Gauss α, G.mul x y = G.mul y x := (GaussCommRing C).mul_comm
  dsimp [QuatRing, quatConj, UnitalRing.sub]
  have hz : G.add (G.mul q.z (gaussConj C q.z))
              (G.neg (G.mul (gaussConj C (G.neg q.w)) q.w)) =
            ⟨quatNormSq C q, C.zero⟩ := by
    dsimp [G]
    rw [gaussConj_neg]
    change G.add (G.mul q.z (gaussConj C q.z))
             (G.neg (G.mul (G.neg (gaussConj C q.w)) q.w)) = _
    rw [G.neg_mul, G.neg_neg, gcomm (gaussConj C q.w) q.w]
    dsimp [G]
    rw [gauss_mul_conj C q.z, gauss_mul_conj C q.w]
    dsimp [GaussRing, quatNormSq]
    rw [C.toUnitalRing.add_zero]
  have hw : G.add (G.mul (G.neg q.w) q.z)
              (G.mul q.w (gaussConj C (gaussConj C q.z))) = G.zero := by
    rw [gaussConj_conj, G.neg_mul, G.add_left_neg]
  exact Quat.ext hz hw

def quatScalar {α : Type u} (C : CommUnitalRing α) (s : α) : Quat α :=
  ⟨⟨s, C.zero⟩, ⟨C.zero, C.zero⟩⟩

theorem quatScalar_mul_helper {α : Type u} (R : UnitalRing α)
    (hcomm : ∀ u v : α, R.mul u v = R.mul v u) (s : α) (q : Quat α) :
    let C : CommUnitalRing α := { R with mul_comm := hcomm }
    (QuatRing C).mul (quatScalar C s) q =
    ⟨⟨R.mul s q.z.re, R.mul s q.z.im⟩, ⟨R.mul s q.w.re, R.mul s q.w.im⟩⟩ := by
  dsimp [QuatRing, quatScalar, gaussConj, GaussRing, UnitalRing.sub]
  exact Quat.ext
    (Gauss.ext
      (by simp [R.mul_zero, R.zero_mul, R.neg_zero, R.add_zero, R.zero_add])
      (by simp [R.mul_zero, R.zero_mul, R.neg_zero, R.add_zero, R.zero_add]))
    (Gauss.ext
      (by simp [R.mul_zero, R.zero_mul, R.neg_zero, R.add_zero, R.zero_add, hcomm _ s])
      (by simp [R.mul_zero, R.zero_mul, R.neg_zero, R.add_zero, R.zero_add, hcomm _ s]))

theorem quatScalar_mul {α : Type u} (C : CommUnitalRing α) (s : α) (q : Quat α) :
    (QuatRing C).mul (quatScalar C s) q =
    ⟨⟨C.mul s q.z.re, C.mul s q.z.im⟩, ⟨C.mul s q.w.re, C.mul s q.w.im⟩⟩ :=
  quatScalar_mul_helper C.toUnitalRing C.mul_comm s q

/-! ## 2. Division-Algebra Obstruction A: `Cl_{0,1}(F_3) ≅ F_9` -/

abbrev Cl01F3 : Type := Gauss F3
abbrev Cl01F3Ring : UnitalRing Cl01F3 := GaussRing F3CommRing
abbrev Cl01F3CommRing : CommUnitalRing Cl01F3 := GaussCommRing F3CommRing

def cl01F3Inv (z : Cl01F3) : Cl01F3 :=
  let n := F3.inv (F3.add (F3.mul z.re z.re) (F3.mul z.im z.im))
  ⟨F3.mul z.re n, F3.mul (F3.neg z.im) n⟩

def Cl01F3FieldRing : FieldRing Cl01F3 :=
  { Cl01F3CommRing with
    inv := cl01F3Inv
    mul_inv_cancel := fun ⟨a, b⟩ hne => by
      cases a <;> cases b <;> first | exact absurd rfl hne | rfl }

theorem field_isSimpleRing {α : Type u} (K : FieldRing α) :
    IsSimpleRing K.toUnitalRing := by
  let R := K.toUnitalRing
  intro I hI ⟨x, hxI, hxne⟩ y
  have h1 : I R.one := by
    have hm : R.mul (K.inv x) x = R.one := by
      rw [K.mul_comm, K.mul_inv_cancel x hxne]
    rw [← hm]
    exact hI.1.2 (K.inv x) x hxI
  have hy : R.mul y R.one = y := R.mul_one y
  rw [← hy]
  exact hI.1.2 y R.one h1

theorem cl01_f3_simple_and_idempotents :
    ExactCard (IsMinimalTwoSidedIdeal Cl01F3Ring) 1 ∧
    ExactCard (IsMinimalLeftIdeal Cl01F3Ring) 1 ∧
    ExactCard (IsIdempotent Cl01F3Ring) 2 := by
  have htwo := simpleRing_exactCard_minimal_two_sided_one Cl01F3Ring
    (field_isSimpleRing Cl01F3FieldRing)
  have hleft : ExactCard (IsMinimalLeftIdeal Cl01F3Ring) 1 := by
    obtain ⟨f, hf1, hf2, hf3⟩ := htwo
    exact ⟨f,
      fun i => (comm_minLeft_iff_minTwoSided Cl01F3Ring Cl01F3CommRing.mul_comm (f i)).mpr (hf1 i),
      hf2,
      fun L hL => hf3 L ((comm_minLeft_iff_minTwoSided Cl01F3Ring Cl01F3CommRing.mul_comm L).mp hL)⟩
  have hidem : ExactCard (IsIdempotent Cl01F3Ring) 2 := by
    let f : Fin 2 → Cl01F3
      | ⟨0, _⟩ => Cl01F3Ring.zero
      | ⟨1, _⟩ => Cl01F3Ring.one
    refine ⟨f, by decide, by decide, ?_⟩
    intro ⟨a, b⟩ hm
    revert a b hm
    decide
  exact ⟨htwo, hleft, hidem⟩

def f3Index : Fin 3 → F3
  | ⟨0, _⟩ => F3.c0
  | ⟨1, _⟩ => F3.c1
  | ⟨2, _⟩ => F3.c2

def cl01Enum9 (k : Fin 9) : Cl01F3 :=
  ⟨f3Index ⟨k.val / 3, by omega⟩, f3Index ⟨k.val % 3, by omega⟩⟩

theorem cl01F3_card_nine : ExactCard (fun _ : Cl01F3 => True) 9 := by
  refine ⟨cl01Enum9, fun _ => True.intro, by decide, ?_⟩
  intro ⟨a, b⟩ _
  revert a b
  decide

def mat1F3Enum3 (k : Fin 3) : MatN 1 F3 :=
  fun _ _ => f3Index k

theorem mat1F3_card_three : ExactCard (fun _ : MatN 1 F3 => True) 3 := by
  refine ⟨mat1F3Enum3, fun _ => True.intro, ?_, ?_⟩
  · intro i j hij
    have h00 : mat1F3Enum3 i ⟨0, by decide⟩ ⟨0, by decide⟩ =
               mat1F3Enum3 j ⟨0, by decide⟩ ⟨0, by decide⟩ :=
      congrFun (congrFun hij ⟨0, by decide⟩) ⟨0, by decide⟩
    clear hij
    revert i j h00
    decide
  · intro A _
    let v := A ⟨0, by decide⟩ ⟨0, by decide⟩
    have hv : ∃ k : Fin 3, f3Index k = v := by
      cases v with
      | c0 => exact ⟨⟨0, by decide⟩, rfl⟩
      | c1 => exact ⟨⟨1, by decide⟩, rfl⟩
      | c2 => exact ⟨⟨2, by decide⟩, rfl⟩
    obtain ⟨k, hk⟩ := hv
    refine ⟨k, ?_⟩
    funext i j
    have hi : i = ⟨0, by decide⟩ := Fin.ext (by omega)
    have hj : j = ⟨0, by decide⟩ := Fin.ext (by omega)
    rw [hi, hj]
    exact hk

/-- **Division-Algebra Obstruction Theorem A**:
    `Cl_{0,1}(F_3) ≅ F_9` is a simple `F_3`-algebra (`m_two = m_left = 1`) that
    is NOT isomorphic as a ring to ANY split matrix ring `M_{n+1}(F_3)`. -/
theorem cl01_f3_not_iso_any_matN_f3 (n : Nat) :
    ¬ Nonempty (RingIso Cl01F3Ring (MatNRing (n + 1) F3Ring)) := by
  intro ⟨φ⟩
  match n with
  | 0 =>
    have h9 : ExactCard (fun _ : MatN 1 F3 => True) 9 := by
      obtain ⟨f, _, hfinj, hfsurj⟩ := cl01F3_card_nine
      refine ⟨fun i => φ.toFun (f i), fun _ => True.intro, ?_, ?_⟩
      · intro i j hij
        dsimp at hij
        apply hfinj
        rw [← φ.left_inv (f i), ← φ.left_inv (f j), hij]
      · intro B _
        obtain ⟨i, hi⟩ := hfsurj (φ.invFun B) True.intro
        refine ⟨i, ?_⟩
        dsimp
        rw [hi, φ.right_inv]
    have h93 : 9 = 3 := exactCard_unique h9 mat1F3_card_three
    omega
  | m + 1 =>
    have hdom := ringIso_preserves_no_zero_divisors φ
      Cl01F3FieldRing.toDomainRing.eq_zero_or_eq_zero_of_mul_eq_zero
    obtain ⟨A, hAne, hAsq⟩ := matN_has_nonzero_nilpotent m F3Ring
    cases hdom A A hAsq with
    | inl h0 => exact hAne h0
    | inr h0 => exact hAne h0

/-! ## 3. Division-Algebra Obstruction B: Quaternions `H(ℤ)` and `H(K)` -/

abbrev QuatIntRing : UnitalRing (Quat Int) := QuatRing IntCommRing

def quatIntI : Quat Int := ⟨⟨0, 1⟩, ⟨0, 0⟩⟩
def quatIntJ : Quat Int := ⟨⟨0, 0⟩, ⟨1, 0⟩⟩

theorem quatInt_clifford_and_noncomm :
    QuatIntRing.mul quatIntI quatIntI = QuatIntRing.neg QuatIntRing.one ∧
    QuatIntRing.mul quatIntJ quatIntJ = QuatIntRing.neg QuatIntRing.one ∧
    QuatIntRing.add (QuatIntRing.mul quatIntI quatIntJ)
                    (QuatIntRing.mul quatIntJ quatIntI) = QuatIntRing.zero ∧
    QuatIntRing.mul quatIntI quatIntJ ≠ QuatIntRing.mul quatIntJ quatIntI := by
  decide

def intSqNat : Int → Nat
  | Int.ofNat m => m * m
  | Int.negSucc m => (m + 1) * (m + 1)

theorem int_mul_self_eq_ofNat (a : Int) : a * a = Int.ofNat (intSqNat a) := by
  cases a <;> rfl

theorem int_eq_zero_of_intSqNat_eq_zero {a : Int} (h : intSqNat a = 0) : a = 0 := by
  cases a with
  | ofNat m =>
    cases m with
    | zero => rfl
    | succ m' =>
      dsimp [intSqNat] at h
      have hp : 0 < (m' + 1) * (m' + 1) := Nat.mul_pos (Nat.succ_pos m') (Nat.succ_pos m')
      omega
  | negSucc m =>
    dsimp [intSqNat] at h
    have hp : 0 < (m + 1) * (m + 1) := Nat.mul_pos (Nat.succ_pos m) (Nat.succ_pos m)
    omega

theorem quatInt_normSq_eq_zero_iff (q : Quat Int) :
    quatNormSq IntCommRing q = 0 ↔ q = QuatIntRing.zero := by
  constructor
  · intro h0
    change (q.z.re * q.z.re + q.z.im * q.z.im) + (q.w.re * q.w.re + q.w.im * q.w.im) = 0 at h0
    rw [int_mul_self_eq_ofNat, int_mul_self_eq_ofNat,
        int_mul_self_eq_ofNat, int_mul_self_eq_ofNat] at h0
    have hnat : (intSqNat q.z.re + intSqNat q.z.im) +
                (intSqNat q.w.re + intSqNat q.w.im) = 0 := Int.ofNat.inj h0
    have ha0 : q.z.re = 0 := int_eq_zero_of_intSqNat_eq_zero (by omega)
    have hb0 : q.z.im = 0 := int_eq_zero_of_intSqNat_eq_zero (by omega)
    have hc0 : q.w.re = 0 := int_eq_zero_of_intSqNat_eq_zero (by omega)
    have hd0 : q.w.im = 0 := int_eq_zero_of_intSqNat_eq_zero (by omega)
    exact Quat.ext (Gauss.ext ha0 hb0) (Gauss.ext hc0 hd0)
  · intro hq
    rw [hq]; rfl

theorem quatInt_no_zero_divisors (q1 q2 : Quat Int)
    (hmul : QuatIntRing.mul q1 q2 = QuatIntRing.zero) :
    q1 = QuatIntRing.zero ∨ q2 = QuatIntRing.zero := by
  by_cases hq1 : q1 = QuatIntRing.zero
  · exact Or.inl hq1
  · right
    have hn_ne : quatNormSq IntCommRing q1 ≠ 0 :=
      fun h0 => hq1 ((quatInt_normSq_eq_zero_iff q1).mp h0)
    have hconj : QuatIntRing.mul (QuatIntRing.mul (quatConj IntCommRing q1) q1) q2 =
                 QuatIntRing.zero := by
      rw [QuatIntRing.mul_assoc, hmul, QuatIntRing.mul_zero]
    rw [quat_conj_mul_self IntCommRing q1] at hconj
    change (QuatRing IntCommRing).mul (quatScalar IntCommRing (quatNormSq IntCommRing q1)) q2 =
           QuatIntRing.zero at hconj
    rw [quatScalar_mul IntCommRing] at hconj
    have e1 : quatNormSq IntCommRing q1 * q2.z.re = 0 :=
      congrArg Gauss.re (congrArg Quat.z hconj)
    have e2 : quatNormSq IntCommRing q1 * q2.z.im = 0 :=
      congrArg Gauss.im (congrArg Quat.z hconj)
    have e3 : quatNormSq IntCommRing q1 * q2.w.re = 0 :=
      congrArg Gauss.re (congrArg Quat.w hconj)
    have e4 : quatNormSq IntCommRing q1 * q2.w.im = 0 :=
      congrArg Gauss.im (congrArg Quat.w hconj)
    have r1 : q2.z.re = 0 :=
      (int_eq_zero_or_eq_zero_of_mul_eq_zero _ _ e1).resolve_left hn_ne
    have r2 : q2.z.im = 0 :=
      (int_eq_zero_or_eq_zero_of_mul_eq_zero _ _ e2).resolve_left hn_ne
    have r3 : q2.w.re = 0 :=
      (int_eq_zero_or_eq_zero_of_mul_eq_zero _ _ e3).resolve_left hn_ne
    have r4 : q2.w.im = 0 :=
      (int_eq_zero_or_eq_zero_of_mul_eq_zero _ _ e4).resolve_left hn_ne
    cases q2 with | mk z w =>
    cases z; cases w; dsimp at r1 r2 r3 r4; subst r1 r2 r3 r4; rfl

theorem mat1_mul_comm {α : Type u} (C : CommUnitalRing α) (A B : MatN 1 α) :
    (MatNRing 1 C.toUnitalRing).mul A B = (MatNRing 1 C.toUnitalRing).mul B A := by
  funext i j
  let z0 : Fin 1 := ⟨0, Nat.zero_lt_succ 0⟩
  have hi : i = z0 := Fin.ext (by omega)
  have hj : j = z0 := Fin.ext (by omega)
  dsimp [MatNRing, finSum]
  rw [C.toUnitalRing.add_zero, C.toUnitalRing.add_zero]
  change C.mul (A i z0) (B z0 j) = C.mul (B i z0) (A z0 j)
  rw [hi, hj, C.mul_comm]

/-- **Division-Algebra Obstruction Theorem B (Integral Quaternions)**:
    `H(ℤ) = Cl_{0,2}(ℤ)` is NOT ring-isomorphic to `M_{n+1}(ℤ)` for ANY `n`. -/
theorem quatInt_not_iso_any_matN_int (n : Nat) :
    ¬ Nonempty (RingIso QuatIntRing (MatNRing (n + 1) IntRing)) := by
  intro ⟨φ⟩
  match n with
  | 0 =>
    have hcomm := ringIso_preserves_comm φ (mat1_mul_comm IntCommRing)
    exact quatInt_clifford_and_noncomm.2.2.2 (hcomm quatIntI quatIntJ)
  | m + 1 =>
    have hdom := ringIso_preserves_no_zero_divisors φ quatInt_no_zero_divisors
    obtain ⟨A, hAne, hAsq⟩ := matN_has_nonzero_nilpotent m IntRing
    cases hdom A A hAsq with
    | inl h0 => exact hAne h0
    | inr h0 => exact hAne h0

/-- Formally real field (`ℚ`, `ℝ`, etc.): characteristic ≠ 2 and sum of four
    squares vanishes only when all four terms vanish. -/
structure FormallyRealField (α : Type u) extends FieldRing α where
  one_add_one_ne_zero : add one one ≠ zero
  sum4_sq_eq_zero :
    ∀ a b c d : α,
      add (add (mul a a) (mul b b)) (add (mul c c) (mul d d)) = zero →
      a = zero ∧ b = zero ∧ c = zero ∧ d = zero

theorem quat_ij_comm_imp_one_eq_neg_one {α : Type u} (R : UnitalRing α)
    (hcomm : ∀ u v : α, R.mul u v = R.mul v u) :
    let C : CommUnitalRing α := { R with mul_comm := hcomm }
    let Q := QuatRing C
    let qi : Quat α := ⟨⟨R.zero, R.one⟩, ⟨R.zero, R.zero⟩⟩
    let qj : Quat α := ⟨⟨R.zero, R.zero⟩, ⟨R.one, R.zero⟩⟩
    Q.mul qi qj = Q.mul qj qi → R.one = R.neg R.one := by
  intro C Q qi qj hij
  have hw := congrArg Gauss.im (congrArg Quat.w hij)
  dsimp [C, Q, QuatRing, qi, qj, gaussConj, GaussRing, UnitalRing.sub] at hw
  simp only [R.mul_zero, R.zero_mul, R.one_mul, R.mul_one, R.neg_zero,
             R.add_zero, R.zero_add] at hw
  exact hw

/-- **Division-Algebra Obstruction Theorem C (`H(K) = Cl_{0,2}(K)`)**:
    Over any formally real field `K` (such as `ℚ` or `ℝ`), `QuatRing K` is a
    simple division ring (`m_two = 1`) that is NOT ring-isomorphic to `M_{n+1}(K)`
    for ANY `n`. -/
theorem quatField_simple_and_not_matN {α : Type u} (K : FormallyRealField α) :
    let Q := QuatRing K.toCommUnitalRing
    IsSimpleRing Q ∧
    ExactCard (IsMinimalTwoSidedIdeal Q) 1 ∧
    (∀ n : Nat, ¬ Nonempty (RingIso Q (MatNRing (n + 1) K.toUnitalRing))) := by
  let C := K.toCommUnitalRing
  let R := K.toUnitalRing
  let Q := QuatRing C
  have hnorm_zero : ∀ q : Quat α, quatNormSq C q = R.zero → q = Q.zero := by
    intro q h0
    obtain ⟨ha, hb, hc, hd⟩ := K.sum4_sq_eq_zero q.z.re q.z.im q.w.re q.w.im h0
    exact Quat.ext (Gauss.ext ha hb) (Gauss.ext hc hd)
  have hleft_inv : ∀ q : Quat α, q ≠ Q.zero →
      ∃ qinv : Quat α, Q.mul qinv q = Q.one := by
    intro q hqne
    have hn_ne : quatNormSq C q ≠ R.zero := fun h0 => hqne (hnorm_zero q h0)
    let s := K.inv (quatNormSq C q)
    refine ⟨Q.mul (quatScalar C s) (quatConj C q), ?_⟩
    rw [Q.mul_assoc, quat_conj_mul_self C q]
    change Q.mul (quatScalar C s) (quatScalar C (quatNormSq C q)) = Q.one
    rw [quatScalar_mul C]
    have hinv : R.mul s (quatNormSq C q) = R.one := by
      dsimp [s]; rw [K.mul_comm, K.mul_inv_cancel _ hn_ne]
    exact Quat.ext (Gauss.ext hinv (R.mul_zero s)) (Gauss.ext (R.mul_zero s) (R.mul_zero s))
  have hdom : ∀ q1 q2 : Quat α, Q.mul q1 q2 = Q.zero → q1 = Q.zero ∨ q2 = Q.zero := by
    intro q1 q2 hmul
    by_cases h1 : q1 = Q.zero
    · exact Or.inl h1
    · right
      obtain ⟨qinv, hinv⟩ := hleft_inv q1 h1
      calc
        q2 = Q.mul Q.one q2 := (Q.one_mul q2).symm
        _ = Q.mul (Q.mul qinv q1) q2 := by rw [hinv]
        _ = Q.mul qinv (Q.mul q1 q2) := Q.mul_assoc qinv q1 q2
        _ = Q.zero := by rw [hmul, Q.mul_zero]
  have hsimple : IsSimpleRing Q := by
    intro I hI ⟨q, hqI, hqne⟩ x
    obtain ⟨qinv, hinv⟩ := hleft_inv q hqne
    have h1 : I Q.one := by
      rw [← hinv]
      exact hI.1.2 qinv q hqI
    have hx : Q.mul x Q.one = x := Q.mul_one x
    rw [← hx]
    exact hI.1.2 x Q.one h1
  refine ⟨hsimple, simpleRing_exactCard_minimal_two_sided_one Q hsimple, ?_⟩
  intro n ⟨φ⟩
  match n with
  | 0 =>
    have hcomm := ringIso_preserves_comm φ (mat1_mul_comm C)
    let qi : Quat α := ⟨⟨R.zero, R.one⟩, ⟨R.zero, R.zero⟩⟩
    let qj : Quat α := ⟨⟨R.zero, R.zero⟩, ⟨R.one, R.zero⟩⟩
    have hcomp : R.one = R.neg R.one :=
      quat_ij_comm_imp_one_eq_neg_one R K.mul_comm (hcomm qi qj)
    have h11 : R.add R.one R.one = R.zero := by
      calc
        R.add R.one R.one = R.add R.one (R.neg R.one) := by rw [← hcomp]
        _ = R.zero := R.add_right_neg R.one
    exact K.one_add_one_ne_zero h11
  | m + 1 =>
    have hm_dom := ringIso_preserves_no_zero_divisors φ hdom
    obtain ⟨A, hAne, hAsq⟩ := matN_has_nonzero_nilpotent m R
    cases hm_dom A A hAsq with
    | inl h0 => exact hAne h0
    | inr h0 => exact hAne h0

/-! ## 4. Non-Semisimple & Degenerate Clifford Obstructions -/

/-! ### 4A. 1D Exterior Algebra `DualF3 = F_3[ε]/(ε^2) = Λ(F_3^1)` -/

structure DualF3 where
  a : F3
  b : F3
  deriving DecidableEq, Repr

theorem DualF3.ext {x y : DualF3} (ha : x.a = y.a) (hb : x.b = y.b) : x = y := by
  cases x; cases y; dsimp at ha hb; subst ha hb; rfl

def DualF3Ring : UnitalRing DualF3 where
  zero := ⟨F3.c0, F3.c0⟩
  one := ⟨F3.c1, F3.c0⟩
  add := fun x y => ⟨F3.add x.a y.a, F3.add x.b y.b⟩
  neg := fun x => ⟨F3.neg x.a, F3.neg x.b⟩
  mul := fun x y => ⟨F3.mul x.a y.a, F3.add (F3.mul x.a y.b) (F3.mul x.b y.a)⟩
  add_assoc := fun ⟨a1, b1⟩ ⟨a2, b2⟩ ⟨a3, b3⟩ =>
    DualF3.ext (F3Ring.add_assoc a1 a2 a3) (F3Ring.add_assoc b1 b2 b3)
  add_comm := fun ⟨a1, b1⟩ ⟨a2, b2⟩ =>
    DualF3.ext (F3Ring.add_comm a1 a2) (F3Ring.add_comm b1 b2)
  zero_add := fun ⟨a, b⟩ =>
    DualF3.ext (F3Ring.zero_add a) (F3Ring.zero_add b)
  add_left_neg := fun ⟨a, b⟩ =>
    DualF3.ext (F3Ring.add_left_neg a) (F3Ring.add_left_neg b)
  mul_assoc := fun ⟨a1, b1⟩ ⟨a2, b2⟩ ⟨a3, b3⟩ =>
    DualF3.ext
      (F3Ring.mul_assoc a1 a2 a3)
      (by cases a1 <;> cases b1 <;> cases a2 <;> cases b2 <;> cases a3 <;> cases b3 <;> rfl)
  one_mul := fun ⟨a, b⟩ => by cases a <;> cases b <;> rfl
  mul_one := fun ⟨a, b⟩ => by cases a <;> cases b <;> rfl
  left_distrib := fun ⟨a1, b1⟩ ⟨a2, b2⟩ ⟨a3, b3⟩ =>
    DualF3.ext
      (F3Ring.left_distrib a1 a2 a3)
      (by cases a1 <;> cases b1 <;> cases a2 <;> cases b2 <;> cases a3 <;> cases b3 <;> rfl)
  right_distrib := fun ⟨a1, b1⟩ ⟨a2, b2⟩ ⟨a3, b3⟩ =>
    DualF3.ext
      (F3Ring.right_distrib a1 a2 a3)
      (by cases a1 <;> cases b1 <;> cases a2 <;> cases b2 <;> cases a3 <;> cases b3 <;> rfl)
  one_ne_zero := by decide

theorem dualF3_mul_comm (x y : DualF3) :
    DualF3Ring.mul x y = DualF3Ring.mul y x := by
  cases x with | mk a1 b1 =>
  cases y with | mk a2 b2 =>
  cases a1 <;> cases b1 <;> cases a2 <;> cases b2 <;> rfl

def dualRad (x : DualF3) : Prop := x.a = F3.c0

theorem dualRad_isMinimal_and_squareZero :
    IsMinimalTwoSidedIdeal DualF3Ring dualRad ∧
    IsSquareZeroIdeal DualF3Ring dualRad ∧
    (∀ I : DualF3 → Prop, IsMinimalTwoSidedIdeal DualF3Ring I → I = dualRad) := by
  have hTwo : IsTwoSidedIdeal DualF3Ring dualRad := by
    have hL : IsLeftIdeal DualF3Ring dualRad := by
      refine ⟨⟨rfl, ?_, ?_⟩, ?_⟩
      · intro x y hx hy; dsimp [dualRad, DualF3Ring] at *; rw [hx, hy]; rfl
      · intro x hx; dsimp [dualRad, DualF3Ring] at *; rw [hx]; rfl
      · intro r x hx; dsimp [dualRad, DualF3Ring] at *; rw [hx]; simp
    exact ⟨hL, ⟨hL.1, fun x r hx => by rw [dualF3_mul_comm x r]; exact hL.2 r x hx⟩⟩
  have hMin : IsMinimalTwoSidedIdeal DualF3Ring dualRad := by
    refine ⟨hTwo, ⟨⟨F3.c0, F3.c1⟩, rfl, by decide⟩, ?_⟩
    intro J hJ ⟨x, hxJ, hxne⟩ hsub y hy
    have hxa : x.a = F3.c0 := hsub x hxJ
    have hxb : x.b ≠ F3.c0 := by
      intro hb0; apply hxne
      cases x; dsimp at hxa hb0; subst hxa hb0; rfl
    let scale : DualF3 := ⟨F3.mul y.b (F3.inv x.b), F3.c0⟩
    have hmul : DualF3Ring.mul scale x = y := by
      cases x with | mk xa xb =>
      cases y with | mk ya yb =>
      dsimp [dualRad] at hxa hy hxb
      subst hxa hy
      cases xb with
      | c0 => exact absurd rfl hxb
      | c1 => cases yb <;> rfl
      | c2 => cases yb <;> rfl
    rw [← hmul]
    exact hJ.1.2 scale x hxJ
  have hSqZero : IsSquareZeroIdeal DualF3Ring dualRad := by
    intro x y hx hy
    cases x with | mk xa xb =>
    cases y with | mk ya yb =>
    dsimp [dualRad] at hx hy
    subst hx hy
    cases xb <;> rfl
  refine ⟨hMin, hSqZero, ?_⟩
  intro I ⟨hI, ⟨x, hxI, hxne⟩, hImin⟩
  by_cases hxa : x.a ≠ F3.c0
  · -- x is a unit in DualF3: (a, b) * (a^-1, -a^-2 * b) = (1, 0)
    let xinv : DualF3 :=
      ⟨F3.inv x.a, F3.neg (F3.mul (F3.mul (F3.inv x.a) (F3.inv x.a)) x.b)⟩
    have hunit : DualF3Ring.mul xinv x = DualF3Ring.one := by
      cases x with | mk xa xb =>
      dsimp at hxa
      cases xa with
      | c0 => exact absurd rfl hxa
      | c1 => cases xb <;> rfl
      | c2 => cases xb <;> rfl
    have h1 : I DualF3Ring.one := by
      rw [← hunit]; exact hI.1.2 xinv x hxI
    have hall : ∀ y : DualF3, I y := by
      intro y; have hy : DualF3Ring.mul y DualF3Ring.one = y := DualF3Ring.mul_one y
      rw [← hy]; exact hI.1.2 y DualF3Ring.one h1
    have hsup : ∀ y : DualF3, I y → dualRad y :=
      hImin dualRad hMin.1 hMin.2.1 (fun y _ => hall y)
    have hf : dualRad DualF3Ring.one := hsup DualF3Ring.one h1
    exact absurd hf (by intro h; cases h)
  · have hxa0 : x.a = F3.c0 := Classical.byContradiction (fun h => hxa h)
    let Inter : DualF3 → Prop := fun y => I y ∧ dualRad y
    have hInter_two : IsTwoSidedIdeal DualF3Ring Inter :=
      ⟨⟨⟨⟨hI.1.1.1, hMin.1.1.1.1⟩,
         fun a b ha hb => ⟨hI.1.1.2.1 a b ha.1 hb.1, hMin.1.1.1.2.1 a b ha.2 hb.2⟩,
         fun a ha => ⟨hI.1.1.2.2 a ha.1, hMin.1.1.1.2.2 a ha.2⟩⟩,
        fun r y hy => ⟨hI.1.2 r y hy.1, hMin.1.1.2 r y hy.2⟩⟩,
       ⟨⟨⟨hI.1.1.1, hMin.1.1.1.1⟩,
         fun a b ha hb => ⟨hI.1.1.2.1 a b ha.1 hb.1, hMin.1.1.1.2.1 a b ha.2 hb.2⟩,
         fun a ha => ⟨hI.1.1.2.2 a ha.1, hMin.1.1.1.2.2 a ha.2⟩⟩,
        fun y r hy => ⟨hI.2.2 y r hy.1, hMin.1.2.2 y r hy.2⟩⟩⟩
    have hInter_nz : IsNonzeroPred DualF3Ring Inter :=
      ⟨x, ⟨hxI, hxa0⟩, hxne⟩
    have hs1 := hMin.2.2 Inter hInter_two hInter_nz (fun _ hy => hy.2)
    have hs2 := hImin Inter hInter_two hInter_nz (fun _ hy => hy.1)
    funext y
    exact propext ⟨fun hy => (hs2 y hy).2, fun hy => (hs1 y hy).1⟩

/-- **Exterior Algebra Obstruction (`Λ(F_3^1) = F_3[ε]/(ε^2)`)**:
    Unique minimal ideal is square-zero (contains no nonzero idempotents), and
    `DualF3` is not ring-isomorphic to `M_{n+1}(F_3)` for any `n`. -/
theorem dualF3_obstruction_theorem :
    ExactCard (IsIdempotent DualF3Ring) 2 ∧
    ExactCard (IsMinimalTwoSidedIdeal DualF3Ring) 1 ∧
    IsSquareZeroIdeal DualF3Ring dualRad ∧
    (∀ e : DualF3, dualRad e → IsIdempotent DualF3Ring e → e = DualF3Ring.zero) ∧
    (∀ n : Nat, ¬ Nonempty (RingIso DualF3Ring (MatNRing (n + 1) F3Ring))) := by
  have hidem : ExactCard (IsIdempotent DualF3Ring) 2 := by
    let f : Fin 2 → DualF3
      | ⟨0, _⟩ => DualF3Ring.zero
      | ⟨1, _⟩ => DualF3Ring.one
    refine ⟨f, by decide, by decide, ?_⟩
    intro ⟨a, b⟩ hm; revert a b hm; decide
  obtain ⟨hMin, hSq, hUniq⟩ := dualRad_isMinimal_and_squareZero
  have hcard1 : ExactCard (IsMinimalTwoSidedIdeal DualF3Ring) 1 := by
    refine ⟨fun _ => dualRad, fun _ => hMin, fun _ _ _ => Fin.ext (by omega), ?_⟩
    intro I hI
    exact ⟨⟨0, Nat.zero_lt_one⟩, (hUniq I hI).symm⟩
  have hno_idem : ∀ e : DualF3, dualRad e → IsIdempotent DualF3Ring e → e = DualF3Ring.zero :=
    fun e he hid => hid.symm.trans (hSq e e he he)
  refine ⟨hidem, hcard1, hSq, hno_idem, ?_⟩
  intro n ⟨φ⟩
  match n with
  | 0 =>
    let enum9 : Fin 9 → DualF3 := fun k =>
      ⟨f3Index ⟨k.val / 3, by omega⟩, f3Index ⟨k.val % 3, by omega⟩⟩
    have hDual9 : ExactCard (fun _ : DualF3 => True) 9 := by
      refine ⟨enum9, fun _ => True.intro, by decide, ?_⟩
      intro ⟨a, b⟩ _; revert a b; decide
    have hMat9 : ExactCard (fun _ : MatN 1 F3 => True) 9 := by
      obtain ⟨f, _, hfinj, hfsurj⟩ := hDual9
      refine ⟨fun i => φ.toFun (f i), fun _ => True.intro, ?_, ?_⟩
      · intro i j hij; dsimp at hij; apply hfinj; rw [← φ.left_inv (f i), ← φ.left_inv (f j), hij]
      · intro B _; obtain ⟨i, hi⟩ := hfsurj (φ.invFun B) True.intro
        exact ⟨i, by dsimp; rw [hi, φ.right_inv]⟩
    have h93 : 9 = 3 := exactCard_unique hMat9 mat1F3_card_three
    omega
  | m + 1 =>
    -- MatN (m + 2) F3 is noncommutative while DualF3 is commutative!
    let M := MatNRing (m + 2) F3Ring
    let i0 : Fin (m + 2) := ⟨0, by omega⟩
    let i1 : Fin (m + 2) := ⟨1, by omega⟩
    let E00 : MatN (m + 2) F3 := fun i j => if i = i0 ∧ j = i0 then F3.c1 else F3.c0
    let E01 : MatN (m + 2) F3 := fun i j => if i = i0 ∧ j = i1 then F3.c1 else F3.c0
    have h_lhs : M.mul E00 E01 i0 i1 = F3.c1 := by
      dsimp [M, MatNRing]
      rw [finSum_single F3Ring i0]
      · dsimp [E00, E01, F3Ring]
      · intro k hk
        dsimp [E00, E01, F3Ring]
        simp [hk]
    have h_rhs : M.mul E01 E00 i0 i1 = F3.c0 := by
      dsimp [M, MatNRing]
      calc
        finSum F3Ring (m + 2) (fun k => F3.mul (E01 i0 k) (E00 k i1))
          = finSum F3Ring (m + 2) (fun _ => F3.c0) := by
            apply finSum_congr
            intro k
            have h10 : i1 ≠ i0 := fun h => Nat.one_ne_zero (congrArg Fin.val h)
            have hn2 : ¬ (k = i0 ∧ i1 = i0) := fun h => h10 h.2
            dsimp [E00, E01, F3Ring]; simp [hn2]
        _ = F3.c0 := finSum_zero_const F3Ring (m + 2)
    have hcomm_M : M.mul E00 E01 = M.mul E01 E00 := by
      rw [← φ.right_inv E00, ← φ.right_inv E01, ← φ.map_mul, ← φ.map_mul,
          dualF3_mul_comm]
    have h10 : F3.c1 = F3.c0 := by
      rw [← h_lhs, ← h_rhs, hcomm_M]
    exact F3Ring.one_ne_zero h10

/-! ### 4B. Commutative Local Algebra `LocalF3 = F_3[x, y]/(x^2, xy, y^2)` -/

structure LocalF3 where
  a : F3
  b : F3
  c : F3
  deriving DecidableEq, Repr

theorem LocalF3.ext {u v : LocalF3}
    (ha : u.a = v.a) (hb : u.b = v.b) (hc : u.c = v.c) : u = v := by
  cases u; cases v; dsimp at ha hb hc; subst ha hb hc; rfl

def LocalF3Ring : UnitalRing LocalF3 where
  zero := ⟨F3.c0, F3.c0, F3.c0⟩
  one := ⟨F3.c1, F3.c0, F3.c0⟩
  add := fun u v => ⟨F3.add u.a v.a, F3.add u.b v.b, F3.add u.c v.c⟩
  neg := fun u => ⟨F3.neg u.a, F3.neg u.b, F3.neg u.c⟩
  mul := fun u v =>
    ⟨F3.mul u.a v.a,
     F3.add (F3.mul u.a v.b) (F3.mul u.b v.a),
     F3.add (F3.mul u.a v.c) (F3.mul u.c v.a)⟩
  add_assoc := fun ⟨a1, b1, z1⟩ ⟨a2, b2, z2⟩ ⟨a3, b3, z3⟩ =>
    LocalF3.ext (F3Ring.add_assoc a1 a2 a3)
      (F3Ring.add_assoc b1 b2 b3) (F3Ring.add_assoc z1 z2 z3)
  add_comm := fun ⟨a1, b1, z1⟩ ⟨a2, b2, z2⟩ =>
    LocalF3.ext (F3Ring.add_comm a1 a2)
      (F3Ring.add_comm b1 b2) (F3Ring.add_comm z1 z2)
  zero_add := fun ⟨a, b, z⟩ =>
    LocalF3.ext (F3Ring.zero_add a) (F3Ring.zero_add b) (F3Ring.zero_add z)
  add_left_neg := fun ⟨a, b, z⟩ =>
    LocalF3.ext (F3Ring.add_left_neg a) (F3Ring.add_left_neg b) (F3Ring.add_left_neg z)
  mul_assoc := fun ⟨a1, b1, z1⟩ ⟨a2, b2, z2⟩ ⟨a3, b3, z3⟩ =>
    LocalF3.ext
      (F3Ring.mul_assoc a1 a2 a3)
      (by cases a1 <;> cases b1 <;> cases a2 <;> cases b2 <;> cases a3 <;> cases b3 <;> rfl)
      (by cases a1 <;> cases z1 <;> cases a2 <;> cases z2 <;> cases a3 <;> cases z3 <;> rfl)
  one_mul := fun ⟨a, b, z⟩ =>
    LocalF3.ext (F3Ring.one_mul a)
      (by cases a <;> cases b <;> rfl) (by cases a <;> cases z <;> rfl)
  mul_one := fun ⟨a, b, z⟩ =>
    LocalF3.ext (F3Ring.mul_one a)
      (by cases a <;> cases b <;> rfl) (by cases a <;> cases z <;> rfl)
  left_distrib := fun ⟨a1, b1, z1⟩ ⟨a2, b2, z2⟩ ⟨a3, b3, z3⟩ =>
    LocalF3.ext
      (F3Ring.left_distrib a1 a2 a3)
      (by cases a1 <;> cases b1 <;> cases a2 <;> cases b2 <;> cases a3 <;> cases b3 <;> rfl)
      (by cases a1 <;> cases z1 <;> cases a2 <;> cases z2 <;> cases a3 <;> cases z3 <;> rfl)
  right_distrib := fun ⟨a1, b1, z1⟩ ⟨a2, b2, z2⟩ ⟨a3, b3, z3⟩ =>
    LocalF3.ext
      (F3Ring.right_distrib a1 a2 a3)
      (by cases a1 <;> cases b1 <;> cases a2 <;> cases b2 <;> cases a3 <;> cases b3 <;> rfl)
      (by cases a1 <;> cases z1 <;> cases a2 <;> cases z2 <;> cases a3 <;> cases z3 <;> rfl)
  one_ne_zero := by decide

theorem localF3_mul_comm (u v : LocalF3) :
    LocalF3Ring.mul u v = LocalF3Ring.mul v u := by
  cases u with | mk ua ub uz =>
  cases v with | mk va vb vz =>
  exact LocalF3.ext
    (F3CommRing.mul_comm ua va)
    (by cases ua <;> cases ub <;> cases va <;> cases vb <;> rfl)
    (by cases ua <;> cases uz <;> cases va <;> cases vz <;> rfl)

def localMin4 (k : Fin 4) : LocalF3 → Prop :=
  match k with
  | ⟨0, _⟩ => fun u => u.a = F3.c0 ∧ u.c = F3.c0
  | ⟨1, _⟩ => fun u => u.a = F3.c0 ∧ u.b = F3.c0
  | ⟨2, _⟩ => fun u => u.a = F3.c0 ∧ u.c = u.b
  | ⟨3, _⟩ => fun u => u.a = F3.c0 ∧ u.c = F3.mul F3.c2 u.b

theorem localMin4_isMinimal (k : Fin 4) :
    IsMinimalTwoSidedIdeal LocalF3Ring (localMin4 k) := by
  apply (comm_minLeft_iff_minTwoSided LocalF3Ring localF3_mul_comm (localMin4 k)).mp
  match k with
  | ⟨0, _⟩ =>
    refine ⟨⟨⟨⟨rfl, rfl⟩, ?_, ?_⟩, ?_⟩, ⟨⟨F3.c0, F3.c1, F3.c0⟩, ⟨rfl, rfl⟩, by decide⟩, ?_⟩
    · intro u v hu hv
      dsimp [localMin4, LocalF3Ring] at *; rw [hu.1, hv.1, hu.2, hv.2]; exact ⟨rfl, rfl⟩
    · intro u hu
      dsimp [localMin4, LocalF3Ring] at *; rw [hu.1, hu.2]; exact ⟨rfl, rfl⟩
    · intro r u hu
      dsimp [localMin4, LocalF3Ring] at *; rw [hu.1, hu.2]; exact ⟨by simp, by simp⟩
    · intro M hM ⟨u, huM, hune⟩ hsub y hy
      obtain ⟨hua, huc⟩ := hsub u huM
      dsimp [localMin4] at hua huc hy
      have hub : u.b ≠ F3.c0 := by
        intro hb0; apply hune; cases u; dsimp at hua hb0 huc; subst hua hb0 huc; rfl
      let r : LocalF3 := ⟨F3.mul y.b (F3.inv u.b), F3.c0, F3.c0⟩
      have hmul : LocalF3Ring.mul r u = y := by
        cases u with | mk ua ub uc =>
        cases y with | mk ya yb yc =>
        dsimp [r] at *; rw [hua, huc, hy.1, hy.2]
        cases ub with
        | c0 => exact absurd rfl hub
        | c1 => cases yb <;> rfl
        | c2 => cases yb <;> rfl
      rw [← hmul]; exact hM.2 r u huM
  | ⟨1, _⟩ =>
    refine ⟨⟨⟨⟨rfl, rfl⟩, ?_, ?_⟩, ?_⟩, ⟨⟨F3.c0, F3.c0, F3.c1⟩, ⟨rfl, rfl⟩, by decide⟩, ?_⟩
    · intro u v hu hv
      dsimp [localMin4, LocalF3Ring] at *; rw [hu.1, hv.1, hu.2, hv.2]; exact ⟨rfl, rfl⟩
    · intro u hu
      dsimp [localMin4, LocalF3Ring] at *; rw [hu.1, hu.2]; exact ⟨rfl, rfl⟩
    · intro r u hu
      dsimp [localMin4, LocalF3Ring] at *; rw [hu.1, hu.2]; exact ⟨by simp, by simp⟩
    · intro M hM ⟨u, huM, hune⟩ hsub y hy
      obtain ⟨hua, hub⟩ := hsub u huM
      dsimp [localMin4] at hua hub hy
      have huc : u.c ≠ F3.c0 := by
        intro hc0; apply hune; cases u; dsimp at hua hub hc0; subst hua hub hc0; rfl
      let r : LocalF3 := ⟨F3.mul y.c (F3.inv u.c), F3.c0, F3.c0⟩
      have hmul : LocalF3Ring.mul r u = y := by
        cases u with | mk ua ub uc =>
        cases y with | mk ya yb yc =>
        dsimp [r] at *; rw [hua, hub, hy.1, hy.2]
        cases uc with
        | c0 => exact absurd rfl huc
        | c1 => cases yc <;> rfl
        | c2 => cases yc <;> rfl
      rw [← hmul]; exact hM.2 r u huM
  | ⟨2, _⟩ =>
    refine ⟨⟨⟨⟨rfl, rfl⟩, ?_, ?_⟩, ?_⟩, ⟨⟨F3.c0, F3.c1, F3.c1⟩, ⟨rfl, rfl⟩, by decide⟩, ?_⟩
    · intro u v hu hv
      dsimp [localMin4, LocalF3Ring] at *; rw [hu.1, hv.1, hu.2, hv.2]; exact ⟨rfl, rfl⟩
    · intro u hu
      dsimp [localMin4, LocalF3Ring] at *; rw [hu.1, hu.2]; exact ⟨rfl, rfl⟩
    · intro r u hu
      dsimp [localMin4, LocalF3Ring] at *; rw [hu.1, hu.2]; exact ⟨by simp, by simp⟩
    · intro M hM ⟨u, huM, hune⟩ hsub y hy
      obtain ⟨hua, huc⟩ := hsub u huM
      dsimp [localMin4] at hua huc hy
      have hub : u.b ≠ F3.c0 := by
        intro hb0; apply hune; cases u; dsimp at hua huc hb0; rw [hua, huc, hb0]; rfl
      let r : LocalF3 := ⟨F3.mul y.b (F3.inv u.b), F3.c0, F3.c0⟩
      have hmul : LocalF3Ring.mul r u = y := by
        cases u with | mk ua ub uc =>
        cases y with | mk ya yb yc =>
        dsimp [r] at *; rw [hua, huc, hy.1, hy.2]
        cases ub with
        | c0 => exact absurd rfl hub
        | c1 => cases yb <;> rfl
        | c2 => cases yb <;> rfl
      rw [← hmul]; exact hM.2 r u huM
  | ⟨3, _⟩ =>
    refine ⟨⟨⟨⟨rfl, rfl⟩, ?_, ?_⟩, ?_⟩, ⟨⟨F3.c0, F3.c1, F3.c2⟩, ⟨rfl, rfl⟩, by decide⟩, ?_⟩
    · intro u v hu hv
      cases u with | mk ua ub uc =>
      cases v with | mk va vb vc =>
      dsimp [localMin4] at hu hv
      dsimp [localMin4, LocalF3Ring]
      rw [hu.1, hu.2, hv.1, hv.2]
      exact ⟨rfl, by cases ub <;> cases vb <;> rfl⟩
    · intro u hu
      cases u with | mk ua ub uc =>
      dsimp [localMin4] at hu
      dsimp [localMin4, LocalF3Ring]
      rw [hu.1, hu.2]
      exact ⟨rfl, by cases ub <;> rfl⟩
    · intro r u hu
      cases r with | mk ra rb rc =>
      cases u with | mk ua ub uc =>
      dsimp [localMin4] at hu
      dsimp [localMin4, LocalF3Ring]
      rw [hu.1, hu.2]
      exact ⟨by simp, by cases ra <;> cases rb <;> cases rc <;> cases ub <;> rfl⟩
    · intro M hM ⟨u, huM, hune⟩ hsub y hy
      obtain ⟨hua, huc⟩ := hsub u huM
      dsimp [localMin4] at hua huc hy
      have hub : u.b ≠ F3.c0 := by
        intro hb0; apply hune; cases u; dsimp at hua huc hb0; rw [hua, huc, hb0]; rfl
      let r : LocalF3 := ⟨F3.mul y.b (F3.inv u.b), F3.c0, F3.c0⟩
      have hmul : LocalF3Ring.mul r u = y := by
        cases u with | mk ua ub uc =>
        cases y with | mk ya yb yc =>
        dsimp [r] at *; rw [hua, huc, hy.1, hy.2]
        cases ub with
        | c0 => exact absurd rfl hub
        | c1 => cases yb <;> rfl
        | c2 => cases yb <;> rfl
      rw [← hmul]; exact hM.2 r u huM
  | ⟨n + 4, hn⟩ => omega

/-- **Commutative Non-Semisimple Counterexample (`F_3[x, y]/(x^2, xy, y^2)`)**:
    In a commutative ring (where every idempotent is central and left ideals =
    two-sided ideals), idempotent decomposition length and count are BOTH `1`,
    YET `ExactCard IsMinimalTwoSidedIdeal 4` (`4 ≠ 1`), and all `4` minimal
    ideals are square-zero nilpotent! -/
theorem localF3_commutative_counterexample :
    (∀ u v : LocalF3, LocalF3Ring.mul u v = LocalF3Ring.mul v u) ∧
    ExactCard (IsIdempotent LocalF3Ring) 2 ∧
    ExactCard (IsPrimitiveIdempotent LocalF3Ring) 1 ∧
    (∀ (r : Nat) (e : Fin r → LocalF3), IsPrimOrthDecomp LocalF3Ring r e → r = 1) ∧
    ExactCard (IsUnordPrimOrthDecomp LocalF3Ring) 1 ∧
    ExactCard (IsMinimalTwoSidedIdeal LocalF3Ring) 4 ∧
    (∀ I : LocalF3 → Prop, IsMinimalTwoSidedIdeal LocalF3Ring I →
      IsSquareZeroIdeal LocalF3Ring I) ∧
    ¬ (∃ k, ExactCard (IsUnordPrimOrthDecomp LocalF3Ring) k ∧
            ExactCard (IsMinimalTwoSidedIdeal LocalF3Ring) k) := by
  have hidem_iff : ∀ u : LocalF3,
      IsIdempotent LocalF3Ring u ↔ u = LocalF3Ring.zero ∨ u = LocalF3Ring.one := by
    intro ⟨a, b, c⟩
    revert a b c; decide
  have hidem2 : ExactCard (IsIdempotent LocalF3Ring) 2 := by
    let f : Fin 2 → LocalF3
      | ⟨0, _⟩ => LocalF3Ring.zero
      | ⟨1, _⟩ => LocalF3Ring.one
    refine ⟨f, by decide, by decide, ?_⟩
    intro u hu
    cases (hidem_iff u).mp hu with
    | inl h0 => exact ⟨⟨0, by decide⟩, h0.symm⟩
    | inr h1 => exact ⟨⟨1, by decide⟩, h1.symm⟩
  have h1_prim : IsPrimitiveIdempotent LocalF3Ring LocalF3Ring.one := by
    refine ⟨⟨LocalF3Ring.one_mul _, LocalF3Ring.one_ne_zero⟩, ?_⟩
    intro ⟨f, g, hf, hg, horth, _⟩
    cases (hidem_iff f).mp hf.1 with
    | inl hf0 => exact hf.2 hf0
    | inr hf1 =>
      cases (hidem_iff g).mp hg.1 with
      | inl hg0 => exact hg.2 hg0
      | inr hg1 =>
        have h10 : LocalF3Ring.one = LocalF3Ring.zero := by
          have h := horth.1; rw [hf1, hg1, LocalF3Ring.one_mul] at h; exact h
        exact LocalF3Ring.one_ne_zero h10
  have hprim_iff : ∀ u : LocalF3,
      IsPrimitiveIdempotent LocalF3Ring u ↔ u = LocalF3Ring.one := by
    intro u
    constructor
    · intro hp
      cases (hidem_iff u).mp hp.1.1 with
      | inl h0 => exact absurd h0 hp.1.2
      | inr h1 => exact h1
    · intro h1; subst h1; exact h1_prim
  have hprim1 : ExactCard (IsPrimitiveIdempotent LocalF3Ring) 1 := by
    refine ⟨fun _ => LocalF3Ring.one, fun _ => h1_prim, fun _ _ _ => Fin.ext (by omega), ?_⟩
    intro u hu; exact ⟨⟨0, Nat.zero_lt_one⟩, ((hprim_iff u).mp hu).symm⟩
  have hlen : ∀ (r : Nat) (e : Fin r → LocalF3), IsPrimOrthDecomp LocalF3Ring r e → r = 1 := by
    intro r e he
    match r with
    | 0 => exact absurd he.1.2.2.symm LocalF3Ring.one_ne_zero
    | 1 => rfl
    | m + 2 =>
      let i0 : Fin (m + 2) := ⟨0, by omega⟩
      let i1 : Fin (m + 2) := ⟨1, by omega⟩
      have hne : i0 ≠ i1 := fun h => by
        have hv : (0 : Nat) = 1 := congrArg Fin.val h
        exact absurd hv (by decide)
      have he0 : e i0 = LocalF3Ring.one := (hprim_iff (e i0)).mp (he.2 i0)
      have he1 : e i1 = LocalF3Ring.one := (hprim_iff (e i1)).mp (he.2 i1)
      have h0 : LocalF3Ring.mul (e i0) (e i1) = LocalF3Ring.zero := (he.1.2.1 i0 i1 hne).1
      rw [he0, he1, LocalF3Ring.one_mul] at h0
      exact absurd h0 LocalF3Ring.one_ne_zero
  have hunord1 : ExactCard (IsUnordPrimOrthDecomp LocalF3Ring) 1 := by
    let S0 : LocalF3 → Prop := fun x => x = LocalF3Ring.one
    refine ⟨fun _ => S0, ?_, fun _ _ _ => Fin.ext (by omega), ?_⟩
    · intro _
      refine ⟨1, fun _ => LocalF3Ring.one, ?_, ?_⟩
      · refine ⟨⟨fun _ => h1_prim.1, fun i j hne => absurd (Fin.ext (by omega)) hne, ?_⟩,
                fun _ => h1_prim⟩
        simp only [finSum]; exact LocalF3Ring.add_zero _
      · funext x; apply propext
        exact ⟨fun hx => ⟨⟨0, Nat.zero_lt_one⟩, hx⟩, fun ⟨_, hx⟩ => hx⟩
    · intro S ⟨r, e, he, hS⟩
      have hr : r = 1 := hlen r e he
      subst hr
      refine ⟨⟨0, Nat.zero_lt_one⟩, ?_⟩
      rw [hS]
      funext x; apply propext
      constructor
      · intro hx; exact ⟨⟨0, Nat.zero_lt_one⟩, hx.trans ((hprim_iff _).mp (he.2 _)).symm⟩
      · intro ⟨i, hxi⟩; exact hxi.trans ((hprim_iff (e i)).mp (he.2 i))
  have hmin4_surj : ∀ I : LocalF3 → Prop,
      IsMinimalTwoSidedIdeal LocalF3Ring I → ∃ k : Fin 4, localMin4 k = I := by
    intro I ⟨hI, ⟨u, huI, hune⟩, hImin⟩
    by_cases hua : u.a ≠ F3.c0
    · let uinv : LocalF3 :=
        ⟨F3.inv u.a,
         F3.neg (F3.mul (F3.mul (F3.inv u.a) (F3.inv u.a)) u.b),
         F3.neg (F3.mul (F3.mul (F3.inv u.a) (F3.inv u.a)) u.c)⟩
      have hunit : LocalF3Ring.mul uinv u = LocalF3Ring.one := by
        cases u with | mk ua ub uc =>
        dsimp at hua
        cases ua with
        | c0 => exact absurd rfl hua
        | c1 => exact LocalF3.ext rfl (by cases ub <;> rfl) (by cases uc <;> rfl)
        | c2 => exact LocalF3.ext rfl (by cases ub <;> rfl) (by cases uc <;> rfl)
      have h1 : I LocalF3Ring.one := by rw [← hunit]; exact hI.1.2 uinv u huI
      have hall : ∀ y : LocalF3, I y := by
        intro y; rw [← LocalF3Ring.mul_one y]; exact hI.1.2 y _ h1
      have hLk := localMin4_isMinimal ⟨0, by decide⟩
      have hsup := hImin _ hLk.1 hLk.2.1 (fun y _ => hall y)
      exact absurd (hsup LocalF3Ring.one h1).1 (by decide)
    · have hua0 : u.a = F3.c0 := Classical.byContradiction (fun h => hua h)
      have hbc : u.b ≠ F3.c0 ∨ u.c ≠ F3.c0 := by
        apply Classical.byContradiction
        intro hnot
        have hb0 : u.b = F3.c0 := Classical.byContradiction (fun h => hnot (Or.inl h))
        have hc0 : u.c = F3.c0 := Classical.byContradiction (fun h => hnot (Or.inr h))
        apply hune; cases u; dsimp at hua0 hb0 hc0; subst hua0 hb0 hc0; rfl
      have match_k : ∃ k : Fin 4, localMin4 k u := by
        cases u with | mk ua ub uc =>
        dsimp at hua0 hbc; subst hua0
        cases ub with
        | c0 =>
          cases uc with
          | c0 => cases hbc with | inl h => exact absurd rfl h | inr h => exact absurd rfl h
          | c1 => exact ⟨⟨1, by decide⟩, ⟨rfl, rfl⟩⟩
          | c2 => exact ⟨⟨1, by decide⟩, ⟨rfl, rfl⟩⟩
        | c1 =>
          cases uc with
          | c0 => exact ⟨⟨0, by decide⟩, ⟨rfl, rfl⟩⟩
          | c1 => exact ⟨⟨2, by decide⟩, ⟨rfl, rfl⟩⟩
          | c2 => exact ⟨⟨3, by decide⟩, ⟨rfl, rfl⟩⟩
        | c2 =>
          cases uc with
          | c0 => exact ⟨⟨0, by decide⟩, ⟨rfl, rfl⟩⟩
          | c1 => exact ⟨⟨3, by decide⟩, ⟨rfl, rfl⟩⟩
          | c2 => exact ⟨⟨2, by decide⟩, ⟨rfl, rfl⟩⟩
      obtain ⟨k, hku⟩ := match_k
      have hLk := localMin4_isMinimal k
      let Inter : LocalF3 → Prop := fun y => I y ∧ localMin4 k y
      have hInter_two : IsTwoSidedIdeal LocalF3Ring Inter :=
        ⟨⟨⟨⟨hI.1.1.1, hLk.1.1.1.1⟩,
           fun a b ha hb => ⟨hI.1.1.2.1 a b ha.1 hb.1, hLk.1.1.1.2.1 a b ha.2 hb.2⟩,
           fun a ha => ⟨hI.1.1.2.2 a ha.1, hLk.1.1.1.2.2 a ha.2⟩⟩,
          fun r y hy => ⟨hI.1.2 r y hy.1, hLk.1.1.2 r y hy.2⟩⟩,
         ⟨⟨⟨hI.1.1.1, hLk.1.1.1.1⟩,
           fun a b ha hb => ⟨hI.1.1.2.1 a b ha.1 hb.1, hLk.1.1.1.2.1 a b ha.2 hb.2⟩,
           fun a ha => ⟨hI.1.1.2.2 a ha.1, hLk.1.1.1.2.2 a ha.2⟩⟩,
          fun y r hy => ⟨hI.2.2 y r hy.1, hLk.1.2.2 y r hy.2⟩⟩⟩
      have hInter_nz : IsNonzeroPred LocalF3Ring Inter := ⟨u, ⟨huI, hku⟩, hune⟩
      have hs1 := hLk.2.2 Inter hInter_two hInter_nz (fun _ hy => hy.2)
      have hs2 := hImin Inter hInter_two hInter_nz (fun _ hy => hy.1)
      refine ⟨k, ?_⟩
      funext y
      exact propext ⟨fun hy => (hs1 y hy).1, fun hy => (hs2 y hy).2⟩
  have hmin4 : ExactCard (IsMinimalTwoSidedIdeal LocalF3Ring) 4 := by
    refine ⟨localMin4, localMin4_isMinimal, ?_, hmin4_surj⟩
    intro i j hij
    have test : ∀ u : LocalF3, localMin4 i u ↔ localMin4 j u := fun u => by rw [hij]
    match i, j with
    | ⟨0, _⟩, ⟨0, _⟩ => rfl
    | ⟨1, _⟩, ⟨1, _⟩ => rfl
    | ⟨2, _⟩, ⟨2, _⟩ => rfl
    | ⟨3, _⟩, ⟨3, _⟩ => rfl
    | ⟨0, _⟩, ⟨1, _⟩ => exact absurd ((test ⟨F3.c0, F3.c1, F3.c0⟩).mp ⟨rfl, rfl⟩).2 (by decide)
    | ⟨0, _⟩, ⟨2, _⟩ => exact absurd ((test ⟨F3.c0, F3.c1, F3.c0⟩).mp ⟨rfl, rfl⟩).2 (by decide)
    | ⟨0, _⟩, ⟨3, _⟩ => exact absurd ((test ⟨F3.c0, F3.c1, F3.c0⟩).mp ⟨rfl, rfl⟩).2 (by decide)
    | ⟨1, _⟩, ⟨0, _⟩ => exact absurd ((test ⟨F3.c0, F3.c1, F3.c0⟩).mpr ⟨rfl, rfl⟩).2 (by decide)
    | ⟨1, _⟩, ⟨2, _⟩ => exact absurd ((test ⟨F3.c0, F3.c0, F3.c1⟩).mp ⟨rfl, rfl⟩).2 (by decide)
    | ⟨1, _⟩, ⟨3, _⟩ => exact absurd ((test ⟨F3.c0, F3.c0, F3.c1⟩).mp ⟨rfl, rfl⟩).2 (by decide)
    | ⟨2, _⟩, ⟨0, _⟩ => exact absurd ((test ⟨F3.c0, F3.c1, F3.c0⟩).mpr ⟨rfl, rfl⟩).2 (by decide)
    | ⟨2, _⟩, ⟨1, _⟩ => exact absurd ((test ⟨F3.c0, F3.c0, F3.c1⟩).mpr ⟨rfl, rfl⟩).2 (by decide)
    | ⟨2, _⟩, ⟨3, _⟩ => exact absurd ((test ⟨F3.c0, F3.c1, F3.c1⟩).mp ⟨rfl, rfl⟩).2 (by decide)
    | ⟨3, _⟩, ⟨0, _⟩ => exact absurd ((test ⟨F3.c0, F3.c1, F3.c0⟩).mpr ⟨rfl, rfl⟩).2 (by decide)
    | ⟨3, _⟩, ⟨1, _⟩ => exact absurd ((test ⟨F3.c0, F3.c0, F3.c1⟩).mpr ⟨rfl, rfl⟩).2 (by decide)
    | ⟨3, _⟩, ⟨2, _⟩ => exact absurd ((test ⟨F3.c0, F3.c1, F3.c1⟩).mpr ⟨rfl, rfl⟩).2 (by decide)
    | ⟨n + 4, hn⟩, _ => omega
    | _, ⟨n + 4, hn⟩ => omega
  have hsq_all : ∀ I : LocalF3 → Prop,
      IsMinimalTwoSidedIdeal LocalF3Ring I → IsSquareZeroIdeal LocalF3Ring I := by
    intro I hI
    obtain ⟨k, hk⟩ := hmin4_surj I hI
    rw [← hk]
    intro x y hx hy
    have hxa : x.a = F3.c0 := by
      match k with
      | ⟨0, _⟩ => exact hx.1
      | ⟨1, _⟩ => exact hx.1
      | ⟨2, _⟩ => exact hx.1
      | ⟨3, _⟩ => exact hx.1
      | ⟨n + 4, hn⟩ => omega
    have hya : y.a = F3.c0 := by
      match k with
      | ⟨0, _⟩ => exact hy.1
      | ⟨1, _⟩ => exact hy.1
      | ⟨2, _⟩ => exact hy.1
      | ⟨3, _⟩ => exact hy.1
      | ⟨n + 4, hn⟩ => omega
    cases x with | mk xa xb xz =>
    cases y with | mk ya yb yz =>
    dsimp at hxa hya; subst hxa hya; cases xb <;> cases xz <;> rfl
  exact ⟨localF3_mul_comm, hidem2, hprim1, hlen, hunord1, hmin4, hsq_all,
    exactCard_disjoint_counts hunord1 hmin4 (by decide)⟩

end Conjecture00000007625
