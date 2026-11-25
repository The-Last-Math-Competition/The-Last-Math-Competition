/-
  Conjecture 00000007602 — Module 3: Concrete Instantiation over ℚ (Characteristic 0)
  and Complete Structural Refutations:
    1. Characteristic 2 (F_2): A^k_sgn(F_2^n) NEVER vanishes for ANY k > n ≥ 1,
       and has dimension 3 ≠ choose 2 2 = 1 at (n, k) = (2, 2).
    2. Positive Characteristic p ≤ k ≤ n: k! = 0 destroys (1/k!) Alt_k, forces
       nilpotence Alt_k ∘ Alt_k = 0, prematurely kills iterated outer products
       Alt_3(ω_01 ⊗ e_2) = 0 at n = k = 3, and decouples modular Lucas zeros
       from exterior dimension.
    3. Characteristic 0 (ℤ and ℚ): Higher-grade multivector outer product in
       Λ(ℚ^n) and Cl_{n,0}(ℚ) fails factor-antisymmetrization both below/at the
       threshold (n = 4, r = s = 2) and above the threshold (n = 3, r = s = 2).

  Pure Core Lean 4.19.0 (zero external dependencies).
-/

import Conjecture00000007602.Antisymmetrization

namespace Conjecture00000007602

/-! ## 1. Exact Ring Instances: `ℤ`, `ℚ` (Characteristic 0), and `𝔽_2` (Characteristic 2) -/

def intRing : CommRingOps Int where
  zero := 0
  one := 1
  add := (· + ·)
  neg := (- ·)
  mul := (· * ·)
  add_assoc := Int.add_assoc
  add_comm := Int.add_comm
  zero_add := Int.zero_add
  add_neg := fun a => by omega
  mul_assoc := Int.mul_assoc
  mul_comm := Int.mul_comm
  one_mul := Int.one_mul
  left_distrib := Int.mul_add

/-- Formal rational pairs `(a, b)` representing `a / (b + 1)` with strictly positive denominator. -/
abbrev RawQ : Type := Int × Nat

def RawQRel (x y : RawQ) : Prop :=
  x.1 * ((y.2 + 1 : Nat) : Int) = y.1 * ((x.2 + 1 : Nat) : Int)

theorem int_cancel_pos_nat {x y : Int} (m : Nat)
    (h : x * ((m + 1 : Nat) : Int) = y * ((m + 1 : Nat) : Int)) : x = y := by
  by_cases hxy : x = y
  · exact hxy
  · have hdiff : (x - y) * ((m + 1 : Nat) : Int) = 0 := by
      rw [Int.sub_mul, h]
      omega
    cases Int.mul_eq_zero.mp hdiff with
    | inl hsub => omega
    | inr hm0 => omega

theorem rawQRel_refl (x : RawQ) : RawQRel x x := rfl

theorem rawQRel_symm {x y : RawQ} (h : RawQRel x y) : RawQRel y x := h.symm

theorem rawQRel_trans {x y z : RawQ} (hxy : RawQRel x y) (hyz : RawQRel y z) :
    RawQRel x z := by
  unfold RawQRel at *
  let X := ((x.2 + 1 : Nat) : Int)
  let Y := ((y.2 + 1 : Nat) : Int)
  let Z := ((z.2 + 1 : Nat) : Int)
  change x.1 * Y = y.1 * X at hxy
  change y.1 * Z = z.1 * Y at hyz
  have h1 : x.1 * Z * Y = z.1 * X * Y := by
    calc
      x.1 * Z * Y = (x.1 * Y) * Z := by
            rw [Int.mul_assoc, Int.mul_comm Z Y, ← Int.mul_assoc]
      _ = (y.1 * X) * Z := by rw [hxy]
      _ = (y.1 * Z) * X := by
            rw [Int.mul_assoc, Int.mul_comm X Z, ← Int.mul_assoc]
      _ = (z.1 * Y) * X := by rw [hyz]
      _ = z.1 * X * Y := by
            rw [Int.mul_assoc, Int.mul_comm Y X, ← Int.mul_assoc]
  exact int_cancel_pos_nat y.2 h1

abbrev RatQ : Type := Quot RawQRel

def rawAdd (x y : RawQ) : RawQ :=
  (x.1 * ((y.2 + 1 : Nat) : Int) + y.1 * ((x.2 + 1 : Nat) : Int), (x.2 + 1) * (y.2 + 1) - 1)

def rawNeg (x : RawQ) : RawQ := (-x.1, x.2)

def rawMul (x y : RawQ) : RawQ :=
  (x.1 * y.1, (x.2 + 1) * (y.2 + 1) - 1)

theorem rawDen_prod (a b : Nat) : (a + 1) * (b + 1) - 1 + 1 = (a + 1) * (b + 1) := by
  have hpos : 1 ≤ (a + 1) * (b + 1) := Nat.mul_pos (Nat.succ_pos a) (Nat.succ_pos b)
  omega

theorem int_ring_add_wd {a1 c1 y1 : Int} {a2 c2 y2 : Nat}
    (hac : a1 * ((c2 + 1 : Nat) : Int) = c1 * ((a2 + 1 : Nat) : Int)) :
    (a1 * ((y2 + 1 : Nat) : Int) + y1 * ((a2 + 1 : Nat) : Int)) *
        (((c2 + 1) * (y2 + 1) : Nat) : Int) =
    (c1 * ((y2 + 1 : Nat) : Int) + y1 * ((c2 + 1 : Nat) : Int)) *
        (((a2 + 1) * (y2 + 1) : Nat) : Int) := by
  rw [intCast_mul, intCast_mul, Int.add_mul, Int.add_mul]
  let A := ((a2 + 1 : Nat) : Int)
  let C := ((c2 + 1 : Nat) : Int)
  let Y := ((y2 + 1 : Nat) : Int)
  change a1 * C = c1 * A at hac
  change a1 * Y * (C * Y) + y1 * A * (C * Y) = c1 * Y * (A * Y) + y1 * C * (A * Y)
  have h1 : a1 * Y * (C * Y) = c1 * Y * (A * Y) := by
    calc
      a1 * Y * (C * Y) = (a1 * C) * (Y * Y) := by
            rw [← Int.mul_assoc, Int.mul_assoc a1, Int.mul_comm Y C,
              ← Int.mul_assoc a1, Int.mul_assoc]
      _ = (c1 * A) * (Y * Y) := by rw [hac]
      _ = c1 * Y * (A * Y) := by
            rw [← Int.mul_assoc, Int.mul_assoc c1, Int.mul_comm A Y,
              ← Int.mul_assoc c1, Int.mul_assoc, Int.mul_comm Y A]
  have h2 : y1 * A * (C * Y) = y1 * C * (A * Y) := by
    rw [Int.mul_assoc y1, Int.mul_assoc y1, ← Int.mul_assoc A, Int.mul_comm A C, Int.mul_assoc C]
  rw [h1, h2]

def ratAdd : RatQ → RatQ → RatQ :=
  Quot.lift
    (fun x => Quot.lift (fun y => Quot.mk RawQRel (rawAdd x y)) (by
      intro y1 y2 hy
      apply Quot.sound
      unfold RawQRel rawAdd
      dsimp only
      rw [rawDen_prod, rawDen_prod]
      rw [Int.add_comm (x.1 * _), Int.add_comm (x.1 * _),
        Nat.mul_comm (x.2 + 1) (y2.2 + 1), Nat.mul_comm (x.2 + 1) (y1.2 + 1)]
      exact int_ring_add_wd hy))
    (by
      intro x1 x2 hx
      funext qy
      induction qy using Quot.ind with
      | mk y =>
          apply Quot.sound
          unfold RawQRel rawAdd
          dsimp only
          rw [rawDen_prod, rawDen_prod]
          exact int_ring_add_wd hx)

def ratNeg : RatQ → RatQ :=
  Quot.lift (fun x => Quot.mk RawQRel (rawNeg x)) (by
    intro x1 x2 hx
    apply Quot.sound
    unfold RawQRel rawNeg at *
    dsimp only
    rw [Int.neg_mul, Int.neg_mul, hx])

def ratMul : RatQ → RatQ → RatQ :=
  Quot.lift
    (fun x => Quot.lift (fun y => Quot.mk RawQRel (rawMul x y)) (by
      intro y1 y2 hy
      apply Quot.sound
      unfold RawQRel rawMul at *
      dsimp only
      rw [rawDen_prod, rawDen_prod, intCast_mul, intCast_mul]
      let X := ((x.2 + 1 : Nat) : Int)
      let Y1 := ((y1.2 + 1 : Nat) : Int)
      let Y2 := ((y2.2 + 1 : Nat) : Int)
      change y1.1 * Y2 = y2.1 * Y1 at hy
      change x.1 * y1.1 * (X * Y2) = x.1 * y2.1 * (X * Y1)
      calc
        x.1 * y1.1 * (X * Y2) = (x.1 * X) * (y1.1 * Y2) := by
              rw [Int.mul_assoc x.1, ← Int.mul_assoc y1.1, Int.mul_comm y1.1 X,
                Int.mul_assoc X, ← Int.mul_assoc x.1]
        _ = (x.1 * X) * (y2.1 * Y1) := by rw [hy]
        _ = x.1 * y2.1 * (X * Y1) := by
              rw [Int.mul_assoc x.1, ← Int.mul_assoc X y2.1 Y1, Int.mul_comm X y2.1,
                Int.mul_assoc y2.1 X Y1, ← Int.mul_assoc x.1 y2.1]))
    (by
      intro x1 x2 hx
      funext qy
      induction qy using Quot.ind with
      | mk y =>
          apply Quot.sound
          unfold RawQRel rawMul at *
          dsimp only
          rw [rawDen_prod, rawDen_prod, intCast_mul, intCast_mul]
          let X1 := ((x1.2 + 1 : Nat) : Int)
          let X2 := ((x2.2 + 1 : Nat) : Int)
          let Y := ((y.2 + 1 : Nat) : Int)
          change x1.1 * X2 = x2.1 * X1 at hx
          change x1.1 * y.1 * (X2 * Y) = x2.1 * y.1 * (X1 * Y)
          calc
            x1.1 * y.1 * (X2 * Y) = (x1.1 * X2) * (y.1 * Y) := by
                  rw [Int.mul_assoc x1.1, ← Int.mul_assoc y.1, Int.mul_comm y.1 X2,
                    Int.mul_assoc X2, ← Int.mul_assoc x1.1]
            _ = (x2.1 * X1) * (y.1 * Y) := by rw [hx]
            _ = x2.1 * y.1 * (X1 * Y) := by
                  rw [Int.mul_assoc x2.1, ← Int.mul_assoc X1 y.1 Y, Int.mul_comm X1 y.1,
                    Int.mul_assoc y.1 X1 Y, ← Int.mul_assoc x2.1 y.1])

def ratRing : CommRingOps RatQ where
  zero := Quot.mk RawQRel (0, 0)
  one := Quot.mk RawQRel (1, 0)
  add := ratAdd
  neg := ratNeg
  mul := ratMul
  add_assoc := by
    intro qa qb qc
    induction qa using Quot.ind with | mk a =>
    induction qb using Quot.ind with | mk b =>
    induction qc using Quot.ind with | mk c =>
      apply Quot.sound
      unfold RawQRel rawAdd
      dsimp only
      have hd1 : (a.2 + 1) * (b.2 + 1) - 1 + 1 = (a.2 + 1) * (b.2 + 1) := rawDen_prod a.2 b.2
      have hd2 : (b.2 + 1) * (c.2 + 1) - 1 + 1 = (b.2 + 1) * (c.2 + 1) := rawDen_prod b.2 c.2
      rw [hd1, hd2]
      have hd3 : (a.2 + 1) * (b.2 + 1) * (c.2 + 1) - 1 + 1 =
          (a.2 + 1) * (b.2 + 1) * (c.2 + 1) := by
        have hp : 1 ≤ (a.2 + 1) * (b.2 + 1) * (c.2 + 1) :=
          Nat.mul_pos (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)) (Nat.succ_pos _)
        omega
      have hd4 : (a.2 + 1) * ((b.2 + 1) * (c.2 + 1)) - 1 + 1 =
          (a.2 + 1) * ((b.2 + 1) * (c.2 + 1)) := by
        have hp : 1 ≤ (a.2 + 1) * ((b.2 + 1) * (c.2 + 1)) :=
          Nat.mul_pos (Nat.succ_pos _) (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _))
        omega
      rw [hd3, hd4]
      rw [intCast_mul, intCast_mul, intCast_mul, intCast_mul, intCast_mul]
      let A := ((a.2 + 1 : Nat) : Int)
      let B := ((b.2 + 1 : Nat) : Int)
      let C := ((c.2 + 1 : Nat) : Int)
      let M := A * (B * C)
      simp only [Int.add_mul, Int.mul_assoc]
      rw [Int.add_assoc]
      have hT2 : A * (C * M) = C * (A * M) := by
        rw [← Int.mul_assoc A C M, Int.mul_comm A C, Int.mul_assoc C A M]
      have hT3 : A * (B * M) = B * (A * M) := by
        rw [← Int.mul_assoc A B M, Int.mul_comm A B, Int.mul_assoc B A M]
      rw [hT2, hT3]
  add_comm := by
    intro qa qb
    induction qa using Quot.ind with | mk a =>
    induction qb using Quot.ind with | mk b =>
      apply Quot.sound
      unfold RawQRel rawAdd
      dsimp only
      rw [rawDen_prod, rawDen_prod, Int.add_comm, Nat.mul_comm]
  zero_add := by
    intro qa
    induction qa using Quot.ind with | mk a =>
      apply Quot.sound
      unfold RawQRel rawAdd
      dsimp only
      rw [rawDen_prod]
      simp [Int.zero_mul, Int.zero_add, Int.one_mul, Int.mul_one]
  add_neg := by
    intro qa
    induction qa using Quot.ind with | mk a =>
      apply Quot.sound
      unfold RawQRel rawAdd rawNeg
      dsimp only
      rw [rawDen_prod]
      have h : a.1 * ((a.2 + 1 : Nat) : Int) + (-a.1) * ((a.2 + 1 : Nat) : Int) = 0 := by
        rw [Int.neg_mul]
        omega
      rw [h]
      simp [Int.zero_mul]
  mul_assoc := by
    intro qa qb qc
    induction qa using Quot.ind with | mk a =>
    induction qb using Quot.ind with | mk b =>
    induction qc using Quot.ind with | mk c =>
      apply Quot.sound
      unfold RawQRel rawMul
      dsimp only
      have hd1 : (a.2 + 1) * (b.2 + 1) - 1 + 1 = (a.2 + 1) * (b.2 + 1) := rawDen_prod a.2 b.2
      have hd2 : (b.2 + 1) * (c.2 + 1) - 1 + 1 = (b.2 + 1) * (c.2 + 1) := rawDen_prod b.2 c.2
      rw [hd1, hd2]
      have hd3 : (a.2 + 1) * (b.2 + 1) * (c.2 + 1) - 1 + 1 =
          (a.2 + 1) * (b.2 + 1) * (c.2 + 1) := by
        have hp : 1 ≤ (a.2 + 1) * (b.2 + 1) * (c.2 + 1) :=
          Nat.mul_pos (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)) (Nat.succ_pos _)
        omega
      have hd4 : (a.2 + 1) * ((b.2 + 1) * (c.2 + 1)) - 1 + 1 =
          (a.2 + 1) * ((b.2 + 1) * (c.2 + 1)) := by
        have hp : 1 ≤ (a.2 + 1) * ((b.2 + 1) * (c.2 + 1)) :=
          Nat.mul_pos (Nat.succ_pos _) (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _))
        omega
      rw [hd3, hd4, Int.mul_assoc a.1 b.1 c.1, Nat.mul_assoc]
  mul_comm := by
    intro qa qb
    induction qa using Quot.ind with | mk a =>
    induction qb using Quot.ind with | mk b =>
      apply Quot.sound
      unfold RawQRel rawMul
      dsimp only
      rw [rawDen_prod, rawDen_prod, Int.mul_comm a.1 b.1, Nat.mul_comm]
  one_mul := by
    intro qa
    induction qa using Quot.ind with | mk a =>
      apply Quot.sound
      unfold RawQRel rawMul
      dsimp only
      rw [rawDen_prod]
      simp [Int.one_mul]
  left_distrib := by
    intro qa qb qc
    induction qa using Quot.ind with | mk a =>
    induction qb using Quot.ind with | mk b =>
    induction qc using Quot.ind with | mk c =>
      apply Quot.sound
      unfold RawQRel rawMul rawAdd
      dsimp only
      have hd_bc : (b.2 + 1) * (c.2 + 1) - 1 + 1 = (b.2 + 1) * (c.2 + 1) := rawDen_prod b.2 c.2
      have hd_ab : (a.2 + 1) * (b.2 + 1) - 1 + 1 = (a.2 + 1) * (b.2 + 1) := rawDen_prod a.2 b.2
      have hd_ac : (a.2 + 1) * (c.2 + 1) - 1 + 1 = (a.2 + 1) * (c.2 + 1) := rawDen_prod a.2 c.2
      rw [hd_bc, hd_ab, hd_ac]
      have hd_L : (a.2 + 1) * ((b.2 + 1) * (c.2 + 1)) - 1 + 1 =
          (a.2 + 1) * ((b.2 + 1) * (c.2 + 1)) := by
        have hp : 1 ≤ (a.2 + 1) * ((b.2 + 1) * (c.2 + 1)) :=
          Nat.mul_pos (Nat.succ_pos _) (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _))
        omega
      have hd_R : (a.2 + 1) * (b.2 + 1) * ((a.2 + 1) * (c.2 + 1)) - 1 + 1 =
          (a.2 + 1) * (b.2 + 1) * ((a.2 + 1) * (c.2 + 1)) := by
        have hp : 1 ≤ (a.2 + 1) * (b.2 + 1) * ((a.2 + 1) * (c.2 + 1)) :=
          Nat.mul_pos (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _))
            (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _))
        omega
      rw [hd_L, hd_R]
      rw [intCast_mul, intCast_mul, intCast_mul, intCast_mul, intCast_mul]
      simp only [Int.mul_add, Int.add_mul]
      let A := ((a.2 + 1 : Nat) : Int)
      let B := ((b.2 + 1 : Nat) : Int)
      let C := ((c.2 + 1 : Nat) : Int)
      have h1 : a.1 * (b.1 * C) * (A * B * (A * C)) = a.1 * b.1 * (A * C) * (A * (B * C)) := by
        calc
          a.1 * (b.1 * C) * (A * B * (A * C))
              = (a.1 * b.1) * (C * ((A * B) * (A * C))) := by
                  rw [← Int.mul_assoc a.1 b.1 C, Int.mul_assoc (a.1 * b.1)]
          _ = (a.1 * b.1) * ((A * C) * (A * (B * C))) := by
                congr 1
                calc
                  C * ((A * B) * (A * C))
                      = C * (A * (B * (A * C))) := by rw [Int.mul_assoc A B]
                  _ = C * (A * ((A * C) * B)) := by rw [Int.mul_comm B (A * C)]
                  _ = C * (A * (A * (C * B))) := by rw [Int.mul_assoc A C B]
                  _ = (C * A) * (A * (B * C)) := by rw [← Int.mul_assoc C A, Int.mul_comm C B]
                  _ = (A * C) * (A * (B * C)) := by rw [Int.mul_comm C A]
          _ = a.1 * b.1 * (A * C) * (A * (B * C)) := (Int.mul_assoc _ _ _).symm
      have h2 : a.1 * (c.1 * B) * (A * B * (A * C)) = a.1 * c.1 * (A * B) * (A * (B * C)) := by
        calc
          a.1 * (c.1 * B) * (A * B * (A * C))
              = (a.1 * c.1) * (B * ((A * B) * (A * C))) := by
                  rw [← Int.mul_assoc a.1 c.1 B, Int.mul_assoc (a.1 * c.1)]
          _ = (a.1 * c.1) * ((A * B) * (A * (B * C))) := by
                congr 1
                calc
                  B * ((A * B) * (A * C))
                      = ((A * B) * B) * (A * C) := by
                          rw [← Int.mul_assoc B (A * B), Int.mul_comm B (A * B)]
                  _ = (A * B) * (B * (A * C)) := Int.mul_assoc _ _ _
                  _ = (A * B) * ((B * A) * C) := by rw [← Int.mul_assoc B A C]
                  _ = (A * B) * ((A * B) * C) := by rw [Int.mul_comm B A]
                  _ = (A * B) * (A * (B * C)) := by rw [Int.mul_assoc A B C]
          _ = a.1 * c.1 * (A * B) * (A * (B * C)) := (Int.mul_assoc _ _ _).symm
      rw [h1, h2]

theorem rat_eq_iff (x y : RawQ) :
    (Quot.mk RawQRel x : RatQ) = Quot.mk RawQRel y ↔ RawQRel x y := by
  constructor
  · intro heq
    let liftProp : RatQ → Prop := Quot.lift (fun z => RawQRel x z) (by
      intro z1 z2 hz
      exact propext ⟨fun h1 => rawQRel_trans h1 hz, fun h2 => rawQRel_trans h2 (rawQRel_symm hz)⟩)
    have hxx : liftProp (Quot.mk RawQRel x) := rawQRel_refl x
    rw [heq] at hxx
    exact hxx
  · exact Quot.sound

theorem rat_one_ne_zero : ratRing.one ≠ ratRing.zero := by
  intro heq
  have hrel := (rat_eq_iff (1, 0) (0, 0)).mp heq
  unfold RawQRel at hrel
  omega

theorem natCast_ratRing (m : Nat) :
    natCast ratRing m = Quot.mk RawQRel ((m : Int), 0) := by
  induction m with
  | zero => rfl
  | succ m ih =>
      change ratAdd (natCast ratRing m) (Quot.mk RawQRel (1, 0)) =
        Quot.mk RawQRel (((m + 1 : Nat) : Int), 0)
      rw [ih]
      apply Quot.sound
      unfold RawQRel rawAdd
      dsimp only
      rw [rawDen_prod]
      omega

/-- Explicit inverse `(k!)⁻¹ ∈ ℚ` for EVERY `k ∈ ℕ`. -/
def invFactorialQ (k : Nat) : RatQ :=
  Quot.mk RawQRel (1, factorial k - 1)

theorem invFactorialQ_mul (k : Nat) :
    ratRing.mul (invFactorialQ k) (natCast ratRing (factorial k)) = ratRing.one := by
  rw [natCast_ratRing]
  apply Quot.sound
  unfold RawQRel rawMul
  have hfk : factorial k - 1 + 1 = factorial k := by
    have := factorial_pos k
    omega
  rw [rawDen_prod, hfk]
  simp

/-- Characteristic-0 Concrete Master Theorem over `ℚ` for ALL `n, k ∈ ℕ`:
    `Π_k = (1/k!) Alt_k` is an idempotent projection onto `A^k_sgn(ℚ^n)`, and both
    `Π_k` and `A^k_sgn(ℚ^n)` vanish **if and only if** `choose n k = 0` (`n < k`). -/
theorem char0_rat_positive_theorem (n k : Nat) :
    (∀ T : Tensor RatQ n k,
      normAlt ratRing (invFactorialQ k) (normAlt ratRing (invFactorialQ k) T) =
        normAlt ratRing (invFactorialQ k) T) ∧
    (∀ T : Tensor RatQ n k,
      IsAntisym ratRing T ↔ normAlt ratRing (invFactorialQ k) T = T) ∧
    ((∀ T : Tensor RatQ n k,
        normAlt ratRing (invFactorialQ k) T = zeroTensor ratRing) ↔ choose n k = 0) ∧
    ((∀ T : Tensor RatQ n k,
        IsAntisym ratRing T → T = zeroTensor ratRing) ↔ choose n k = 0) := by
  have hu := invFactorialQ_mul k
  have hmaster := positive_binomial_threshold_master (n := n) (k := k) ratRing rat_one_ne_zero hu
  exact ⟨normAlt_idem ratRing hu, isAntisym_iff_normAlt_eq ratRing hu, hmaster.1, hmaster.2⟩

/-- Field `𝔽_2` of characteristic `2`, realized on `Bool` (`xor` = `+`, `and` = `*`). -/
def f2Ring : CommRingOps Bool where
  zero := false
  one := true
  add := xor
  neg := fun x => x
  mul := and
  add_assoc := Bool.xor_assoc
  add_comm := Bool.xor_comm
  zero_add := Bool.false_xor
  add_neg := Bool.xor_self
  mul_assoc := Bool.and_assoc
  mul_comm := Bool.and_comm
  one_mul := Bool.true_and
  left_distrib := by intro a b c; cases a <;> cases b <;> cases c <;> rfl

/-! ## 2. Refutation Family 1: Characteristic 2 — Non-Vanishing of `A^k_sgn(𝔽_2^n)` for ALL `k > n` -/

/-- Over `𝔽_2`, `+1 = -1`, so `sgnVal` is the identity on all signs. -/
theorem f2_sgnVal_eq_id (b x : Bool) : sgnVal f2Ring b x = x := by
  cases b <;> rfl

/-- Over `𝔽_2`, the `S_k`-antisymmetric ("fully antisymmetric part") subspace `A^k_sgn(𝔽_2^n)`
    collapses to the `S_k`-invariant (symmetric) tensor subspace `((𝔽_2^n)^{⊗ k})^{S_k}`. -/
theorem f2_isAntisym_iff_sym {n k : Nat} (T : Tensor Bool n k) :
    IsAntisym f2Ring T ↔ ∀ σ : Perm k, actTensor σ T = T := by
  unfold IsAntisym sgnTensor
  simp only [f2_sgnVal_eq_id]

/-- Pure diagonal basis tensor `e_0^{⊗ k}` in `T^k(𝔽_2^n)` for `n ≥ 1`. -/
def diagZeroTensor {n : Nat} (hn : 0 < n) (k : Nat) : Tensor Bool n k :=
  basisTensor f2Ring (fun _ => ⟨0, hn⟩)

theorem diagZeroTensor_isAntisym {n : Nat} (hn : 0 < n) (k : Nat) :
    IsAntisym f2Ring (diagZeroTensor hn k) := by
  rw [f2_isAntisym_iff_sym]
  intro σ
  funext I
  unfold actTensor diagZeroTensor basisTensor
  have heq : vecEq (fun r => I (σ.toFun r)) (fun _ => ⟨0, hn⟩) =
      vecEq I (fun _ => ⟨0, hn⟩) := by
    cases hv : vecEq I (fun _ => ⟨0, hn⟩) with
    | true =>
        have hI := (vecEq_iff _ _).mp hv
        have hIσ : (fun r => I (σ.toFun r)) = (fun _ => ⟨0, hn⟩) := by
          funext r; exact congrFun hI (σ.toFun r)
        exact (vecEq_iff _ _).mpr hIσ
    | false =>
        cases hv2 : vecEq (fun r => I (σ.toFun r)) (fun _ => ⟨0, hn⟩) with
        | false => rfl
        | true =>
            have hIσ := (vecEq_iff _ _).mp hv2
            have hI : I = (fun _ => ⟨0, hn⟩) := by
              funext s
              calc
                I s = I (σ.toFun (σ.invFun s)) := by rw [σ.right_inv]
                _ = ⟨0, hn⟩ := congrFun hIσ (σ.invFun s)
            rw [(vecEq_iff _ _).mpr hI] at hv
            cases hv
  rw [heq]

theorem diagZeroTensor_ne_zero {n : Nat} (hn : 0 < n) (k : Nat) :
    diagZeroTensor hn k ≠ zeroTensor f2Ring := by
  intro hz
  let I0 : Fin k → Fin n := fun _ => ⟨0, hn⟩
  have hev : diagZeroTensor hn k I0 = false := congrFun hz I0
  unfold diagZeroTensor basisTensor at hev
  rw [if_pos ((vecEq_iff I0 I0).mpr rfl)] at hev
  cases hev

/-- **Refutation 1a (Global Non-Vanishing Above the Threshold in Characteristic 2):**
    For EVERY `n ≥ 1` and EVERY `k > n`, `choose n k = 0` (at a binomial zero),
    YET `A^k_sgn(𝔽_2^n)` is strictly non-zero! Thus the fully antisymmetric part
    has NO finite dimension-vanishing threshold in characteristic 2. -/
theorem refutation_char2_nonvanishing_above_threshold {n k : Nat} (hn : 0 < n) (hgt : n < k) :
    choose n k = 0 ∧ ∃ T : Tensor Bool n k, IsAntisym f2Ring T ∧ T ≠ zeroTensor f2Ring :=
  ⟨choose_eq_zero_of_lt hgt, diagZeroTensor hn k,
    diagZeroTensor_isAntisym hn k, diagZeroTensor_ne_zero hn k⟩

/-- Consequently, the unqualified statement that over every non-trivial commutative ring / field,
    `A^k_sgn(K^n)` vanishes iff `choose n k = 0` is FALSE (witnessed at `n = 2, k = 3`). -/
theorem refutation_unqualified_binomial_threshold_false :
    ¬ (∀ (R : Type) (cr : CommRingOps R), cr.one ≠ cr.zero →
        ∀ (n k : Nat),
          (∀ T : Tensor R n k, IsAntisym cr T → T = zeroTensor cr) ↔ choose n k = 0) := by
  intro hall
  have h23 := hall Bool f2Ring (by decide) 2 3
  rcases refutation_char2_nonvanishing_above_threshold (n := 2) (k := 3)
      (by omega) (by omega) with ⟨hc0, T, hT, hne⟩
  exact hne (h23.mpr hc0 T hT)

/-- Concrete Dimension Mismatch at `(n, k) = (2, 2)` over `𝔽_2`:
    `choose 2 2 = 1`, yet `A^2_sgn(𝔽_2^2)` contains three `𝔽_2`-linearly independent
    tensors (`e_0 ⊗ e_0`, `e_1 ⊗ e_1`, `e_0 ⊗ e_1 + e_1 ⊗ e_0`), giving `dim = 3 ≠ 1`. -/
def f2SymBiv00 : Tensor Bool 2 2 :=
  diagZeroTensor (Nat.succ_pos 1) 2

def f2SymBiv11 : Tensor Bool 2 2 :=
  fun I => vecEq I (fun _ => ⟨1, by omega⟩)

def f2SymBiv01 : Tensor Bool 2 2 :=
  alt f2Ring (basisTensor f2Ring (fun r : Fin 2 => ⟨r.val, r.isLt⟩))

theorem f2_dim_mismatch_n2_k2 :
    choose 2 2 = 1 ∧
    IsAntisym f2Ring f2SymBiv00 ∧
    IsAntisym f2Ring f2SymBiv11 ∧
    IsAntisym f2Ring f2SymBiv01 ∧
    (∀ c0 c1 c2 : Bool,
      (∀ I : Fin 2 → Fin 2,
        xor (xor (and c0 (f2SymBiv00 I)) (and c1 (f2SymBiv11 I))) (and c2 (f2SymBiv01 I)) =
          false) →
      c0 = false ∧ c1 = false ∧ c2 = false) := by
  refine ⟨rfl, diagZeroTensor_isAntisym (Nat.succ_pos 1) 2, ?_, alt_isAntisym f2Ring _, ?_⟩
  · rw [f2_isAntisym_iff_sym]
    intro σ
    funext I
    unfold actTensor f2SymBiv11
    cases hv : vecEq I (fun _ => ⟨1, by omega⟩) with
    | true =>
        have hI := (vecEq_iff _ _).mp hv
        exact (vecEq_iff _ _).mpr (funext fun r => congrFun hI (σ.toFun r))
    | false =>
        cases hv2 : vecEq (fun r => I (σ.toFun r)) (fun _ => ⟨1, by omega⟩) with
        | false => rfl
        | true =>
            have hIσ := (vecEq_iff _ _).mp hv2
            have hI : I = (fun _ => ⟨1, by omega⟩) := by
              funext s
              calc
                I s = I (σ.toFun (σ.invFun s)) := by rw [σ.right_inv]
                _ = ⟨1, by omega⟩ := congrFun hIσ (σ.invFun s)
            rw [(vecEq_iff _ _).mpr hI] at hv
            cases hv
  · intro c0 c1 c2 hcomb
    have e00 := hcomb (fun _ => ⟨0, by omega⟩)
    have e11 := hcomb (fun _ => ⟨1, by omega⟩)
    have e01 := hcomb (fun r : Fin 2 => ⟨r.val, r.isLt⟩)
    revert e00 e11 e01
    cases c0 <;> cases c1 <;> cases c2 <;> decide

/-! ## 3. Refutation Family 2: Breakdown of Full Antisymmetrization in Positive Characteristic -/

theorem f2_natCast_even (m : Nat) : natCast f2Ring (2 * m) = false := by
  induction m with
  | zero => rfl
  | succ m ih =>
      have h : 2 * (m + 1) = 2 * m + 2 := by omega
      rw [h, natCast_add, ih]
      rfl

theorem f2_factorial_zero_of_ge_two {k : Nat} (hk : 2 ≤ k) :
    natCast f2Ring (factorial k) = false := by
  have heven : ∃ m : Nat, factorial k = 2 * m := by
    cases k with
    | zero => omega
    | succ k1 =>
        cases k1 with
        | zero => omega
        | succ k2 =>
            induction k2 with
            | zero => exact ⟨1, rfl⟩
            | succ m ihm =>
                rcases ihm (by omega) with ⟨q, hq⟩
                refine ⟨(m + 3) * q, ?_⟩
                change (m + 3) * factorial (m + 2) = 2 * ((m + 3) * q)
                rw [hq, ← Nat.mul_assoc, Nat.mul_comm (m + 3) 2, Nat.mul_assoc]
  rcases heven with ⟨m, hm⟩
  rw [hm]
  exact f2_natCast_even m

/-- **Refutation 2a (Non-Existence of Normalized `(1/k!) Alt_k` & Universal Nilpotence `Alt_k^2 = 0`):**
    In characteristic 2, for EVERY `k ≥ 2` and `n ∈ ℕ`:
    1. `(k!)⁻¹` does not exist in `𝔽_2`;
    2. Unnormalized `Alt_k` satisfies `Alt_k ∘ Alt_k = 0` identically (nilpotent, never a projection
       whenever `Alt_k ≠ 0`, e.g. at `n = 2, k = 2` where `choose 2 2 = 1`). -/
theorem refutation_char2_nilpotent_and_no_inv {n k : Nat} (hk : 2 ≤ k) :
    (¬ ∃ u : Bool, f2Ring.mul u (natCast f2Ring (factorial k)) = f2Ring.one) ∧
    (∀ T : Tensor Bool n k, alt f2Ring (alt f2Ring T) = zeroTensor f2Ring) := by
  have hfz := f2_factorial_zero_of_ge_two hk
  refine ⟨?_, ?_⟩
  · rintro ⟨u, hu⟩
    rw [hfz] at hu
    revert u hu
    decide
  · intro T
    rw [alt_idem_scaled, hfz]
    funext _
    exact cr_zero_mul f2Ring _

theorem refutation_char2_alt2_not_projection :
    choose 2 2 = 1 ∧
    f2SymBiv01 ≠ zeroTensor f2Ring ∧
    alt f2Ring f2SymBiv01 = zeroTensor f2Ring := by
  refine ⟨rfl, ?_, (refutation_char2_nilpotent_and_no_inv (n := 2) (k := 2) (by omega)).2 _⟩
  intro hz
  have h := congrFun hz (fun r : Fin 2 => ⟨r.val, r.isLt⟩)
  revert h
  decide

/-- Tensor product `T_2 ⊗ v ∈ T^3(R^n)` of a `2`-tensor `T_2` and a `1`-vector `v`. -/
def tensor21 {R : Type} (cr : CommRingOps R) {n : Nat}
    (T2 : Tensor R n 2) (v : Tensor R n 1) : Tensor R n 3 :=
  fun I => cr.mul (T2 (fun r : Fin 2 => I ⟨r.val, by omega⟩)) (v (fun _ => I ⟨2, by omega⟩))

/-- **Refutation 2b (Premature Annihilation of Iterated Outer Product by `Alt_3` at `n = 3`):**
    Over `𝔽_2^3` (`n = 3`), `choose 3 3 = 1 ≠ 0` and `Alt_3(e_0 ⊗ e_1 ⊗ e_2) ≠ 0`,
    YET for the non-zero alternating `2`-tensor `ω_01 = Alt_2(e_0 ⊗ e_1)` and `e_2`,
    full antisymmetrization `Alt_3(ω_01 ⊗ e_2) = 0` vanishes ALREADY AT `k = 3 = n`! -/
theorem refutation_char2_iterated_alt_vanishes_at_n3 :
    let e01 : Tensor Bool 3 2 := basisTensor f2Ring (fun r : Fin 2 => ⟨r.val, by omega⟩)
    let ω01 : Tensor Bool 3 2 := alt f2Ring e01
    let e2 : Tensor Bool 3 1 := basisTensor f2Ring (fun _ => ⟨2, by omega⟩)
    let e012 : Tensor Bool 3 3 := basisTensor f2Ring (fun r : Fin 3 => r)
    choose 3 3 = 1 ∧
    ω01 ≠ zeroTensor f2Ring ∧
    alt f2Ring e012 ≠ zeroTensor f2Ring ∧
    alt f2Ring (tensor21 f2Ring ω01 e2) = zeroTensor f2Ring := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro hz
    have h := congrFun hz (fun r : Fin 2 => ⟨r.val, by omega⟩)
    revert h; decide
  · intro hz
    have h := congrFun hz (fun r : Fin 3 => r)
    revert h; decide
  · funext I
    have hdec_all : ∀ (h0 h1 h2 : Fin 3),
        alt f2Ring
          (tensor21 f2Ring
            (alt f2Ring (basisTensor f2Ring (fun r : Fin 2 => ⟨r.val, by omega⟩)))
            (basisTensor f2Ring (fun _ : Fin 1 => ⟨2, by omega⟩)))
          (fun r : Fin 3 => if r.val = 0 then h0 else if r.val = 1 then h1 else h2) = false := by
      decide
    have hIeq : I = (fun r : Fin 3 =>
        if r.val = 0 then I ⟨0, by omega⟩
        else if r.val = 1 then I ⟨1, by omega⟩
        else I ⟨2, by omega⟩) := by
      funext r
      have hr := r.isLt
      by_cases hr0 : r.val = 0
      · rw [if_pos hr0]
        exact congrArg I (Fin.ext hr0)
      · rw [if_neg hr0]
        by_cases hr1 : r.val = 1
        · rw [if_pos hr1]
          exact congrArg I (Fin.ext hr1)
        · rw [if_neg hr1]
          have hr2 : r.val = 2 := by omega
          exact congrArg I (Fin.ext hr2)
    rw [hIeq]
    exact hdec_all (I ⟨0, by omega⟩) (I ⟨1, by omega⟩) (I ⟨2, by omega⟩)

/-- **Refutation 2c (Modular Lucas Binomial Zeros vs Exterior Dimension):**
    At `n = 2, k = 1` (and `n = 4, k = 2`), `choose n k` vanishes in `𝔽_2` (`natCast = 0`),
    yet `(strictIncLists n k).length = choose n k > 0` and `Alt_k ≠ 0` over `𝔽_2^n`. -/
theorem refutation_modular_binomial_zeros_f2 :
    (natCast f2Ring (choose 2 1) = f2Ring.zero ∧
      (strictIncLists 2 1).length = 2 ∧
      ∃ T : Tensor Bool 2 1, alt f2Ring T ≠ zeroTensor f2Ring) ∧
    (natCast f2Ring (choose 4 2) = f2Ring.zero ∧
      (strictIncLists 4 2).length = 6 ∧
      ∃ T : Tensor Bool 4 2, alt f2Ring T ≠ zeroTensor f2Ring) := by
  refine ⟨⟨by decide, by decide, alt_nonvanishing_of_le f2Ring (by decide) (by omega)⟩,
          ⟨by decide, by decide, alt_nonvanishing_of_le f2Ring (by decide) (by omega)⟩⟩

/-! ## 4. Refutation Family 3: Characteristic-0 Multivectors in `Λ(ℚ^n)` and `Cl_{n,0}(ℚ)` -/

/-- Basis blades of `Λ(R^n)` and `Cl_{n,0}(R)` encoded as bitmasks `Fin (2^n)`. -/
abbrev Multivector (R : Type) (n : Nat) : Type := Fin (2 ^ n) → R

def bitSet (mask bit : Nat) : Bool :=
  ((mask >>> bit) &&& 1) == 1

def popcount : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, mask => (if bitSet mask n then 1 else 0) + popcount n mask

/-- Koszul swap parity when commuting basis blade `a` past basis blade `b`. -/
def koszulBladeParity (n a b : Nat) : Bool :=
  listSum xorMonoid (finList n) (fun i =>
    if bitSet a i.val then
      listSum xorMonoid (finList n) (fun j =>
        decide (j.val < i.val) && bitSet b j.val)
    else false)

def mvZero {R : Type} (cr : CommRingOps R) {n : Nat} : Multivector R n :=
  fun _ => cr.zero

def mvSub {R : Type} (cr : CommRingOps R) {n : Nat} (A B : Multivector R n) : Multivector R n :=
  fun m => cr.add (A m) (cr.neg (B m))

def mvSmul {R : Type} (cr : CommRingOps R) {n : Nat} (c : R) (A : Multivector R n) :
    Multivector R n :=
  fun m => cr.mul c (A m)

def basisBlade {R : Type} (cr : CommRingOps R) {n : Nat} (mask : Fin (2 ^ n)) : Multivector R n :=
  fun m => if m = mask then cr.one else cr.zero

/-- Exterior (Grassmann wedge) product `A ∧ B` in `Λ(R^n)`. -/
def wedge {R : Type} (cr : CommRingOps R) {n : Nat} (A B : Multivector R n) : Multivector R n :=
  fun out =>
    listSum cr.toAddMonoid (finList (2 ^ n)) (fun a =>
      listSum cr.toAddMonoid (finList (2 ^ n)) (fun b =>
        if (a.val &&& b.val) == 0 && (a.val ||| b.val) == out.val then
          sgnVal cr (koszulBladeParity n a.val b.val) (cr.mul (A a) (B b))
        else cr.zero))

/-- Euclidean Clifford geometric product `A B` in `Cl_{n,0}(R)` (`e_i^2 = +1`). -/
def cliffMul {R : Type} (cr : CommRingOps R) {n : Nat} (A B : Multivector R n) : Multivector R n :=
  fun out =>
    listSum cr.toAddMonoid (finList (2 ^ n)) (fun a =>
      listSum cr.toAddMonoid (finList (2 ^ n)) (fun b =>
        if (a.val ^^^ b.val) == out.val then
          sgnVal cr (koszulBladeParity n a.val b.val) (cr.mul (A a) (B b))
        else cr.zero))

/-- Homogeneous grade-`g` projection `⟨M⟩_g` in `Cl_{n,0}(R)`. -/
def gradeProj {R : Type} (cr : CommRingOps R) {n : Nat} (g : Nat) (M : Multivector R n) :
    Multivector R n :=
  fun m => if popcount n m.val == g then M m else cr.zero

def intToRat (z : Int) : RatQ := Quot.mk RawQRel (z, 0)

def halfQ : RatQ := Quot.mk RawQRel (1, 1)

theorem intToRat_zero : intToRat 0 = ratRing.zero := rfl

theorem intToRat_ne_zero {z : Int} (hz : z ≠ 0) : intToRat z ≠ ratRing.zero := by
  intro heq
  have hrel := (rat_eq_iff (z, 0) (0, 0)).mp heq
  unfold RawQRel at hrel
  omega

theorem intToRat_add (x y : Int) : intToRat (x + y) = ratRing.add (intToRat x) (intToRat y) := by
  apply Quot.sound
  unfold RawQRel rawAdd
  rw [rawDen_prod]
  simp

theorem intToRat_neg (x : Int) : intToRat (-x) = ratRing.neg (intToRat x) := rfl

theorem intToRat_mul (x y : Int) : intToRat (x * y) = ratRing.mul (intToRat x) (intToRat y) := by
  apply Quot.sound
  unfold RawQRel rawMul
  rw [rawDen_prod]
  simp

theorem intToRat_sgnVal (b : Bool) (x : Int) :
    intToRat (sgnVal intRing b x) = sgnVal ratRing b (intToRat x) := by
  cases b <;> rfl

theorem intToRat_listSum {α : Type} (f : α → Int) :
    ∀ (l : List α),
      intToRat (listSum intRing.toAddMonoid l f) =
        listSum ratRing.toAddMonoid l (fun x => intToRat (f x))
  | [] => rfl
  | a :: t => by
      simp only [listSum]
      change intToRat (f a + listSum intRing.toAddMonoid t f) =
        ratRing.add (intToRat (f a)) (listSum ratRing.toAddMonoid t (fun x => intToRat (f x)))
      rw [intToRat_add, intToRat_listSum f t]

def liftMv {n : Nat} (M : Multivector Int n) : Multivector RatQ n :=
  fun m => intToRat (M m)

theorem liftMv_basisBlade {n : Nat} (mask : Fin (2 ^ n)) :
    liftMv (basisBlade intRing mask) = basisBlade ratRing mask := by
  funext m
  unfold liftMv basisBlade
  split <;> rfl

theorem liftMv_wedge {n : Nat} (A B : Multivector Int n) :
    liftMv (wedge intRing A B) = wedge ratRing (liftMv A) (liftMv B) := by
  funext out
  unfold liftMv wedge
  rw [intToRat_listSum]
  apply listSum_congr ratRing.toAddMonoid
  intro a _
  rw [intToRat_listSum]
  apply listSum_congr ratRing.toAddMonoid
  intro b _
  split
  · rw [intToRat_sgnVal]
    change sgnVal ratRing _ (intToRat (A a * B b)) =
      sgnVal ratRing _ (ratRing.mul (intToRat (A a)) (intToRat (B b)))
    rw [intToRat_mul]
  · rfl

theorem liftMv_cliffMul {n : Nat} (A B : Multivector Int n) :
    liftMv (cliffMul intRing A B) = cliffMul ratRing (liftMv A) (liftMv B) := by
  funext out
  unfold liftMv cliffMul
  rw [intToRat_listSum]
  apply listSum_congr ratRing.toAddMonoid
  intro a _
  rw [intToRat_listSum]
  apply listSum_congr ratRing.toAddMonoid
  intro b _
  split
  · rw [intToRat_sgnVal]
    change sgnVal ratRing _ (intToRat (A a * B b)) =
      sgnVal ratRing _ (ratRing.mul (intToRat (A a)) (intToRat (B b)))
    rw [intToRat_mul]
  · rfl

theorem liftMv_sub {n : Nat} (A B : Multivector Int n) :
    liftMv (mvSub intRing A B) = mvSub ratRing (liftMv A) (liftMv B) := by
  funext m
  unfold liftMv mvSub
  change intToRat (A m + -B m) = _
  rw [intToRat_add, intToRat_neg]

theorem liftMv_gradeProj {n : Nat} (g : Nat) (M : Multivector Int n) :
    liftMv (gradeProj intRing g M) = gradeProj ratRing g (liftMv M) := by
  funext m
  unfold liftMv gradeProj
  split <;> rfl

theorem halfQ_mul_two_intToRat (z : Int) :
    ratRing.mul halfQ (intToRat (2 * z)) = intToRat z := by
  apply Quot.sound
  unfold RawQRel rawMul
  rw [rawDen_prod]
  omega

/-- **Refutation 3a (Characteristic 0, `n = 4`, Premature Vanishing at the Threshold `2 + 2 = 4`):**
    In `Λ(ℚ^4)` / `Cl_{4,0}(ℚ)`, `choose 4 4 = 1 ≠ 0`. For the two grade-2 bivectors
    `A = e_0 ∧ e_1` (mask `3 = 0b0011`) and `B = e_2 ∧ e_3` (mask `12 = 0b1100`):
    - The true outer product `A ∧ B = ⟨A B⟩_4 = e_0 ∧ e_1 ∧ e_2 ∧ e_3` (mask `15`) is NON-ZERO;
    - Yet factor antisymmetrization `(1/2)(A ∧ B - B ∧ A) = 0` and `(1/2)(A B - B A) = 0`
      vanishes prematurely at `k = 4 = n`! -/
theorem refutation_char0_bivector_premature_vanishing_n4 :
    let A : Multivector RatQ 4 := basisBlade ratRing ⟨3, by omega⟩
    let B : Multivector RatQ 4 := basisBlade ratRing ⟨12, by omega⟩
    choose 4 4 = 1 ∧
    wedge ratRing A B ≠ mvZero ratRing ∧
    gradeProj ratRing 4 (cliffMul ratRing A B) = wedge ratRing A B ∧
    mvSmul ratRing halfQ (mvSub ratRing (wedge ratRing A B) (wedge ratRing B A)) =
      mvZero ratRing ∧
    mvSmul ratRing halfQ (mvSub ratRing (cliffMul ratRing A B) (cliffMul ratRing B A)) =
      mvZero ratRing := by
  let Ai : Multivector Int 4 := basisBlade intRing ⟨3, by omega⟩
  let Bi : Multivector Int 4 := basisBlade intRing ⟨12, by omega⟩
  have hA : liftMv Ai = basisBlade ratRing ⟨3, by omega⟩ := liftMv_basisBlade _
  have hB : liftMv Bi = basisBlade ratRing ⟨12, by omega⟩ := liftMv_basisBlade _
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · intro hz
    have hval : wedge ratRing (liftMv Ai) (liftMv Bi) ⟨15, by omega⟩ = ratRing.zero := by
      rw [hA, hB]; exact congrFun hz ⟨15, by omega⟩
    rw [← liftMv_wedge] at hval
    have h1 : wedge intRing Ai Bi ⟨15, by omega⟩ = 1 := by decide
    unfold liftMv at hval
    rw [h1] at hval
    exact rat_one_ne_zero hval
  · rw [← hA, ← hB, ← liftMv_cliffMul, ← liftMv_gradeProj, ← liftMv_wedge]
    apply congrArg liftMv
    funext m
    revert m; decide
  · rw [← hA, ← hB, ← liftMv_wedge, ← liftMv_wedge, ← liftMv_sub]
    funext m
    have hz : mvSub intRing (wedge intRing Ai Bi) (wedge intRing Bi Ai) m = 0 := by
      revert m; decide
    unfold mvSmul liftMv
    rw [hz, intToRat_zero, cr_mul_zero]
    rfl
  · rw [← hA, ← hB, ← liftMv_cliffMul, ← liftMv_cliffMul, ← liftMv_sub]
    funext m
    have hz : mvSub intRing (cliffMul intRing Ai Bi) (cliffMul intRing Bi Ai) m = 0 := by
      revert m; decide
    unfold mvSmul liftMv
    rw [hz, intToRat_zero, cr_mul_zero]
    rfl

/-- **Refutation 3b (Characteristic 0, `n = 3`, Failure to Vanish Above Threshold `2 + 2 = 4 > 3`):**
    In `Cl_{3,0}(ℚ)`, at total grade `2 + 2 = 4 > 3`, `choose 3 4 = 0`, and the true outer
    product `A ∧ B = ⟨A B⟩_4 = 0` vanishes for `A = e_0 e_1` (mask `3`) and `B = e_1 e_2` (mask `6`),
    YET the antisymmetrized Clifford product `(1/2)(A B - B A) = e_0 e_2` (mask `5`) is NON-ZERO! -/
theorem refutation_char0_bivector_nonvanishing_above_n3 :
    let A : Multivector RatQ 3 := basisBlade ratRing ⟨3, by omega⟩
    let B : Multivector RatQ 3 := basisBlade ratRing ⟨6, by omega⟩
    let e02 : Multivector RatQ 3 := basisBlade ratRing ⟨5, by omega⟩
    choose 3 4 = 0 ∧
    wedge ratRing A B = mvZero ratRing ∧
    gradeProj ratRing 4 (cliffMul ratRing A B) = mvZero ratRing ∧
    mvSmul ratRing halfQ (mvSub ratRing (cliffMul ratRing A B) (cliffMul ratRing B A)) = e02 ∧
    e02 ≠ mvZero ratRing := by
  let Ai : Multivector Int 3 := basisBlade intRing ⟨3, by omega⟩
  let Bi : Multivector Int 3 := basisBlade intRing ⟨6, by omega⟩
  have hA : liftMv Ai = basisBlade ratRing ⟨3, by omega⟩ := liftMv_basisBlade _
  have hB : liftMv Bi = basisBlade ratRing ⟨6, by omega⟩ := liftMv_basisBlade _
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · rw [← hA, ← hB, ← liftMv_wedge]
    funext m
    have hz : wedge intRing Ai Bi m = 0 := by revert m; decide
    unfold liftMv
    rw [hz]; rfl
  · rw [← hA, ← hB, ← liftMv_cliffMul, ← liftMv_gradeProj]
    funext m
    have hz : gradeProj intRing 4 (cliffMul intRing Ai Bi) m = 0 := by revert m; decide
    unfold liftMv
    rw [hz]; rfl
  · rw [← hA, ← hB, ← liftMv_cliffMul, ← liftMv_cliffMul, ← liftMv_sub,
      ← liftMv_basisBlade ⟨5, by omega⟩]
    funext m
    have h2 : mvSub intRing (cliffMul intRing Ai Bi) (cliffMul intRing Bi Ai) m =
        2 * basisBlade intRing ⟨5, by omega⟩ m := by
      revert m; decide
    unfold mvSmul liftMv
    rw [h2, halfQ_mul_two_intToRat]
  · intro hz
    have h := congrFun hz ⟨5, by omega⟩
    unfold basisBlade mvZero at h
    simp at h
    exact rat_one_ne_zero h

end Conjecture00000007602
