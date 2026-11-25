/-
  SpinorMinimalIdeals/PositiveSplitCl11.lean
  1. Unified parametric Clifford algebras `Cl1 q1` (`dim = 2`, `n = 1`) and
     `Cl2 q1 q2` (`dim = 4`, `n = 2`) over `ℚ`, proving the unital associative
     `ℚ`-algebra laws and the quadratic Clifford identity `v * v = Q(v) • 1`.
  2. Positive Non-Vacuity Theorem in even split signature `Cl_{1,1}(ℚ) = Cl2 1 (-1) ≅ M_2(ℚ)`
     (`n = 2`, `2^(n/2) = 2`):
       - Explicit `ℚ`-algebra isomorphism `Φ_{1,1} : Cl_{1,1}(ℚ) ≅ M_2(ℚ)`,
       - Primitive idempotent `e = (1 + e_1)/2` and minimal left ideal `S_{1,1} = Cl_{1,1} · e`,
       - Exact dimension `HasQDim Cl11Alg S_{1,1} 2` (`= 2^(2/2)`),
       - Faithfulness of `S_{1,1}` and surjectivity of left multiplication onto `M_2(ℚ)`,
       - Complete `{+1, -1}` weight spectrum of the Cartan generator `e_1` on `S_{1,1}`,
       - Matrix realization of `S_{1,1}` as the exact first-column subspace of `M_2(ℚ)`,
       - Contrast with minimal *two-sided* ideals: `Cl_{1,1}(ℚ)` is a simple ring whose unique
         minimal nonzero two-sided ideal is the full 4-dimensional algebra (`dim = 4 ≠ 2`).
-/

import SpinorMinimalIdeals.AlgebraicFramework

namespace SpinorMinimalIdeals

open PolyNorm

/-! ### 1-Dimensional Parametric Clifford Algebra `Cl1 q1` (`e_1^2 = q1`) -/

structure Cl1 (q1 : RatQ) where
  a0 : RatQ
  a1 : RatQ

instance {q1 : RatQ} : DecidableEq (Cl1 q1) := fun x y =>
  if h : x.a0 = y.a0 ∧ x.a1 = y.a1 then
    isTrue (by cases x; cases y; cases h.1; cases h.2; rfl)
  else
    isFalse (fun heq => by subst heq; exact h ⟨rfl, rfl⟩)

namespace Cl1

def zero (q1 : RatQ) : Cl1 q1 := ⟨0, 0⟩
def one (q1 : RatQ) : Cl1 q1 := ⟨1, 0⟩
def e1 (q1 : RatQ) : Cl1 q1 := ⟨0, 1⟩
def add {q1 : RatQ} (x y : Cl1 q1) : Cl1 q1 := ⟨x.a0 + y.a0, x.a1 + y.a1⟩
def neg {q1 : RatQ} (x : Cl1 q1) : Cl1 q1 := ⟨-x.a0, -x.a1⟩
def smul {q1 : RatQ} (r : RatQ) (x : Cl1 q1) : Cl1 q1 := ⟨r * x.a0, r * x.a1⟩
def mul {q1 : RatQ} (x y : Cl1 q1) : Cl1 q1 :=
  ⟨x.a0 * y.a0 + q1 * x.a1 * y.a1, x.a0 * y.a1 + x.a1 * y.a0⟩

theorem ext {q1 : RatQ} {x y : Cl1 q1} (h0 : x.a0 = y.a0) (h1 : x.a1 = y.a1) : x = y := by
  cases x; cases y; simp_all

def alg (q1 : RatQ) : QAlgebra (Cl1 q1) where
  zero := zero q1
  one  := one q1
  add  := add
  neg  := neg
  mul  := mul
  smul := smul
  add_assoc x y z := ext (RatQ.add_assoc _ _ _) (RatQ.add_assoc _ _ _)
  add_comm x y    := ext (RatQ.add_comm _ _) (RatQ.add_comm _ _)
  zero_add x      := ext (RatQ.zero_add _) (RatQ.zero_add _)
  add_zero x      := ext (RatQ.add_zero _) (RatQ.add_zero _)
  neg_add x       := ext (RatQ.neg_add_cancel _) (RatQ.neg_add_cancel _)
  mul_assoc x y z := by
    apply ext
    · exact RatQ.eqQ_of_norm_eq [q1, x.a0, x.a1, y.a0, y.a1, z.a0, z.a1]
        (.add (.mul (.add (.mul (.var 1) (.var 3)) (.mul (.mul (.var 0) (.var 2)) (.var 4))) (.var 5))
              (.mul (.mul (.var 0) (.add (.mul (.var 1) (.var 4)) (.mul (.var 2) (.var 3)))) (.var 6)))
        (.add (.mul (.var 1) (.add (.mul (.var 3) (.var 5)) (.mul (.mul (.var 0) (.var 4)) (.var 6))))
              (.mul (.mul (.var 0) (.var 2)) (.add (.mul (.var 3) (.var 6)) (.mul (.var 4) (.var 5))))) (by decide)
    · exact RatQ.eqQ_of_norm_eq [q1, x.a0, x.a1, y.a0, y.a1, z.a0, z.a1]
        (.add (.mul (.add (.mul (.var 1) (.var 3)) (.mul (.mul (.var 0) (.var 2)) (.var 4))) (.var 6))
              (.mul (.add (.mul (.var 1) (.var 4)) (.mul (.var 2) (.var 3))) (.var 5)))
        (.add (.mul (.var 1) (.add (.mul (.var 3) (.var 6)) (.mul (.var 4) (.var 5))))
              (.mul (.var 2) (.add (.mul (.var 3) (.var 5)) (.mul (.mul (.var 0) (.var 4)) (.var 6))))) (by decide)
  one_mul x := by
    apply ext
    · exact RatQ.eqQ_of_norm_eq [q1, x.a0, x.a1]
        (.add (.mul (.const 1) (.var 1)) (.mul (.mul (.var 0) (.const 0)) (.var 2))) (.var 1) (by decide)
    · exact RatQ.eqQ_of_norm_eq [q1, x.a0, x.a1]
        (.add (.mul (.const 1) (.var 2)) (.mul (.const 0) (.var 1))) (.var 2) (by decide)
  mul_one x := by
    apply ext
    · exact RatQ.eqQ_of_norm_eq [q1, x.a0, x.a1]
        (.add (.mul (.var 1) (.const 1)) (.mul (.mul (.var 0) (.var 2)) (.const 0))) (.var 1) (by decide)
    · exact RatQ.eqQ_of_norm_eq [q1, x.a0, x.a1]
        (.add (.mul (.var 1) (.const 0)) (.mul (.var 2) (.const 1))) (.var 2) (by decide)
  left_distrib x y z := by
    apply ext
    · exact RatQ.eqQ_of_norm_eq [q1, x.a0, x.a1, y.a0, y.a1, z.a0, z.a1]
        (.add (.mul (.var 1) (.add (.var 3) (.var 5)))
              (.mul (.mul (.var 0) (.var 2)) (.add (.var 4) (.var 6))))
        (.add (.add (.mul (.var 1) (.var 3)) (.mul (.mul (.var 0) (.var 2)) (.var 4)))
              (.add (.mul (.var 1) (.var 5)) (.mul (.mul (.var 0) (.var 2)) (.var 6)))) (by decide)
    · exact RatQ.eqQ_of_norm_eq [q1, x.a0, x.a1, y.a0, y.a1, z.a0, z.a1]
        (.add (.mul (.var 1) (.add (.var 4) (.var 6)))
              (.mul (.var 2) (.add (.var 3) (.var 5))))
        (.add (.add (.mul (.var 1) (.var 4)) (.mul (.var 2) (.var 3)))
              (.add (.mul (.var 1) (.var 6)) (.mul (.var 2) (.var 5)))) (by decide)
  right_distrib x y z := by
    apply ext
    · exact RatQ.eqQ_of_norm_eq [q1, x.a0, x.a1, y.a0, y.a1, z.a0, z.a1]
        (.add (.mul (.add (.var 1) (.var 3)) (.var 5))
              (.mul (.mul (.var 0) (.add (.var 2) (.var 4))) (.var 6)))
        (.add (.add (.mul (.var 1) (.var 5)) (.mul (.mul (.var 0) (.var 2)) (.var 6)))
              (.add (.mul (.var 3) (.var 5)) (.mul (.mul (.var 0) (.var 4)) (.var 6)))) (by decide)
    · exact RatQ.eqQ_of_norm_eq [q1, x.a0, x.a1, y.a0, y.a1, z.a0, z.a1]
        (.add (.mul (.add (.var 1) (.var 3)) (.var 6))
              (.mul (.add (.var 2) (.var 4)) (.var 5)))
        (.add (.add (.mul (.var 1) (.var 6)) (.mul (.var 2) (.var 5)))
              (.add (.mul (.var 3) (.var 6)) (.mul (.var 4) (.var 5)))) (by decide)
  one_smul x := ext (RatQ.one_mul _) (RatQ.one_mul _)
  mul_smul r s x := ext (RatQ.mul_assoc _ _ _) (RatQ.mul_assoc _ _ _)
  smul_add r x y := ext (RatQ.left_distrib _ _ _) (RatQ.left_distrib _ _ _)
  add_smul r s x := ext (RatQ.right_distrib _ _ _) (RatQ.right_distrib _ _ _)
  zero_smul x := ext (RatQ.zero_mul _) (RatQ.zero_mul _)
  smul_mul_left r x y := by
    apply ext
    · exact RatQ.eqQ_of_norm_eq [r, q1, x.a0, x.a1, y.a0, y.a1]
        (.add (.mul (.mul (.var 0) (.var 2)) (.var 4))
              (.mul (.mul (.var 1) (.mul (.var 0) (.var 3))) (.var 5)))
        (.mul (.var 0) (.add (.mul (.var 2) (.var 4)) (.mul (.mul (.var 1) (.var 3)) (.var 5)))) (by decide)
    · exact RatQ.eqQ_of_norm_eq [r, q1, x.a0, x.a1, y.a0, y.a1]
        (.add (.mul (.mul (.var 0) (.var 2)) (.var 5))
              (.mul (.mul (.var 0) (.var 3)) (.var 4)))
        (.mul (.var 0) (.add (.mul (.var 2) (.var 5)) (.mul (.var 3) (.var 4)))) (by decide)

theorem clifford_rel (q1 x1 : RatQ) :
    mul (smul x1 (e1 q1)) (smul x1 (e1 q1)) = smul (q1 * (x1 * x1)) (one q1) := by
  apply ext
  · exact RatQ.eqQ_of_norm_eq [q1, x1]
      (.add (.mul (.mul (.var 1) (.const 0)) (.mul (.var 1) (.const 0)))
            (.mul (.mul (.var 0) (.mul (.var 1) (.const 1))) (.mul (.var 1) (.const 1))))
      (.mul (.mul (.var 0) (.mul (.var 1) (.var 1))) (.const 1)) (by decide)
  · exact RatQ.eqQ_of_norm_eq [q1, x1]
      (.add (.mul (.mul (.var 1) (.const 0)) (.mul (.var 1) (.const 1)))
            (.mul (.mul (.var 1) (.const 1)) (.mul (.var 1) (.const 0))))
      (.mul (.mul (.var 0) (.mul (.var 1) (.var 1))) (.const 0)) (by decide)

end Cl1

/-! ### 2-Dimensional Parametric Clifford Algebra `Cl2 q1 q2` (`e_1^2 = q1`, `e_2^2 = q2`) -/

structure Cl2 (q1 q2 : RatQ) where
  a0  : RatQ
  a1  : RatQ
  a2  : RatQ
  a12 : RatQ

instance {q1 q2 : RatQ} : DecidableEq (Cl2 q1 q2) := fun x y =>
  if h : x.a0 = y.a0 ∧ x.a1 = y.a1 ∧ x.a2 = y.a2 ∧ x.a12 = y.a12 then
    isTrue (by
      rcases h with ⟨h0, h1, h2, h12⟩
      cases x; cases y; cases h0; cases h1; cases h2; cases h12; rfl)
  else
    isFalse (fun heq => by subst heq; exact h ⟨rfl, rfl, rfl, rfl⟩)

namespace Cl2

def zero (q1 q2 : RatQ) : Cl2 q1 q2 := ⟨0, 0, 0, 0⟩
def one (q1 q2 : RatQ) : Cl2 q1 q2 := ⟨1, 0, 0, 0⟩
def e1 (q1 q2 : RatQ) : Cl2 q1 q2 := ⟨0, 1, 0, 0⟩
def e2 (q1 q2 : RatQ) : Cl2 q1 q2 := ⟨0, 0, 1, 0⟩
def e12 (q1 q2 : RatQ) : Cl2 q1 q2 := ⟨0, 0, 0, 1⟩

def add {q1 q2 : RatQ} (x y : Cl2 q1 q2) : Cl2 q1 q2 :=
  ⟨x.a0 + y.a0, x.a1 + y.a1, x.a2 + y.a2, x.a12 + y.a12⟩

def neg {q1 q2 : RatQ} (x : Cl2 q1 q2) : Cl2 q1 q2 :=
  ⟨-x.a0, -x.a1, -x.a2, -x.a12⟩

def smul {q1 q2 : RatQ} (r : RatQ) (x : Cl2 q1 q2) : Cl2 q1 q2 :=
  ⟨r * x.a0, r * x.a1, r * x.a2, r * x.a12⟩

def mul {q1 q2 : RatQ} (x y : Cl2 q1 q2) : Cl2 q1 q2 :=
  ⟨x.a0 * y.a0 + q1 * x.a1 * y.a1 + q2 * x.a2 * y.a2 - q1 * q2 * x.a12 * y.a12,
   x.a0 * y.a1 + x.a1 * y.a0 - q2 * x.a2 * y.a12 + q2 * x.a12 * y.a2,
   x.a0 * y.a2 + q1 * x.a1 * y.a12 + x.a2 * y.a0 - q1 * x.a12 * y.a1,
   x.a0 * y.a12 + x.a1 * y.a2 - x.a2 * y.a1 + x.a12 * y.a0⟩

theorem ext {q1 q2 : RatQ} {x y : Cl2 q1 q2}
    (h0 : x.a0 = y.a0) (h1 : x.a1 = y.a1) (h2 : x.a2 = y.a2) (h12 : x.a12 = y.a12) :
    x = y := by
  cases x; cases y; simp_all

/- Symbolic helpers for `Cl2.mul` in `PExpr` (`q1 = var 0`, `q2 = var 1`). -/
private def pMul0 (q1 q2 x0 x1 x2 x3 y0 y1 y2 y3 : PExpr) : PExpr :=
  .sub (.add (.add (.mul x0 y0) (.mul (.mul q1 x1) y1)) (.mul (.mul q2 x2) y2))
       (.mul (.mul (.mul q1 q2) x3) y3)

private def pMul1 (_q1 q2 x0 x1 x2 x3 y0 y1 y2 y3 : PExpr) : PExpr :=
  .add (.sub (.add (.mul x0 y1) (.mul x1 y0)) (.mul (.mul q2 x2) y3))
       (.mul (.mul q2 x3) y2)

private def pMul2 (q1 _q2 x0 x1 x2 x3 y0 y1 y2 y3 : PExpr) : PExpr :=
  .sub (.add (.add (.mul x0 y2) (.mul (.mul q1 x1) y3)) (.mul x2 y0))
       (.mul (.mul q1 x3) y1)

private def pMul3 (_q1 _q2 x0 x1 x2 x3 y0 y1 y2 y3 : PExpr) : PExpr :=
  .add (.sub (.add (.mul x0 y3) (.mul x1 y2)) (.mul x2 y1))
       (.mul x3 y0)

def alg (q1 q2 : RatQ) : QAlgebra (Cl2 q1 q2) where
  zero := zero q1 q2
  one  := one q1 q2
  add  := add
  neg  := neg
  mul  := mul
  smul := smul
  add_assoc x y z := ext (RatQ.add_assoc _ _ _) (RatQ.add_assoc _ _ _)
                         (RatQ.add_assoc _ _ _) (RatQ.add_assoc _ _ _)
  add_comm x y    := ext (RatQ.add_comm _ _) (RatQ.add_comm _ _)
                         (RatQ.add_comm _ _) (RatQ.add_comm _ _)
  zero_add x      := ext (RatQ.zero_add _) (RatQ.zero_add _)
                         (RatQ.zero_add _) (RatQ.zero_add _)
  add_zero x      := ext (RatQ.add_zero _) (RatQ.add_zero _)
                         (RatQ.add_zero _) (RatQ.add_zero _)
  neg_add x       := ext (RatQ.neg_add_cancel _) (RatQ.neg_add_cancel _)
                         (RatQ.neg_add_cancel _) (RatQ.neg_add_cancel _)
  mul_assoc x y z := by
    let env := [q1, q2, x.a0, x.a1, x.a2, x.a12, y.a0, y.a1, y.a2, y.a12, z.a0, z.a1, z.a2, z.a12]
    let pq1 := PExpr.var 0; let pq2 := PExpr.var 1
    let ax0 := PExpr.var 2; let ax1 := PExpr.var 3; let ax2 := PExpr.var 4; let ax3 := PExpr.var 5
    let by0 := PExpr.var 6; let by1 := PExpr.var 7; let by2 := PExpr.var 8; let by3 := PExpr.var 9
    let cz0 := PExpr.var 10; let cz1 := PExpr.var 11; let cz2 := PExpr.var 12; let cz3 := PExpr.var 13
    let xy0 := pMul0 pq1 pq2 ax0 ax1 ax2 ax3 by0 by1 by2 by3
    let xy1 := pMul1 pq1 pq2 ax0 ax1 ax2 ax3 by0 by1 by2 by3
    let xy2 := pMul2 pq1 pq2 ax0 ax1 ax2 ax3 by0 by1 by2 by3
    let xy3 := pMul3 pq1 pq2 ax0 ax1 ax2 ax3 by0 by1 by2 by3
    let yz0 := pMul0 pq1 pq2 by0 by1 by2 by3 cz0 cz1 cz2 cz3
    let yz1 := pMul1 pq1 pq2 by0 by1 by2 by3 cz0 cz1 cz2 cz3
    let yz2 := pMul2 pq1 pq2 by0 by1 by2 by3 cz0 cz1 cz2 cz3
    let yz3 := pMul3 pq1 pq2 by0 by1 by2 by3 cz0 cz1 cz2 cz3
    refine ext ?_ ?_ ?_ ?_
    · exact RatQ.eqQ_of_norm_eq env
        (pMul0 pq1 pq2 xy0 xy1 xy2 xy3 cz0 cz1 cz2 cz3)
        (pMul0 pq1 pq2 ax0 ax1 ax2 ax3 yz0 yz1 yz2 yz3) (by decide)
    · exact RatQ.eqQ_of_norm_eq env
        (pMul1 pq1 pq2 xy0 xy1 xy2 xy3 cz0 cz1 cz2 cz3)
        (pMul1 pq1 pq2 ax0 ax1 ax2 ax3 yz0 yz1 yz2 yz3) (by decide)
    · exact RatQ.eqQ_of_norm_eq env
        (pMul2 pq1 pq2 xy0 xy1 xy2 xy3 cz0 cz1 cz2 cz3)
        (pMul2 pq1 pq2 ax0 ax1 ax2 ax3 yz0 yz1 yz2 yz3) (by decide)
    · exact RatQ.eqQ_of_norm_eq env
        (pMul3 pq1 pq2 xy0 xy1 xy2 xy3 cz0 cz1 cz2 cz3)
        (pMul3 pq1 pq2 ax0 ax1 ax2 ax3 yz0 yz1 yz2 yz3) (by decide)
  one_mul x := by
    let env := [q1, q2, x.a0, x.a1, x.a2, x.a12]
    refine ext ?_ ?_ ?_ ?_
    · exact RatQ.eqQ_of_norm_eq env
        (pMul0 (.var 0) (.var 1) (.const 1) (.const 0) (.const 0) (.const 0) (.var 2) (.var 3) (.var 4) (.var 5))
        (.var 2) (by decide)
    · exact RatQ.eqQ_of_norm_eq env
        (pMul1 (.var 0) (.var 1) (.const 1) (.const 0) (.const 0) (.const 0) (.var 2) (.var 3) (.var 4) (.var 5))
        (.var 3) (by decide)
    · exact RatQ.eqQ_of_norm_eq env
        (pMul2 (.var 0) (.var 1) (.const 1) (.const 0) (.const 0) (.const 0) (.var 2) (.var 3) (.var 4) (.var 5))
        (.var 4) (by decide)
    · exact RatQ.eqQ_of_norm_eq env
        (pMul3 (.var 0) (.var 1) (.const 1) (.const 0) (.const 0) (.const 0) (.var 2) (.var 3) (.var 4) (.var 5))
        (.var 5) (by decide)
  mul_one x := by
    let env := [q1, q2, x.a0, x.a1, x.a2, x.a12]
    refine ext ?_ ?_ ?_ ?_
    · exact RatQ.eqQ_of_norm_eq env
        (pMul0 (.var 0) (.var 1) (.var 2) (.var 3) (.var 4) (.var 5) (.const 1) (.const 0) (.const 0) (.const 0))
        (.var 2) (by decide)
    · exact RatQ.eqQ_of_norm_eq env
        (pMul1 (.var 0) (.var 1) (.var 2) (.var 3) (.var 4) (.var 5) (.const 1) (.const 0) (.const 0) (.const 0))
        (.var 3) (by decide)
    · exact RatQ.eqQ_of_norm_eq env
        (pMul2 (.var 0) (.var 1) (.var 2) (.var 3) (.var 4) (.var 5) (.const 1) (.const 0) (.const 0) (.const 0))
        (.var 4) (by decide)
    · exact RatQ.eqQ_of_norm_eq env
        (pMul3 (.var 0) (.var 1) (.var 2) (.var 3) (.var 4) (.var 5) (.const 1) (.const 0) (.const 0) (.const 0))
        (.var 5) (by decide)
  left_distrib x y z := by
    let env := [q1, q2, x.a0, x.a1, x.a2, x.a12, y.a0, y.a1, y.a2, y.a12, z.a0, z.a1, z.a2, z.a12]
    let pq1 := PExpr.var 0; let pq2 := PExpr.var 1
    let ax0 := PExpr.var 2; let ax1 := PExpr.var 3; let ax2 := PExpr.var 4; let ax3 := PExpr.var 5
    let by0 := PExpr.var 6; let by1 := PExpr.var 7; let by2 := PExpr.var 8; let by3 := PExpr.var 9
    let cz0 := PExpr.var 10; let cz1 := PExpr.var 11; let cz2 := PExpr.var 12; let cz3 := PExpr.var 13
    refine ext ?_ ?_ ?_ ?_
    · exact RatQ.eqQ_of_norm_eq env
        (pMul0 pq1 pq2 ax0 ax1 ax2 ax3 (.add by0 cz0) (.add by1 cz1) (.add by2 cz2) (.add by3 cz3))
        (.add (pMul0 pq1 pq2 ax0 ax1 ax2 ax3 by0 by1 by2 by3)
              (pMul0 pq1 pq2 ax0 ax1 ax2 ax3 cz0 cz1 cz2 cz3)) (by decide)
    · exact RatQ.eqQ_of_norm_eq env
        (pMul1 pq1 pq2 ax0 ax1 ax2 ax3 (.add by0 cz0) (.add by1 cz1) (.add by2 cz2) (.add by3 cz3))
        (.add (pMul1 pq1 pq2 ax0 ax1 ax2 ax3 by0 by1 by2 by3)
              (pMul1 pq1 pq2 ax0 ax1 ax2 ax3 cz0 cz1 cz2 cz3)) (by decide)
    · exact RatQ.eqQ_of_norm_eq env
        (pMul2 pq1 pq2 ax0 ax1 ax2 ax3 (.add by0 cz0) (.add by1 cz1) (.add by2 cz2) (.add by3 cz3))
        (.add (pMul2 pq1 pq2 ax0 ax1 ax2 ax3 by0 by1 by2 by3)
              (pMul2 pq1 pq2 ax0 ax1 ax2 ax3 cz0 cz1 cz2 cz3)) (by decide)
    · exact RatQ.eqQ_of_norm_eq env
        (pMul3 pq1 pq2 ax0 ax1 ax2 ax3 (.add by0 cz0) (.add by1 cz1) (.add by2 cz2) (.add by3 cz3))
        (.add (pMul3 pq1 pq2 ax0 ax1 ax2 ax3 by0 by1 by2 by3)
              (pMul3 pq1 pq2 ax0 ax1 ax2 ax3 cz0 cz1 cz2 cz3)) (by decide)
  right_distrib x y z := by
    let env := [q1, q2, x.a0, x.a1, x.a2, x.a12, y.a0, y.a1, y.a2, y.a12, z.a0, z.a1, z.a2, z.a12]
    let pq1 := PExpr.var 0; let pq2 := PExpr.var 1
    let ax0 := PExpr.var 2; let ax1 := PExpr.var 3; let ax2 := PExpr.var 4; let ax3 := PExpr.var 5
    let by0 := PExpr.var 6; let by1 := PExpr.var 7; let by2 := PExpr.var 8; let by3 := PExpr.var 9
    let cz0 := PExpr.var 10; let cz1 := PExpr.var 11; let cz2 := PExpr.var 12; let cz3 := PExpr.var 13
    refine ext ?_ ?_ ?_ ?_
    · exact RatQ.eqQ_of_norm_eq env
        (pMul0 pq1 pq2 (.add ax0 by0) (.add ax1 by1) (.add ax2 by2) (.add ax3 by3) cz0 cz1 cz2 cz3)
        (.add (pMul0 pq1 pq2 ax0 ax1 ax2 ax3 cz0 cz1 cz2 cz3)
              (pMul0 pq1 pq2 by0 by1 by2 by3 cz0 cz1 cz2 cz3)) (by decide)
    · exact RatQ.eqQ_of_norm_eq env
        (pMul1 pq1 pq2 (.add ax0 by0) (.add ax1 by1) (.add ax2 by2) (.add ax3 by3) cz0 cz1 cz2 cz3)
        (.add (pMul1 pq1 pq2 ax0 ax1 ax2 ax3 cz0 cz1 cz2 cz3)
              (pMul1 pq1 pq2 by0 by1 by2 by3 cz0 cz1 cz2 cz3)) (by decide)
    · exact RatQ.eqQ_of_norm_eq env
        (pMul2 pq1 pq2 (.add ax0 by0) (.add ax1 by1) (.add ax2 by2) (.add ax3 by3) cz0 cz1 cz2 cz3)
        (.add (pMul2 pq1 pq2 ax0 ax1 ax2 ax3 cz0 cz1 cz2 cz3)
              (pMul2 pq1 pq2 by0 by1 by2 by3 cz0 cz1 cz2 cz3)) (by decide)
    · exact RatQ.eqQ_of_norm_eq env
        (pMul3 pq1 pq2 (.add ax0 by0) (.add ax1 by1) (.add ax2 by2) (.add ax3 by3) cz0 cz1 cz2 cz3)
        (.add (pMul3 pq1 pq2 ax0 ax1 ax2 ax3 cz0 cz1 cz2 cz3)
              (pMul3 pq1 pq2 by0 by1 by2 by3 cz0 cz1 cz2 cz3)) (by decide)
  one_smul x := ext (RatQ.one_mul _) (RatQ.one_mul _) (RatQ.one_mul _) (RatQ.one_mul _)
  mul_smul r s x := ext (RatQ.mul_assoc _ _ _) (RatQ.mul_assoc _ _ _)
                        (RatQ.mul_assoc _ _ _) (RatQ.mul_assoc _ _ _)
  smul_add r x y := ext (RatQ.left_distrib _ _ _) (RatQ.left_distrib _ _ _)
                        (RatQ.left_distrib _ _ _) (RatQ.left_distrib _ _ _)
  add_smul r s x := ext (RatQ.right_distrib _ _ _) (RatQ.right_distrib _ _ _)
                        (RatQ.right_distrib _ _ _) (RatQ.right_distrib _ _ _)
  zero_smul x := ext (RatQ.zero_mul _) (RatQ.zero_mul _) (RatQ.zero_mul _) (RatQ.zero_mul _)
  smul_mul_left r x y := by
    let env := [r, q1, q2, x.a0, x.a1, x.a2, x.a12, y.a0, y.a1, y.a2, y.a12]
    let pr := PExpr.var 0; let pq1 := PExpr.var 1; let pq2 := PExpr.var 2
    let ax0 := PExpr.var 3; let ax1 := PExpr.var 4; let ax2 := PExpr.var 5; let ax3 := PExpr.var 6
    let by0 := PExpr.var 7; let by1 := PExpr.var 8; let by2 := PExpr.var 9; let by3 := PExpr.var 10
    refine ext ?_ ?_ ?_ ?_
    · exact RatQ.eqQ_of_norm_eq env
        (pMul0 pq1 pq2 (.mul pr ax0) (.mul pr ax1) (.mul pr ax2) (.mul pr ax3) by0 by1 by2 by3)
        (.mul pr (pMul0 pq1 pq2 ax0 ax1 ax2 ax3 by0 by1 by2 by3)) (by decide)
    · exact RatQ.eqQ_of_norm_eq env
        (pMul1 pq1 pq2 (.mul pr ax0) (.mul pr ax1) (.mul pr ax2) (.mul pr ax3) by0 by1 by2 by3)
        (.mul pr (pMul1 pq1 pq2 ax0 ax1 ax2 ax3 by0 by1 by2 by3)) (by decide)
    · exact RatQ.eqQ_of_norm_eq env
        (pMul2 pq1 pq2 (.mul pr ax0) (.mul pr ax1) (.mul pr ax2) (.mul pr ax3) by0 by1 by2 by3)
        (.mul pr (pMul2 pq1 pq2 ax0 ax1 ax2 ax3 by0 by1 by2 by3)) (by decide)
    · exact RatQ.eqQ_of_norm_eq env
        (pMul3 pq1 pq2 (.mul pr ax0) (.mul pr ax1) (.mul pr ax2) (.mul pr ax3) by0 by1 by2 by3)
        (.mul pr (pMul3 pq1 pq2 ax0 ax1 ax2 ax3 by0 by1 by2 by3)) (by decide)

/-- Fundamental Clifford quadratic law on `V = span(e_1, e_2)`: `v * v = (q1 * x1^2 + q2 * x2^2) • 1`. -/
theorem clifford_vec_sq (q1 q2 x1 x2 : RatQ) :
    let v : Cl2 q1 q2 := add (smul x1 (e1 q1 q2)) (smul x2 (e2 q1 q2))
    mul v v = smul (q1 * (x1 * x1) + q2 * (x2 * x2)) (one q1 q2) := by
  let env := [q1, q2, x1, x2]
  let vx0 := PExpr.add (.mul (.var 2) (.const 0)) (.mul (.var 3) (.const 0))
  let vx1 := PExpr.add (.mul (.var 2) (.const 1)) (.mul (.var 3) (.const 0))
  let vx2 := PExpr.add (.mul (.var 2) (.const 0)) (.mul (.var 3) (.const 1))
  let vx3 := PExpr.add (.mul (.var 2) (.const 0)) (.mul (.var 3) (.const 0))
  let qform := PExpr.add (.mul (.var 0) (.mul (.var 2) (.var 2)))
                         (.mul (.var 1) (.mul (.var 3) (.var 3)))
  refine ext ?_ ?_ ?_ ?_
  · exact RatQ.eqQ_of_norm_eq env
      (pMul0 (.var 0) (.var 1) vx0 vx1 vx2 vx3 vx0 vx1 vx2 vx3) (.mul qform (.const 1)) (by decide)
  · exact RatQ.eqQ_of_norm_eq env
      (pMul1 (.var 0) (.var 1) vx0 vx1 vx2 vx3 vx0 vx1 vx2 vx3) (.mul qform (.const 0)) (by decide)
  · exact RatQ.eqQ_of_norm_eq env
      (pMul2 (.var 0) (.var 1) vx0 vx1 vx2 vx3 vx0 vx1 vx2 vx3) (.mul qform (.const 0)) (by decide)
  · exact RatQ.eqQ_of_norm_eq env
      (pMul3 (.var 0) (.var 1) vx0 vx1 vx2 vx3 vx0 vx1 vx2 vx3) (.mul qform (.const 0)) (by decide)

end Cl2

/-! ### `2 × 2` Matrix Algebra `M2Q` over `ℚ` -/

structure M2Q where
  m00 : RatQ
  m01 : RatQ
  m10 : RatQ
  m11 : RatQ

instance : DecidableEq M2Q := fun A B =>
  if h : A.m00 = B.m00 ∧ A.m01 = B.m01 ∧ A.m10 = B.m10 ∧ A.m11 = B.m11 then
    isTrue (by
      rcases h with ⟨h00, h01, h10, h11⟩
      cases A; cases B; cases h00; cases h01; cases h10; cases h11; rfl)
  else
    isFalse (fun heq => by subst heq; exact h ⟨rfl, rfl, rfl, rfl⟩)

namespace M2Q

def zero : M2Q := ⟨0, 0, 0, 0⟩
def one  : M2Q := ⟨1, 0, 0, 1⟩
def E00  : M2Q := ⟨1, 0, 0, 0⟩
def E01  : M2Q := ⟨0, 1, 0, 0⟩
def E10  : M2Q := ⟨0, 0, 1, 0⟩
def E11  : M2Q := ⟨0, 0, 0, 1⟩

def add (A B : M2Q) : M2Q := ⟨A.m00 + B.m00, A.m01 + B.m01, A.m10 + B.m10, A.m11 + B.m11⟩
def neg (A : M2Q) : M2Q := ⟨-A.m00, -A.m01, -A.m10, -A.m11⟩
def smul (r : RatQ) (A : M2Q) : M2Q := ⟨r * A.m00, r * A.m01, r * A.m10, r * A.m11⟩
def mul (A B : M2Q) : M2Q :=
  ⟨A.m00 * B.m00 + A.m01 * B.m10,
   A.m00 * B.m01 + A.m01 * B.m11,
   A.m10 * B.m00 + A.m11 * B.m10,
   A.m10 * B.m01 + A.m11 * B.m11⟩

theorem ext {A B : M2Q}
    (h00 : A.m00 = B.m00) (h01 : A.m01 = B.m01)
    (h10 : A.m10 = B.m10) (h11 : A.m11 = B.m11) : A = B := by
  cases A; cases B; simp_all

def alg : QAlgebra M2Q where
  zero := zero
  one  := one
  add  := add
  neg  := neg
  mul  := mul
  smul := smul
  add_assoc A B C := ext (RatQ.add_assoc _ _ _) (RatQ.add_assoc _ _ _)
                         (RatQ.add_assoc _ _ _) (RatQ.add_assoc _ _ _)
  add_comm A B    := ext (RatQ.add_comm _ _) (RatQ.add_comm _ _)
                         (RatQ.add_comm _ _) (RatQ.add_comm _ _)
  zero_add A      := ext (RatQ.zero_add _) (RatQ.zero_add _)
                         (RatQ.zero_add _) (RatQ.zero_add _)
  add_zero A      := ext (RatQ.add_zero _) (RatQ.add_zero _)
                         (RatQ.add_zero _) (RatQ.add_zero _)
  neg_add A       := ext (RatQ.neg_add_cancel _) (RatQ.neg_add_cancel _)
                         (RatQ.neg_add_cancel _) (RatQ.neg_add_cancel _)
  mul_assoc A B C := by
    let env := [A.m00, A.m01, A.m10, A.m11, B.m00, B.m01, B.m10, B.m11, C.m00, C.m01, C.m10, C.m11]
    let a00 := PExpr.var 0; let a01 := PExpr.var 1; let a10 := PExpr.var 2; let a11 := PExpr.var 3
    let b00 := PExpr.var 4; let b01 := PExpr.var 5; let b10 := PExpr.var 6; let b11 := PExpr.var 7
    let c00 := PExpr.var 8; let c01 := PExpr.var 9; let c10 := PExpr.var 10; let c11 := PExpr.var 11
    let ab00 := PExpr.add (.mul a00 b00) (.mul a01 b10)
    let ab01 := PExpr.add (.mul a00 b01) (.mul a01 b11)
    let ab10 := PExpr.add (.mul a10 b00) (.mul a11 b10)
    let ab11 := PExpr.add (.mul a10 b01) (.mul a11 b11)
    let bc00 := PExpr.add (.mul b00 c00) (.mul b01 c10)
    let bc01 := PExpr.add (.mul b00 c01) (.mul b01 c11)
    let bc10 := PExpr.add (.mul b10 c00) (.mul b11 c10)
    let bc11 := PExpr.add (.mul b10 c01) (.mul b11 c11)
    refine ext ?_ ?_ ?_ ?_
    · exact RatQ.eqQ_of_norm_eq env (.add (.mul ab00 c00) (.mul ab01 c10))
                                    (.add (.mul a00 bc00) (.mul a01 bc10)) (by decide)
    · exact RatQ.eqQ_of_norm_eq env (.add (.mul ab00 c01) (.mul ab01 c11))
                                    (.add (.mul a00 bc01) (.mul a01 bc11)) (by decide)
    · exact RatQ.eqQ_of_norm_eq env (.add (.mul ab10 c00) (.mul ab11 c10))
                                    (.add (.mul a10 bc00) (.mul a11 bc10)) (by decide)
    · exact RatQ.eqQ_of_norm_eq env (.add (.mul ab10 c01) (.mul ab11 c11))
                                    (.add (.mul a10 bc01) (.mul a11 bc11)) (by decide)
  one_mul A := by
    let env := [A.m00, A.m01, A.m10, A.m11]
    refine ext ?_ ?_ ?_ ?_
    · exact RatQ.eqQ_of_norm_eq env (.add (.mul (.const 1) (.var 0)) (.mul (.const 0) (.var 2))) (.var 0) (by decide)
    · exact RatQ.eqQ_of_norm_eq env (.add (.mul (.const 1) (.var 1)) (.mul (.const 0) (.var 3))) (.var 1) (by decide)
    · exact RatQ.eqQ_of_norm_eq env (.add (.mul (.const 0) (.var 0)) (.mul (.const 1) (.var 2))) (.var 2) (by decide)
    · exact RatQ.eqQ_of_norm_eq env (.add (.mul (.const 0) (.var 1)) (.mul (.const 1) (.var 3))) (.var 3) (by decide)
  mul_one A := by
    let env := [A.m00, A.m01, A.m10, A.m11]
    refine ext ?_ ?_ ?_ ?_
    · exact RatQ.eqQ_of_norm_eq env (.add (.mul (.var 0) (.const 1)) (.mul (.var 1) (.const 0))) (.var 0) (by decide)
    · exact RatQ.eqQ_of_norm_eq env (.add (.mul (.var 0) (.const 0)) (.mul (.var 1) (.const 1))) (.var 1) (by decide)
    · exact RatQ.eqQ_of_norm_eq env (.add (.mul (.var 2) (.const 1)) (.mul (.var 3) (.const 0))) (.var 2) (by decide)
    · exact RatQ.eqQ_of_norm_eq env (.add (.mul (.var 2) (.const 0)) (.mul (.var 3) (.const 1))) (.var 3) (by decide)
  left_distrib A B C := by
    let env := [A.m00, A.m01, A.m10, A.m11, B.m00, B.m01, B.m10, B.m11, C.m00, C.m01, C.m10, C.m11]
    refine ext ?_ ?_ ?_ ?_
    · exact RatQ.eqQ_of_norm_eq env
        (.add (.mul (.var 0) (.add (.var 4) (.var 8))) (.mul (.var 1) (.add (.var 6) (.var 10))))
        (.add (.add (.mul (.var 0) (.var 4)) (.mul (.var 1) (.var 6)))
              (.add (.mul (.var 0) (.var 8)) (.mul (.var 1) (.var 10)))) (by decide)
    · exact RatQ.eqQ_of_norm_eq env
        (.add (.mul (.var 0) (.add (.var 5) (.var 9))) (.mul (.var 1) (.add (.var 7) (.var 11))))
        (.add (.add (.mul (.var 0) (.var 5)) (.mul (.var 1) (.var 7)))
              (.add (.mul (.var 0) (.var 9)) (.mul (.var 1) (.var 11)))) (by decide)
    · exact RatQ.eqQ_of_norm_eq env
        (.add (.mul (.var 2) (.add (.var 4) (.var 8))) (.mul (.var 3) (.add (.var 6) (.var 10))))
        (.add (.add (.mul (.var 2) (.var 4)) (.mul (.var 3) (.var 6)))
              (.add (.mul (.var 2) (.var 8)) (.mul (.var 3) (.var 10)))) (by decide)
    · exact RatQ.eqQ_of_norm_eq env
        (.add (.mul (.var 2) (.add (.var 5) (.var 9))) (.mul (.var 3) (.add (.var 7) (.var 11))))
        (.add (.add (.mul (.var 2) (.var 5)) (.mul (.var 3) (.var 7)))
              (.add (.mul (.var 2) (.var 9)) (.mul (.var 3) (.var 11)))) (by decide)
  right_distrib A B C := by
    let env := [A.m00, A.m01, A.m10, A.m11, B.m00, B.m01, B.m10, B.m11, C.m00, C.m01, C.m10, C.m11]
    refine ext ?_ ?_ ?_ ?_
    · exact RatQ.eqQ_of_norm_eq env
        (.add (.mul (.add (.var 0) (.var 4)) (.var 8)) (.mul (.add (.var 1) (.var 5)) (.var 10)))
        (.add (.add (.mul (.var 0) (.var 8)) (.mul (.var 1) (.var 10)))
              (.add (.mul (.var 4) (.var 8)) (.mul (.var 5) (.var 10)))) (by decide)
    · exact RatQ.eqQ_of_norm_eq env
        (.add (.mul (.add (.var 0) (.var 4)) (.var 9)) (.mul (.add (.var 1) (.var 5)) (.var 11)))
        (.add (.add (.mul (.var 0) (.var 9)) (.mul (.var 1) (.var 11)))
              (.add (.mul (.var 4) (.var 9)) (.mul (.var 5) (.var 11)))) (by decide)
    · exact RatQ.eqQ_of_norm_eq env
        (.add (.mul (.add (.var 2) (.var 6)) (.var 8)) (.mul (.add (.var 3) (.var 7)) (.var 10)))
        (.add (.add (.mul (.var 2) (.var 8)) (.mul (.var 3) (.var 10)))
              (.add (.mul (.var 6) (.var 8)) (.mul (.var 7) (.var 10)))) (by decide)
    · exact RatQ.eqQ_of_norm_eq env
        (.add (.mul (.add (.var 2) (.var 6)) (.var 9)) (.mul (.add (.var 3) (.var 7)) (.var 11)))
        (.add (.add (.mul (.var 2) (.var 9)) (.mul (.var 3) (.var 11)))
              (.add (.mul (.var 6) (.var 9)) (.mul (.var 7) (.var 11)))) (by decide)
  one_smul A := ext (RatQ.one_mul _) (RatQ.one_mul _) (RatQ.one_mul _) (RatQ.one_mul _)
  mul_smul r s A := ext (RatQ.mul_assoc _ _ _) (RatQ.mul_assoc _ _ _)
                        (RatQ.mul_assoc _ _ _) (RatQ.mul_assoc _ _ _)
  smul_add r A B := ext (RatQ.left_distrib _ _ _) (RatQ.left_distrib _ _ _)
                        (RatQ.left_distrib _ _ _) (RatQ.left_distrib _ _ _)
  add_smul r s A := ext (RatQ.right_distrib _ _ _) (RatQ.right_distrib _ _ _)
                        (RatQ.right_distrib _ _ _) (RatQ.right_distrib _ _ _)
  zero_smul A := ext (RatQ.zero_mul _) (RatQ.zero_mul _) (RatQ.zero_mul _) (RatQ.zero_mul _)
  smul_mul_left r A B := by
    let env := [r, A.m00, A.m01, A.m10, A.m11, B.m00, B.m01, B.m10, B.m11]
    refine ext ?_ ?_ ?_ ?_
    · exact RatQ.eqQ_of_norm_eq env
        (.add (.mul (.mul (.var 0) (.var 1)) (.var 5)) (.mul (.mul (.var 0) (.var 2)) (.var 7)))
        (.mul (.var 0) (.add (.mul (.var 1) (.var 5)) (.mul (.var 2) (.var 7)))) (by decide)
    · exact RatQ.eqQ_of_norm_eq env
        (.add (.mul (.mul (.var 0) (.var 1)) (.var 6)) (.mul (.mul (.var 0) (.var 2)) (.var 8)))
        (.mul (.var 0) (.add (.mul (.var 1) (.var 6)) (.mul (.var 2) (.var 8)))) (by decide)
    · exact RatQ.eqQ_of_norm_eq env
        (.add (.mul (.mul (.var 0) (.var 3)) (.var 5)) (.mul (.mul (.var 0) (.var 4)) (.var 7)))
        (.mul (.var 0) (.add (.mul (.var 3) (.var 5)) (.mul (.var 4) (.var 7)))) (by decide)
    · exact RatQ.eqQ_of_norm_eq env
        (.add (.mul (.mul (.var 0) (.var 3)) (.var 6)) (.mul (.mul (.var 0) (.var 4)) (.var 8)))
        (.mul (.var 0) (.add (.mul (.var 3) (.var 6)) (.mul (.var 4) (.var 8)))) (by decide)

/-- First-column subspace of `M_2(ℚ)`: matrices supported exclusively in column 0. -/
def FirstColumn (M : M2Q) : Prop :=
  M.m01 = 0 ∧ M.m11 = 0

instance (M : M2Q) : Decidable (FirstColumn M) :=
  inferInstanceAs (Decidable (M.m01 = 0 ∧ M.m11 = 0))

end M2Q

/-! ### Positive Non-Vacuity Theorem: Split `Cl_{1,1}(ℚ) = Cl2 1 (-1) ≅ M_2(ℚ)` (`n = 2`) -/

abbrev Cl11Q := Cl2 1 (-1)
def Cl11Alg : QAlgebra Cl11Q := Cl2.alg 1 (-1)

namespace Cl11

def phi (x : Cl11Q) : M2Q :=
  ⟨x.a0 + x.a1, -x.a2 - x.a12, x.a2 - x.a12, x.a0 - x.a1⟩

def psi (M : M2Q) : Cl11Q :=
  ⟨RatQ.half * (M.m00 + M.m11),
   RatQ.half * (M.m00 - M.m11),
   RatQ.half * (M.m10 - M.m01),
   -(RatQ.half * (M.m01 + M.m10))⟩

private theorem half_two_id (u : RatQ) : RatQ.half * ((2 : RatQ) * u) = u := by
  rw [← RatQ.mul_assoc, RatQ.half_mul_two, RatQ.one_mul]

private theorem two_half_id (u : RatQ) : (2 : RatQ) * (RatQ.half * u) = u := by
  rw [← RatQ.mul_assoc, RatQ.two_mul_half, RatQ.one_mul]

theorem psi_phi (x : Cl11Q) : psi (phi x) = x := by
  unfold psi phi
  refine Cl2.ext ?_ ?_ ?_ ?_
  · have h : (x.a0 + x.a1) + (x.a0 - x.a1) = (2 : RatQ) * x.a0 :=
      RatQ.eqQ_of_norm_eq [x.a0, x.a1]
        (.add (.add (.var 0) (.var 1)) (.sub (.var 0) (.var 1))) (.mul (.const 2) (.var 0)) (by decide)
    rw [h, half_two_id]
  · have h : (x.a0 + x.a1) - (x.a0 - x.a1) = (2 : RatQ) * x.a1 :=
      RatQ.eqQ_of_norm_eq [x.a0, x.a1]
        (.sub (.add (.var 0) (.var 1)) (.sub (.var 0) (.var 1))) (.mul (.const 2) (.var 1)) (by decide)
    rw [h, half_two_id]
  · have h : (x.a2 - x.a12) - (-x.a2 - x.a12) = (2 : RatQ) * x.a2 :=
      RatQ.eqQ_of_norm_eq [x.a2, x.a12]
        (.sub (.sub (.var 0) (.var 1)) (.sub (.neg (.var 0)) (.var 1))) (.mul (.const 2) (.var 0)) (by decide)
    rw [h, half_two_id]
  · have h : (-x.a2 - x.a12) + (x.a2 - x.a12) = (2 : RatQ) * (-x.a12) :=
      RatQ.eqQ_of_norm_eq [x.a2, x.a12]
        (.add (.sub (.neg (.var 0)) (.var 1)) (.sub (.var 0) (.var 1)))
        (.mul (.const 2) (.neg (.var 1))) (by decide)
    rw [h, half_two_id]
    exact RatQ.eqQ_of_norm_eq [x.a12] (.neg (.neg (.var 0))) (.var 0) (by decide)

theorem phi_psi (M : M2Q) : phi (psi M) = M := by
  unfold phi psi
  refine M2Q.ext ?_ ?_ ?_ ?_
  · have h : RatQ.half * (M.m00 + M.m11) + RatQ.half * (M.m00 - M.m11) =
        (2 : RatQ) * (RatQ.half * M.m00) :=
      RatQ.eqQ_of_norm_eq [RatQ.half, M.m00, M.m11]
        (.add (.mul (.var 0) (.add (.var 1) (.var 2))) (.mul (.var 0) (.sub (.var 1) (.var 2))))
        (.mul (.const 2) (.mul (.var 0) (.var 1))) (by decide)
    rw [h, two_half_id]
  · have h : -(RatQ.half * (M.m10 - M.m01)) - -(RatQ.half * (M.m01 + M.m10)) =
        (2 : RatQ) * (RatQ.half * M.m01) :=
      RatQ.eqQ_of_norm_eq [RatQ.half, M.m01, M.m10]
        (.sub (.neg (.mul (.var 0) (.sub (.var 2) (.var 1))))
              (.neg (.mul (.var 0) (.add (.var 1) (.var 2)))))
        (.mul (.const 2) (.mul (.var 0) (.var 1))) (by decide)
    rw [h, two_half_id]
  · have h : RatQ.half * (M.m10 - M.m01) - -(RatQ.half * (M.m01 + M.m10)) =
        (2 : RatQ) * (RatQ.half * M.m10) :=
      RatQ.eqQ_of_norm_eq [RatQ.half, M.m01, M.m10]
        (.sub (.mul (.var 0) (.sub (.var 2) (.var 1)))
              (.neg (.mul (.var 0) (.add (.var 1) (.var 2)))))
        (.mul (.const 2) (.mul (.var 0) (.var 2))) (by decide)
    rw [h, two_half_id]
  · have h : RatQ.half * (M.m00 + M.m11) - RatQ.half * (M.m00 - M.m11) =
        (2 : RatQ) * (RatQ.half * M.m11) :=
      RatQ.eqQ_of_norm_eq [RatQ.half, M.m00, M.m11]
        (.sub (.mul (.var 0) (.add (.var 1) (.var 2))) (.mul (.var 0) (.sub (.var 1) (.var 2))))
        (.mul (.const 2) (.mul (.var 0) (.var 2))) (by decide)
    rw [h, two_half_id]

theorem phi_mul (x y : Cl11Q) : phi (Cl11Alg.mul x y) = M2Q.mul (phi x) (phi y) := by
  let env := [x.a0, x.a1, x.a2, x.a12, y.a0, y.a1, y.a2, y.a12]
  let ax0 := PExpr.var 0; let ax1 := PExpr.var 1; let ax2 := PExpr.var 2; let ax3 := PExpr.var 3
  let by0 := PExpr.var 4; let by1 := PExpr.var 5; let by2 := PExpr.var 6; let by3 := PExpr.var 7
  let m1 := PExpr.neg (.const 1)
  let c0 := PExpr.sub (.add (.add (.mul ax0 by0) (.mul (.mul (.const 1) ax1) by1))
                            (.mul (.mul m1 ax2) by2))
                      (.mul (.mul (.mul (.const 1) m1) ax3) by3)
  let c1 := PExpr.add (.sub (.add (.mul ax0 by1) (.mul ax1 by0))
                            (.mul (.mul m1 ax2) by3))
                      (.mul (.mul m1 ax3) by2)
  let c2 := PExpr.sub (.add (.add (.mul ax0 by2) (.mul (.mul (.const 1) ax1) by3))
                            (.mul ax2 by0))
                      (.mul (.mul (.const 1) ax3) by1)
  let c3 := PExpr.add (.sub (.add (.mul ax0 by3) (.mul ax1 by2)) (.mul ax2 by1)) (.mul ax3 by0)
  let px00 := PExpr.add ax0 ax1
  let px01 := PExpr.sub (.neg ax2) ax3
  let px10 := PExpr.sub ax2 ax3
  let px11 := PExpr.sub ax0 ax1
  let py00 := PExpr.add by0 by1
  let py01 := PExpr.sub (.neg by2) by3
  let py10 := PExpr.sub by2 by3
  let py11 := PExpr.sub by0 by1
  refine M2Q.ext ?_ ?_ ?_ ?_
  · exact RatQ.eqQ_of_norm_eq env (.add c0 c1) (.add (.mul px00 py00) (.mul px01 py10)) (by decide)
  · exact RatQ.eqQ_of_norm_eq env (.sub (.neg c2) c3) (.add (.mul px00 py01) (.mul px01 py11)) (by decide)
  · exact RatQ.eqQ_of_norm_eq env (.sub c2 c3) (.add (.mul px10 py00) (.mul px11 py10)) (by decide)
  · exact RatQ.eqQ_of_norm_eq env (.sub c0 c1) (.add (.mul px10 py01) (.mul px11 py11)) (by decide)

theorem phi_add (x y : Cl11Q) : phi (Cl11Alg.add x y) = M2Q.add (phi x) (phi y) := by
  refine M2Q.ext ?_ ?_ ?_ ?_
  · exact RatQ.eqQ_of_norm_eq [x.a0, x.a1, y.a0, y.a1]
      (.add (.add (.var 0) (.var 2)) (.add (.var 1) (.var 3)))
      (.add (.add (.var 0) (.var 1)) (.add (.var 2) (.var 3))) (by decide)
  · exact RatQ.eqQ_of_norm_eq [x.a2, x.a12, y.a2, y.a12]
      (.sub (.neg (.add (.var 0) (.var 2))) (.add (.var 1) (.var 3)))
      (.add (.sub (.neg (.var 0)) (.var 1)) (.sub (.neg (.var 2)) (.var 3))) (by decide)
  · exact RatQ.eqQ_of_norm_eq [x.a2, x.a12, y.a2, y.a12]
      (.sub (.add (.var 0) (.var 2)) (.add (.var 1) (.var 3)))
      (.add (.sub (.var 0) (.var 1)) (.sub (.var 2) (.var 3))) (by decide)
  · exact RatQ.eqQ_of_norm_eq [x.a0, x.a1, y.a0, y.a1]
      (.sub (.add (.var 0) (.var 2)) (.add (.var 1) (.var 3)))
      (.add (.sub (.var 0) (.var 1)) (.sub (.var 2) (.var 3))) (by decide)

theorem phi_smul (r : RatQ) (x : Cl11Q) : phi (Cl11Alg.smul r x) = M2Q.smul r (phi x) := by
  refine M2Q.ext ?_ ?_ ?_ ?_
  · exact RatQ.eqQ_of_norm_eq [r, x.a0, x.a1]
      (.add (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 2)))
      (.mul (.var 0) (.add (.var 1) (.var 2))) (by decide)
  · exact RatQ.eqQ_of_norm_eq [r, x.a2, x.a12]
      (.sub (.neg (.mul (.var 0) (.var 1))) (.mul (.var 0) (.var 2)))
      (.mul (.var 0) (.sub (.neg (.var 1)) (.var 2))) (by decide)
  · exact RatQ.eqQ_of_norm_eq [r, x.a2, x.a12]
      (.sub (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 2)))
      (.mul (.var 0) (.sub (.var 1) (.var 2))) (by decide)
  · exact RatQ.eqQ_of_norm_eq [r, x.a0, x.a1]
      (.sub (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 2)))
      (.mul (.var 0) (.sub (.var 1) (.var 2))) (by decide)

theorem phi_zero : phi Cl11Alg.zero = M2Q.zero := by decide
theorem psi_zero : psi M2Q.zero = Cl11Alg.zero := by decide

/-- Explicit `ℚ`-algebra isomorphism `Cl_{1,1}(ℚ) ≅ M_2(ℚ)`. -/
def isoM2 : QAlgebraIso Cl11Alg M2Q.alg where
  toFun := phi
  invFun := psi
  left_inv := psi_phi
  right_inv := phi_psi
  map_one := by decide
  map_add := phi_add
  map_mul := phi_mul
  map_smul := phi_smul

/-- Primitive idempotent `e = (1 + e_1)/2` in `Cl_{1,1}(ℚ)`. -/
def primIdem : Cl11Q := ⟨RatQ.half, RatQ.half, 0, 0⟩

theorem phi_primIdem : phi primIdem = M2Q.E00 := by decide

theorem primIdem_isIdempotent : Cl11Alg.IsIdempotent primIdem := ⟨by decide, by decide⟩

/-- Algebraic spinor space `S_{1,1} = Cl_{1,1}(ℚ) · e = {x : x · e = x}`. -/
def SpinorIdeal (x : Cl11Q) : Prop :=
  Cl11Alg.mul x primIdem = x

/-- Exact matrix-column characterization: `x ∈ S_{1,1}` iff `Φ_{1,1}(x)` lies in column 0 of `M_2(ℚ)`. -/
theorem spinorIdeal_iff_firstColumn (x : Cl11Q) :
    SpinorIdeal x ↔ M2Q.FirstColumn (phi x) := by
  unfold SpinorIdeal M2Q.FirstColumn
  constructor
  · intro hx
    have hphi : phi (Cl11Alg.mul x primIdem) = phi x := by rw [hx]
    rw [phi_mul, phi_primIdem] at hphi
    have hm01 : (M2Q.mul (phi x) M2Q.E00).m01 = (phi x).m01 := by rw [hphi]
    have hm11 : (M2Q.mul (phi x) M2Q.E00).m11 = (phi x).m11 := by rw [hphi]
    have z01 : (M2Q.mul (phi x) M2Q.E00).m01 = 0 := by
      show (phi x).m00 * 0 + (phi x).m01 * 0 = 0
      rw [RatQ.mul_zero, RatQ.mul_zero, RatQ.add_zero]
    have z11 : (M2Q.mul (phi x) M2Q.E00).m11 = 0 := by
      show (phi x).m10 * 0 + (phi x).m11 * 0 = 0
      rw [RatQ.mul_zero, RatQ.mul_zero, RatQ.add_zero]
    exact ⟨hm01.symm.trans z01, hm11.symm.trans z11⟩
  · rintro ⟨h01, h11⟩
    have hmat : M2Q.mul (phi x) M2Q.E00 = phi x := by
      refine M2Q.ext ?_ ?_ ?_ ?_
      · show (phi x).m00 * 1 + (phi x).m01 * 0 = (phi x).m00
        rw [RatQ.mul_one, RatQ.mul_zero, RatQ.add_zero]
      · show (phi x).m00 * 0 + (phi x).m01 * 0 = (phi x).m01
        rw [RatQ.mul_zero, RatQ.mul_zero, RatQ.add_zero, h01]
      · show (phi x).m10 * 1 + (phi x).m11 * 0 = (phi x).m10
        rw [RatQ.mul_one, RatQ.mul_zero, RatQ.add_zero]
      · show (phi x).m10 * 0 + (phi x).m11 * 0 = (phi x).m11
        rw [RatQ.mul_zero, RatQ.mul_zero, RatQ.add_zero, h11]
    have hpsi : psi (phi (Cl11Alg.mul x primIdem)) = psi (phi x) := by
      rw [phi_mul, phi_primIdem, hmat]
    rw [psi_phi, psi_phi] at hpsi
    exact hpsi

/-- Spinor weight basis vectors `s_+ = e` and `s_- = e_2 · e` in `S_{1,1}`. -/
def sPlus  : Cl11Q := primIdem
def sMinus : Cl11Q := Cl11Alg.mul (Cl2.e2 1 (-1)) primIdem

theorem phi_sPlus  : phi sPlus  = M2Q.E00 := by decide
theorem phi_sMinus : phi sMinus = M2Q.E10 := by decide

theorem sPlus_mem  : SpinorIdeal sPlus  := (spinorIdeal_iff_firstColumn sPlus).mpr (by decide)
theorem sMinus_mem : SpinorIdeal sMinus := (spinorIdeal_iff_firstColumn sMinus).mpr (by decide)

/-- `S_{1,1}` is a minimal nonzero left ideal of `Cl_{1,1}(ℚ)`. -/
theorem spinorIdeal_isMinimalLeftIdeal : Cl11Alg.IsMinimalLeftIdeal SpinorIdeal := by
  have hleft : Cl11Alg.IsLeftIdeal SpinorIdeal := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact Cl11Alg.zero_mul primIdem
    · intro x y hx hy
      unfold SpinorIdeal at *
      rw [Cl11Alg.right_distrib, hx, hy]
    · intro r x hx
      unfold SpinorIdeal at *
      rw [Cl11Alg.smul_mul_left, hx]
    · intro a x hx
      unfold SpinorIdeal at *
      rw [Cl11Alg.mul_assoc, hx]
  refine ⟨hleft, ⟨sPlus, sPlus_mem, by decide⟩, ?_⟩
  intro I hI hsub
  by_cases hall0 : ∀ x, I x → x = Cl11Alg.zero
  · exact .inl hall0
  · right
    have hex : ∃ y, I y ∧ y ≠ Cl11Alg.zero := by
      apply Classical.byContradiction
      intro hno
      apply hall0
      intro x hxI
      apply Classical.byContradiction
      intro hxz
      exact hno ⟨x, hxI, hxz⟩
    rcases hex with ⟨y, hyI, hy_nz⟩
    have ⟨hy01, hy11⟩ := (spinorIdeal_iff_firstColumn y).mp (hsub y hyI)
    let u := (phi y).m00
    let v := (phi y).m10
    have huv_nz : u ≠ 0 ∨ v ≠ 0 := by
      by_cases hu : u = 0
      · right
        intro hv
        apply hy_nz
        have hpy : phi y = M2Q.zero := M2Q.ext hu hy01 hv hy11
        have hpsy : psi (phi y) = psi M2Q.zero := by rw [hpy]
        rw [psi_phi, psi_zero] at hpsy
        exact hpsy
      · exact .inl hu
    have hsPlus_in_I : I sPlus := by
      cases huv_nz with
      | inl hu =>
        let A : M2Q := ⟨u⁻¹, 0, 0, 0⟩
        have hmul : Cl11Alg.mul (psi A) y = sPlus := by
          have hphi_eq : phi (Cl11Alg.mul (psi A) y) = phi sPlus := by
            rw [phi_mul, phi_psi, phi_sPlus]
            refine M2Q.ext ?_ ?_ ?_ ?_
            · show u⁻¹ * u + 0 * v = 1
              rw [RatQ.inv_mul_cancel hu, RatQ.zero_mul, RatQ.add_zero]
            · show u⁻¹ * (phi y).m01 + 0 * (phi y).m11 = 0
              rw [hy01, hy11, RatQ.mul_zero, RatQ.mul_zero, RatQ.add_zero]
            · show 0 * u + 0 * v = 0
              rw [RatQ.zero_mul, RatQ.zero_mul, RatQ.add_zero]
            · show 0 * (phi y).m01 + 0 * (phi y).m11 = 0
              rw [RatQ.zero_mul, RatQ.zero_mul, RatQ.add_zero]
          have hpsi_eq : psi (phi (Cl11Alg.mul (psi A) y)) = psi (phi sPlus) := by rw [hphi_eq]
          rw [psi_phi, psi_phi] at hpsi_eq
          exact hpsi_eq
        rw [← hmul]
        exact hI.2.2.2 (psi A) y hyI
      | inr hv =>
        let A : M2Q := ⟨0, v⁻¹, 0, 0⟩
        have hmul : Cl11Alg.mul (psi A) y = sPlus := by
          have hphi_eq : phi (Cl11Alg.mul (psi A) y) = phi sPlus := by
            rw [phi_mul, phi_psi, phi_sPlus]
            refine M2Q.ext ?_ ?_ ?_ ?_
            · show 0 * u + v⁻¹ * v = 1
              rw [RatQ.zero_mul, RatQ.zero_add, RatQ.inv_mul_cancel hv]
            · show 0 * (phi y).m01 + v⁻¹ * (phi y).m11 = 0
              rw [hy01, hy11, RatQ.mul_zero, RatQ.mul_zero, RatQ.add_zero]
            · show 0 * u + 0 * v = 0
              rw [RatQ.zero_mul, RatQ.zero_mul, RatQ.add_zero]
            · show 0 * (phi y).m01 + 0 * (phi y).m11 = 0
              rw [RatQ.zero_mul, RatQ.zero_mul, RatQ.add_zero]
          have hpsi_eq : psi (phi (Cl11Alg.mul (psi A) y)) = psi (phi sPlus) := by rw [hphi_eq]
          rw [psi_phi, psi_phi] at hpsi_eq
          exact hpsi_eq
        rw [← hmul]
        exact hI.2.2.2 (psi A) y hyI
    intro z hzS
    have hzeq : Cl11Alg.mul z sPlus = z := hzS
    rw [← hzeq]
    exact hI.2.2.2 z sPlus hsPlus_in_I

/-- Exact spinor dimension theorem: `dim_ℚ S_{1,1} = 2 = 2^(2/2)`. -/
def spinorLinearIso : LinearIsoQVec Cl11Alg SpinorIdeal 2 where
  toVec x _ := fun ⟨i, hi⟩ =>
    match i, hi with
    | 0, _ => (phi x).m00
    | 1, _ => (phi x).m10
  ofVec v := psi ⟨v ⟨0, by decide⟩, 0, v ⟨1, by decide⟩, 0⟩
  ofVec_mem v := by
    rw [spinorIdeal_iff_firstColumn, phi_psi]
    exact ⟨rfl, rfl⟩
  left_inv x hx := by
    have ⟨h01, h11⟩ := (spinorIdeal_iff_firstColumn x).mp hx
    have hmat : (⟨(phi x).m00, 0, (phi x).m10, 0⟩ : M2Q) = phi x :=
      M2Q.ext rfl h01.symm rfl h11.symm
    rw [hmat, psi_phi]
  right_inv v := by
    funext ⟨i, hi⟩
    match i, hi with
    | 0, _ => exact congrArg M2Q.m00 (phi_psi ⟨v ⟨0, by decide⟩, 0, v ⟨1, by decide⟩, 0⟩)
    | 1, _ => exact congrArg M2Q.m10 (phi_psi ⟨v ⟨0, by decide⟩, 0, v ⟨1, by decide⟩, 0⟩)
  ofVec_add u v := by
    have hphi_eq : phi (psi ⟨(QVec.add u v) ⟨0, by decide⟩, 0, (QVec.add u v) ⟨1, by decide⟩, 0⟩) =
        phi (Cl11Alg.add (psi ⟨u ⟨0, by decide⟩, 0, u ⟨1, by decide⟩, 0⟩)
                         (psi ⟨v ⟨0, by decide⟩, 0, v ⟨1, by decide⟩, 0⟩)) := by
      rw [phi_add, phi_psi, phi_psi, phi_psi]
      refine M2Q.ext rfl ?_ rfl ?_ <;> (show 0 = 0 + 0; rw [RatQ.add_zero])
    have hpsi := congrArg psi hphi_eq
    rw [psi_phi, psi_phi] at hpsi
    exact hpsi
  ofVec_smul r v := by
    have hphi_eq : phi (psi ⟨(QVec.smul r v) ⟨0, by decide⟩, 0, (QVec.smul r v) ⟨1, by decide⟩, 0⟩) =
        phi (Cl11Alg.smul r (psi ⟨v ⟨0, by decide⟩, 0, v ⟨1, by decide⟩, 0⟩)) := by
      rw [phi_smul, phi_psi, phi_psi]
      refine M2Q.ext rfl ?_ rfl ?_ <;> (show 0 = r * 0; rw [RatQ.mul_zero])
    have hpsi := congrArg psi hphi_eq
    rw [psi_phi, psi_phi] at hpsi
    exact hpsi

theorem spinorIdeal_hasDim_two : HasQDim Cl11Alg SpinorIdeal (2 ^ (2 / 2)) :=
  ⟨spinorLinearIso⟩

/-- Faithfulness: `S_{1,1}` is a faithful left `Cl_{1,1}(ℚ)`-module. -/
theorem spinorIdeal_isFaithful : Cl11Alg.IsFaithfulLeftIdeal SpinorIdeal := by
  intro a ha
  have h1 := ha sPlus sPlus_mem
  have h2 := ha sMinus sMinus_mem
  have hp1 : M2Q.mul (phi a) M2Q.E00 = M2Q.zero := by
    have h := congrArg phi h1
    rw [phi_mul, phi_sPlus, phi_zero] at h
    exact h
  have hp2 : M2Q.mul (phi a) M2Q.E10 = M2Q.zero := by
    have h := congrArg phi h2
    rw [phi_mul, phi_sMinus, phi_zero] at h
    exact h
  have ha00 : (phi a).m00 = 0 := by
    have h := congrArg M2Q.m00 hp1
    change (phi a).m00 * 1 + (phi a).m01 * 0 = 0 at h
    rw [RatQ.mul_one, RatQ.mul_zero, RatQ.add_zero] at h; exact h
  have ha10 : (phi a).m10 = 0 := by
    have h := congrArg M2Q.m10 hp1
    change (phi a).m10 * 1 + (phi a).m11 * 0 = 0 at h
    rw [RatQ.mul_one, RatQ.mul_zero, RatQ.add_zero] at h; exact h
  have ha01 : (phi a).m01 = 0 := by
    have h := congrArg M2Q.m00 hp2
    change (phi a).m00 * 0 + (phi a).m01 * 1 = 0 at h
    rw [RatQ.mul_zero, RatQ.zero_add, RatQ.mul_one] at h; exact h
  have ha11 : (phi a).m11 = 0 := by
    have h := congrArg M2Q.m10 hp2
    change (phi a).m10 * 0 + (phi a).m11 * 1 = 0 at h
    rw [RatQ.mul_zero, RatQ.zero_add, RatQ.mul_one] at h; exact h
  have hphia : phi a = M2Q.zero := M2Q.ext ha00 ha01 ha10 ha11
  have hpsia := congrArg psi hphia
  rw [psi_phi, psi_zero] at hpsia
  exact hpsia

/-- Complete Cartan weight spectrum on `S_{1,1}`: `e_1` has eigenvectors `s_+` (`+1`) and `s_-` (`-1`),
    and every spinor `x ∈ S_{1,1}` decomposes uniquely into `u • s_+ + v • s_-`. -/
theorem cartan_spectrum_complete :
    Cl11Alg.mul (Cl2.e1 1 (-1)) sPlus = sPlus ∧
    Cl11Alg.mul (Cl2.e1 1 (-1)) sMinus = Cl11Alg.neg sMinus ∧
    (∀ x, SpinorIdeal x →
      x = Cl11Alg.add (Cl11Alg.smul (phi x).m00 sPlus) (Cl11Alg.smul (phi x).m10 sMinus)) := by
  refine ⟨by decide, by decide, ?_⟩
  intro x hx
  have ⟨h01, h11⟩ := (spinorIdeal_iff_firstColumn x).mp hx
  have hphi_eq : phi x = phi (Cl11Alg.add (Cl11Alg.smul (phi x).m00 sPlus)
                                          (Cl11Alg.smul (phi x).m10 sMinus)) := by
    rw [phi_add, phi_smul, phi_smul, phi_sPlus, phi_sMinus]
    refine M2Q.ext ?_ ?_ ?_ ?_
    · show (phi x).m00 = (phi x).m00 * 1 + (phi x).m10 * 0
      rw [RatQ.mul_one, RatQ.mul_zero, RatQ.add_zero]
    · show (phi x).m01 = (phi x).m00 * 0 + (phi x).m10 * 0
      rw [h01, RatQ.mul_zero, RatQ.mul_zero, RatQ.add_zero]
    · show (phi x).m10 = (phi x).m00 * 0 + (phi x).m10 * 1
      rw [RatQ.mul_zero, RatQ.zero_add, RatQ.mul_one]
    · show (phi x).m11 = (phi x).m00 * 0 + (phi x).m10 * 0
      rw [h11, RatQ.mul_zero, RatQ.mul_zero, RatQ.add_zero]
  have hpsi := congrArg psi hphi_eq
  rw [psi_phi, psi_phi] at hpsi
  exact hpsi

/-- Contrast with minimal *two-sided* ideals: `Cl_{1,1}(ℚ) ≅ M_2(ℚ)` is a simple ring, so its
    unique minimal nonzero two-sided ideal is the full 4-dimensional algebra (`dim = 4 ≠ 2`). -/
def FullCl11 (_ : Cl11Q) : Prop := True

theorem fullCl11_hasDim_four : HasQDim Cl11Alg FullCl11 4 := by
  refine ⟨{
    toVec := fun x _ ⟨i, hi⟩ =>
      match i, hi with
      | 0, _ => x.a0
      | 1, _ => x.a1
      | 2, _ => x.a2
      | 3, _ => x.a12
    ofVec := fun v => ⟨v ⟨0, by decide⟩, v ⟨1, by decide⟩, v ⟨2, by decide⟩, v ⟨3, by decide⟩⟩
    ofVec_mem := fun _ => trivial
    left_inv := fun x _ => by cases x; rfl
    right_inv := fun v => by
      funext ⟨i, hi⟩
      match i, hi with
      | 0, _ => rfl
      | 1, _ => rfl
      | 2, _ => rfl
      | 3, _ => rfl
    ofVec_add := fun _ _ => rfl
    ofVec_smul := fun _ _ => rfl
  }⟩

theorem fullCl11_not_dim_two : ¬ HasQDim Cl11Alg FullCl11 2 :=
  dim_four_not_dim_two fullCl11_hasDim_four

end Cl11
end SpinorMinimalIdeals
