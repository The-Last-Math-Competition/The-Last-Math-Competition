import TensorNuclear
import GenericExtreme
import DecompositionBridge

/-!
The ordinary relative-density clause of conjecture 00000007302 fails for the
actual real tensor product of three Euclidean two-dimensional spaces, equipped
with its finite-decomposition nuclear norm. The source does not uniquely define
its additional parameter-space clause; no interpretation of that clause is
asserted here. In particular, this is not a claim about density of convex
combinations, or about density in the boundary.
-/

noncomputable section
open Set Metric
namespace Conjecture7302

/-- Infimum of the sum of products of Euclidean factor norms over all finite
rank-one decompositions, with ordinary coefficients absorbed into the factors. -/
def nuclearNorm (x : Tensor) : ℝ := sInf (DecompositionBridge.ordinaryCosts x)

/-- The actual norm installed on the genuine tensor product is the decomposition
nuclear norm, rather than an unrelated ambient norm. -/
theorem norm_eq_nuclearNorm (x : Tensor) : ‖x‖ = nuclearNorm x := by
  exact (norm_eq_projective x).trans
    (DecompositionBridge.projectiveSeminorm_eq_sInf_ordinaryCosts x)

/-- The nuclear-norm closed unit ball. -/
def nuclearBall : Set Tensor := {x | nuclearNorm x ≤ 1}

theorem nuclearBall_eq_closedBall : nuclearBall = closedBall (0 : Tensor) 1 := by
  ext x
  simp only [nuclearBall, mem_setOf_eq, mem_closedBall, dist_zero_right,
    norm_eq_nuclearNorm]

theorem zero_mem_nuclearBall : (0 : Tensor) ∈ nuclearBall := by
  rw [nuclearBall_eq_closedBall]
  simp

/-- A concrete point of the ball that is outside the closure of its extreme points.
Closure is in the installed nuclear-norm topology. -/
theorem zero_not_mem_closure_extremePoints :
    (0 : Tensor) ∉ closure (nuclearBall.extremePoints ℝ) := by
  rw [nuclearBall_eq_closedBall]
  intro h
  have hs : closure ((closedBall (0 : Tensor) 1).extremePoints ℝ) ⊆
      sphere (0 : Tensor) 1 :=
    closure_minimal GenericExtreme.extremePoints_closedBall_subset_sphere isClosed_sphere
  have hz := hs h
  simp at hz

/-- The exact relative non-density conclusion: the nuclear ball is not contained
in the closure of its real extreme points. -/
theorem nuclear_extremePoints_not_relatively_dense :
    ¬ nuclearBall ⊆ closure (nuclearBall.extremePoints ℝ) := by
  intro h
  exact zero_not_mem_closure_extremePoints (h zero_mem_nuclearBall)

/-- A self-contained witness of the failed density clause. -/
theorem nuclear_ball_counterexample :
    (0 : Tensor) ∈ nuclearBall ∧
    (0 : Tensor) ∉ closure (nuclearBall.extremePoints ℝ) :=
  ⟨zero_mem_nuclearBall, zero_not_mem_closure_extremePoints⟩

end Conjecture7302
