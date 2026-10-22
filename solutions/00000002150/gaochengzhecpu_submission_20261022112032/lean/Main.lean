import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open Finset Matrix

namespace Signless

set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def signless : Matrix V V ℝ := G.degMatrix ℝ + G.adjMatrix ℝ

theorem quadratic (x : V → ℝ) :
    toLinearMap₂' ℝ (signless G) x x =
      (∑ i : V, ∑ j : V, if G.Adj i j then (x i + x j)^2 else 0) / 2 := by
  simp_rw [toLinearMap₂'_apply', signless, add_mulVec, dotProduct_add,
    G.dotProduct_mulVec_degMatrix, G.dotProduct_mulVec_adjMatrix,
    ← sum_add_distrib, G.degree_eq_sum_if_adj, sum_mul, ite_mul, one_mul,
    zero_mul, ← sum_add_distrib, ite_add_ite, add_zero]
  rw [← add_self_div_two (∑ x_1 : V, ∑ x_2 : V, _)]
  conv_lhs => enter [1,2,2,i,2,j]; rw [if_congr (G.adj_comm i j) rfl rfl]
  conv_lhs => enter [1,2]; rw [Finset.sum_comm]
  simp_rw [← sum_add_distrib, ite_add_ite]
  congr 2 with i
  congr 2 with j
  ring_nf

theorem psd : PosSemidef (signless G) := by
  constructor
  · rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]
    exact G.isSymm_degMatrix.add G.isSymm_adjMatrix
  · intro x
    rw [star_trivial, ← toLinearMap₂'_apply', quadratic]
    positivity

theorem ker_iff (x : V → ℝ) :
    Matrix.toLin' (signless G) x = 0 ↔ ∀ i j : V, G.Adj i j → x i = -x j := by
  rw [← (psd G).toLinearMap₂'_zero_iff, star_trivial, quadratic]
  simp (disch := intros; positivity) [sum_eq_zero_iff_of_nonneg, add_eq_zero_iff_eq_neg]

theorem reachable_sq {x : V → ℝ}
    (hx : ∀ i j, G.Adj i j → x i = -x j) {i j : V} (h : G.Reachable i j) :
    x i ^ 2 = x j ^ 2 := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => rfl
  | cons hij _ ih => rw [hx _ _ hij, neg_sq, ih]

def BipartiteComponent (c : G.ConnectedComponent) : Prop := (G.induce c.supp).Colorable 2

abbrev BipComponents := {c : G.ConnectedComponent // BipartiteComponent G c}

noncomputable instance : Fintype (BipComponents G) := Fintype.ofFinite _

noncomputable def componentColor (c : BipComponents G) :
    (G.induce c.val.supp).Coloring (Fin 2) := Classical.choice c.prop

noncomputable def colorSign (c : BipComponents G) (v : c.val.supp) : ℝ :=
  if componentColor G c v = 0 then 1 else -1

theorem colorSign_sq (c : BipComponents G) (v : c.val.supp) :
    colorSign G c v ^ 2 = 1 := by
  unfold colorSign
  split_ifs <;> norm_num

theorem colorSign_adj (c : BipComponents G) {v w : c.val.supp}
    (h : (G.induce c.val.supp).Adj v w) : colorSign G c v = -colorSign G c w := by
  have hn := (componentColor G c).valid h
  have hv := (componentColor G c v).isLt
  have hw := (componentColor G c w).isLt
  unfold colorSign
  split_ifs with h₁ h₂ h₂
  · exact (hn (h₁.trans h₂.symm)).elim
  · norm_num
  · norm_num
  · have heq : componentColor G c v = componentColor G c w := by
      apply Fin.ext
      have hv₀ : (componentColor G c v).val ≠ 0 := by simpa using h₁
      have hw₀ : (componentColor G c w).val ≠ 0 := by simpa using h₂
      omega
    exact (hn heq).elim

theorem nonzero_component_bipartite {x : V → ℝ}
    (hx : ∀ i j, G.Adj i j → x i = -x j) {c : G.ConnectedComponent}
    {v : V} (hv : v ∈ c.supp) (hvn : x v ≠ 0) : BipartiteComponent G c := by
  have hn (w : c.supp) : x w ≠ 0 := by
    intro hw
    have hreach : G.Reachable v w :=
      SimpleGraph.ConnectedComponent.eq.mp (hv.trans w.prop.symm)
    have hs := reachable_sq G hx hreach
    rw [hw, zero_pow (by decide : 2 ≠ 0)] at hs
    exact hvn (sq_eq_zero_iff.mp hs)
  refine ⟨SimpleGraph.Coloring.mk
    (fun w : c.supp => if 0 < x w then (0 : Fin 2) else 1) ?_⟩
  intro a b hab
  have he := hx a b hab
  have ha := hn a
  have hb := hn b
  dsimp
  split_ifs with h₁ h₂ h₂
  · exfalso; linarith
  · decide
  · decide
  · exfalso
    apply ha
    linarith

noncomputable def basisVector (c : BipComponents G) (v : V) : ℝ :=
  if h : v ∈ c.val.supp then colorSign G c ⟨v,h⟩ else 0

theorem basisVector_adj (c : BipComponents G) {v w : V} (h : G.Adj v w) :
    basisVector G c v = -basisVector G c w := by
  unfold basisVector
  by_cases hv : v ∈ c.val.supp
  · have hw := (c.val.mem_supp_congr_adj h).mp hv
    simp only [dif_pos hv, dif_pos hw]
    exact colorSign_adj G c h
  · have hw : w ∉ c.val.supp := fun hw => hv ((c.val.mem_supp_congr_adj h).mpr hw)
    simp [hv, hw]

noncomputable def kernelVector (c : BipComponents G) :
    LinearMap.ker (Matrix.toLin' (signless G)) :=
  ⟨basisVector G c, (ker_iff G _).mpr (fun _ _ h => basisVector_adj G c h)⟩

theorem basisVector_eq_zero (c : BipComponents G) {v : V}
    (h : G.connectedComponentMk v ≠ c.val) : basisVector G c v = 0 := by
  simp [basisVector, SimpleGraph.ConnectedComponent.mem_supp_iff, h]

theorem basisVector_sq (c : BipComponents G) {v : V} (hv : v ∈ c.val.supp) :
    basisVector G c v ^ 2 = 1 := by
  simp only [basisVector, dif_pos hv]
  exact colorSign_sq G c ⟨v,hv⟩

theorem sum_on_component (a : BipComponents G → ℝ) (c : BipComponents G)
    {v : V} (hv : v ∈ c.val.supp) :
    ∑ d, a d * basisVector G d v = a c * basisVector G c v := by
  classical
  apply Finset.sum_eq_single c
  · intro d _ hdc
    have hn : G.connectedComponentMk v ≠ d.val := by
      intro he
      apply hdc
      apply Subtype.ext
      exact he.symm.trans hv
    rw [basisVector_eq_zero G d hn, mul_zero]
  · simp

theorem basis_independent : LinearIndependent ℝ (kernelVector G) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro a ha c
  have he := congrArg (fun f : LinearMap.ker (Matrix.toLin' (signless G)) =>
    (f : V → ℝ) c.val.out) ha
  change ((∑ d, a d • kernelVector G d : LinearMap.ker _) : V → ℝ) c.val.out = 0 at he
  have hs : ((∑ d, a d • kernelVector G d : LinearMap.ker _) : V → ℝ) c.val.out =
      ∑ d, a d * basisVector G d c.val.out := by
    simp [kernelVector, Submodule.coe_sum, Finset.sum_apply]
  rw [hs, sum_on_component G a c c.val.out_eq] at he
  have hsq := basisVector_sq G c c.val.out_eq
  have hn : basisVector G c c.val.out ≠ 0 := by
    intro hz
    rw [hz] at hsq
    norm_num at hsq
  exact (mul_eq_zero.mp he).resolve_right hn

theorem reachable_product {x y : V → ℝ}
    (hx : ∀ i j, G.Adj i j → x i = -x j)
    (hy : ∀ i j, G.Adj i j → y i = -y j)
    {i j : V} (h : G.Reachable i j) : x i * y i = x j * y j := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => rfl
  | cons hij _ ih => rw [hx _ _ hij, hy _ _ hij, neg_mul_neg, ih]

noncomputable def coefficient (x : V → ℝ) (c : BipComponents G) : ℝ :=
  x c.val.out * basisVector G c c.val.out

theorem coefficient_reproduces {x : V → ℝ}
    (hx : ∀ i j, G.Adj i j → x i = -x j) (c : BipComponents G)
    {v : V} (hv : v ∈ c.val.supp) :
    coefficient G x c * basisVector G c v = x v := by
  have hreach : G.Reachable c.val.out v :=
    SimpleGraph.ConnectedComponent.eq.mp (c.val.out_eq.trans hv.symm)
  have he := reachable_product G hx (fun _ _ h => basisVector_adj G c h) hreach
  unfold coefficient
  rw [he, mul_assoc, ← pow_two, basisVector_sq G c hv, mul_one]

theorem kernel_expansion (x : LinearMap.ker (Matrix.toLin' (signless G))) :
    ∑ c, coefficient G x c • kernelVector G c = x := by
  classical
  apply Subtype.ext
  ext v
  have hx : ∀ i j, G.Adj i j → (x : V → ℝ) i = -(x : V → ℝ) j := (ker_iff G x).mp x.prop
  change ((∑ c, coefficient G x c • kernelVector G c : LinearMap.ker _) : V → ℝ) v = (x : V → ℝ) v
  have hs : ((∑ c, coefficient G x c • kernelVector G c : LinearMap.ker _) : V → ℝ) v =
      ∑ c, coefficient G x c * basisVector G c v := by
    simp [kernelVector, Submodule.coe_sum, Finset.sum_apply]
  rw [hs]
  by_cases hb : BipartiteComponent G (G.connectedComponentMk v)
  · let c : BipComponents G := ⟨G.connectedComponentMk v, hb⟩
    have hv : v ∈ c.val.supp := rfl
    rw [sum_on_component G _ c hv, coefficient_reproduces G hx c hv]
  · have hxv : (x : V → ℝ) v = 0 := by
      by_contra hn
      exact hb (nonzero_component_bipartite G hx (show v ∈
        (G.connectedComponentMk v).supp from rfl) hn)
    rw [hxv]
    apply Finset.sum_eq_zero
    intro c _
    have hn : G.connectedComponentMk v ≠ c.val := by
      intro he
      exact hb (he ▸ c.prop)
    rw [basisVector_eq_zero G c hn, mul_zero]

theorem basis_spans :
    ⊤ ≤ Submodule.span ℝ (Set.range (kernelVector G)) := by
  intro x _
  rw [Submodule.mem_span_range_iff_exists_fun]
  exact ⟨coefficient G x, kernel_expansion G x⟩

noncomputable def signlessKernelBasis :
    Basis (BipComponents G) ℝ (LinearMap.ker (Matrix.toLin' (signless G))) :=
  Basis.mk (basis_independent G) (basis_spans G)

theorem signlessKernelBasis_apply (c : BipComponents G) (v : V) :
    ((signlessKernelBasis G c : LinearMap.ker (Matrix.toLin' (signless G))) : V → ℝ) v =
      basisVector G c v := by
  simp [signlessKernelBasis, Basis.coe_mk, kernelVector]

theorem nullity_eq_bipartite_components :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (signless G))) =
      Fintype.card (BipComponents G) := by
  classical
  exact Module.finrank_eq_card_basis (signlessKernelBasis G)

theorem zero_on_nonbipartite_component
    (x : LinearMap.ker (Matrix.toLin' (signless G))) {v : V}
    (h : ¬ BipartiteComponent G (G.connectedComponentMk v)) : (x : V → ℝ) v = 0 := by
  by_contra hn
  exact h (nonzero_component_bipartite G ((ker_iff G x).mp x.prop)
    (show v ∈ (G.connectedComponentMk v).supp from rfl) hn)

/-- The source's finite, undirected, simple-graph claim, including its kernel-basis interpretation. -/
def Conjecture : Prop :=
  ∀ (W : Type) [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj],
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (signless H))) =
      Fintype.card (BipComponents H) ∧
    ∃ b : Basis (BipComponents H) ℝ (LinearMap.ker (Matrix.toLin' (signless H))),
      ∀ c v, ((b c : LinearMap.ker (Matrix.toLin' (signless H))) : W → ℝ) v =
        basisVector H c v

theorem conjecture : Conjecture := by
  intro W _ _ H _
  exact ⟨nullity_eq_bipartite_components H,
    signlessKernelBasis H, signlessKernelBasis_apply H⟩

end Signless

#print axioms Signless.ker_iff
#print axioms Signless.signlessKernelBasis
#print axioms Signless.kernel_expansion
#print axioms Signless.nullity_eq_bipartite_components
#print axioms Signless.conjecture
