import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-! Conjecture 00000006561: the pullback-composition identity for arbitrary
covariant two-tensors on manifolds, hence for symplectic forms. The proof
uses Mathlib's manifold derivative and its proved chain rule. -/
noncomputable section
namespace SymplecticComposition
open scoped Manifold
variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] (I' : ModelWithCorners ℝ E' H')
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E'']
  {H'' : Type*} [TopologicalSpace H''] (I'' : ModelWithCorners ℝ E'' H'')
  {M'' : Type*} [TopologicalSpace M''] [ChartedSpace H'' M'']

/-- Raw covariant two-tensors. The result holds without extra bilinearity,
closedness or nondegeneracy hypotheses, and thus includes symplectic forms. -/
def Tensor2 := ∀ x : M, TangentSpace I x → TangentSpace I x → ℝ

def pullback (f : M → M') (ω : Tensor2 I' (M := M')) : Tensor2 I (M := M) :=
  fun x u v => ω (f x) (mfderiv I I' f x u) (mfderiv I I' f x v)

theorem pullback_comp (f : M → M') (g : M' → M'')
    (hf : MDifferentiable I I' f) (hg : MDifferentiable I' I'' g)
    (ω : Tensor2 I'' (M := M'')) :
    pullback I I'' (g ∘ f) ω = pullback I I' f (pullback I' I'' g ω) := by
  funext x u v
  simp only [pullback]
  rw [mfderiv_comp x (hg (f x)) (hf x)]
  rfl

/-- Preservation is exactly the pullback identity f*ω'=ω. -/
def Preserves (f : M → M') (ω : Tensor2 I (M := M))
    (ω' : Tensor2 I' (M := M')) : Prop :=
  MDifferentiable I I' f ∧ pullback I I' f ω' = ω

theorem preserves_comp (f : M → M') (g : M' → M'')
    (ω : Tensor2 I (M := M)) (ω' : Tensor2 I' (M := M'))
    (ω'' : Tensor2 I'' (M := M''))
    (hf : Preserves I I' f ω ω') (hg : Preserves I' I'' g ω' ω'') :
    Preserves I I'' (g ∘ f) ω ω'' := by
  refine ⟨hg.1.comp hf.1, ?_⟩
  rw [pullback_comp I I' I'' f g hf.1 hg.1, hg.2, hf.2]

theorem composition_diagram (f : M → M') (g : M' → M'')
    (hf : MDifferentiable I I' f) (hg : MDifferentiable I' I'' g) :
    pullback I I'' (g ∘ f) = pullback I I' f ∘ pullback I' I'' g := by
  funext ω
  exact pullback_comp I I' I'' f g hf hg ω

theorem preserves_id (ω : Tensor2 I (M := M)) : Preserves I I id ω ω := by
  refine ⟨mdifferentiable_id, ?_⟩
  funext x u v
  simp [pullback, mfderiv_id]

/-- Every finite splitting composition of form-preserving self-maps
preserves the same form. -/
theorem preserves_splitting (ω : Tensor2 I (M := M)) (fs : List (M → M))
    (hfs : ∀ f ∈ fs, Preserves I I f ω ω) :
    Preserves I I (fs.foldr (fun f g => f ∘ g) id) ω ω := by
  induction fs with
  | nil => exact preserves_id I ω
  | cons f fs ih =>
    exact preserves_comp I I I _ f ω ω ω
      (ih (fun g hg => hfs g (List.mem_cons_of_mem f hg)))
      (hfs f (List.mem_cons_self))

#print axioms preserves_splitting
#print axioms preserves_comp
#print axioms composition_diagram
end SymplecticComposition
