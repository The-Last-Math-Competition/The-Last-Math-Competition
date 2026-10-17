import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-! Conjecture 00000005030. Sentences are interpreted as measurable events in a
common space of structures. Equal expressive power means mutual definability
by a single sentence, uniformly over all structures and all sizes. -/
namespace ExpressiveConvergence
open Filter MeasureTheory
universe u v w
structure Logic (Ω : Type u) [MeasurableSpace Ω] where
  Sentence : Type v
  models : Sentence → Ω → Prop
  measurable : ∀ φ, MeasurableSet {M | models φ M}

def AtMostExpressive {Ω : Type u} [MeasurableSpace Ω]
    (L : Logic.{u,v} Ω) (K : Logic.{u,w} Ω) : Prop :=
  ∀ φ, ∃ ψ, ∀ M, L.models φ M ↔ K.models ψ M

def SameExpressivePower {Ω : Type u} [MeasurableSpace Ω]
    (L : Logic.{u,v} Ω) (K : Logic.{u,w} Ω) : Prop :=
  AtMostExpressive L K ∧ AtMostExpressive K L

noncomputable def sentenceProbability {Ω : Type u} [MeasurableSpace Ω]
    (μ : ℕ → ProbabilityMeasure Ω) (L : Logic Ω) (φ : L.Sentence) (n : ℕ) : ℝ :=
  ((μ n : Measure Ω) {M | L.models φ M}).toReal

def ConvergenceLaw {Ω : Type u} [MeasurableSpace Ω]
    (μ : ℕ → ProbabilityMeasure Ω) (L : Logic Ω) : Prop :=
  ∀ φ, ∃ r : ℝ, Tendsto (sentenceProbability μ L φ) atTop (nhds r)

theorem transfer {Ω : Type u} [MeasurableSpace Ω]
    (μ : ℕ → ProbabilityMeasure Ω) (L : Logic.{u,v} Ω) (K : Logic.{u,w} Ω)
    (h : AtMostExpressive L K) (hK : ConvergenceLaw μ K) : ConvergenceLaw μ L := by
  intro φ
  obtain ⟨ψ, hψ⟩ := h φ
  obtain ⟨r, hr⟩ := hK ψ
  refine ⟨r, ?_⟩
  have he : {M | L.models φ M} = {M | K.models ψ M} := Set.ext hψ
  have hp : sentenceProbability μ L φ = sentenceProbability μ K ψ := by
    funext n
    unfold sentenceProbability
    rw [he]
  rw [hp]
  exact hr

theorem no_separation {Ω : Type u} [MeasurableSpace Ω]
    (μ : ℕ → ProbabilityMeasure Ω) (L : Logic.{u,v} Ω) (K : Logic.{u,w} Ω)
    (h : SameExpressivePower L K) : ConvergenceLaw μ L ↔ ConvergenceLaw μ K :=
  ⟨transfer μ K L h.2, transfer μ L K h.1⟩

theorem conjecture_false {Ω : Type u} [MeasurableSpace Ω]
    (μ : ℕ → ProbabilityMeasure Ω) :
    ¬ ∃ (L : Logic.{u,v} Ω) (K : Logic.{u,w} Ω),
      SameExpressivePower L K ∧ ¬ (ConvergenceLaw μ L ↔ ConvergenceLaw μ K) := by
  rintro ⟨L, K, he, hd⟩
  exact hd (no_separation μ L K he)

#print axioms conjecture_false
end ExpressiveConvergence
