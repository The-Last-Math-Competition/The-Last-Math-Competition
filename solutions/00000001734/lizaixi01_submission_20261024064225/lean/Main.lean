import Mathlib.GroupTheory.PresentedGroup
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Order

set_option maxHeartbeats 0
set_option maxRecDepth 10000

noncomputable section

namespace TLMC1734

def relatorA : FreeGroup (Fin 3) :=
  FreeGroup.of 2 * FreeGroup.of 0 * (FreeGroup.of 2)⁻¹ *
    (FreeGroup.of 0 * FreeGroup.of 1)⁻¹

def relatorB : FreeGroup (Fin 3) :=
  FreeGroup.of 2 * FreeGroup.of 1 * (FreeGroup.of 2)⁻¹ *
    (FreeGroup.of 1 * FreeGroup.of 0 * FreeGroup.of 1)⁻¹

def relations : Set (FreeGroup (Fin 3)) := {relatorA,relatorB}
abbrev FigureEightGroup := PresentedGroup relations
def loop (i : Fin 3) : FigureEightGroup := PresentedGroup.of i
abbrev SL2Z := Matrix.SpecialLinearGroup (Fin 2) ℤ
abbrev SL2C := Matrix.SpecialLinearGroup (Fin 2) ℂ

theorem group_relation_A : loop 2 * loop 0 * (loop 2)⁻¹ = loop 0 * loop 1 := by
  have h := PresentedGroup.mk_eq_mk_of_mul_inv_mem
    (show relatorA ∈ relations by simp [relations])
  simpa [relatorA, loop, PresentedGroup.of] using h

theorem group_relation_B : loop 2 * loop 1 * (loop 2)⁻¹ = loop 1 * loop 0 * loop 1 := by
  have h := PresentedGroup.mk_eq_mk_of_mul_inv_mem
    (show relatorB ∈ relations by simp [relations])
  simpa [relatorB, loop, PresentedGroup.of] using h

def parameter (n : ℕ) : ℤ := n+3

theorem parameter_injective : Function.Injective parameter := by
  intro n m h
  unfold parameter at h
  omega

theorem parameter_ge_three (n : ℕ) : 3 ≤ parameter n := by
  unfold parameter
  omega

def companion (n : ℕ) : SL2Z :=
  ⟨!![parameter n,-1;1,0], by simp [Matrix.det_fin_two]⟩

def generatorImages (n : ℕ) : Fin 3 → SL2Z := ![1,1,companion n]

theorem generatorImages_relations (n : ℕ) :
    ∀ r ∈ relations, FreeGroup.lift (generatorImages n) r=1 := by
  intro r hr
  simp only [relations, Set.mem_insert_iff, Set.mem_singleton_iff] at hr
  rcases hr with rfl | rfl <;> simp [relatorA, relatorB, generatorImages]

def integerRepresentation (n : ℕ) : FigureEightGroup →* SL2Z :=
  PresentedGroup.toGroup (generatorImages_relations n)

theorem integerRepresentation_loop (n : ℕ) (i : Fin 3) :
    integerRepresentation n (loop i)=generatorImages n i := by
  simp [integerRepresentation, loop]

def complexRepresentation (n : ℕ) : FigureEightGroup →* SL2C :=
  (Matrix.SpecialLinearGroup.map (Int.castRingHom ℂ)).comp (integerRepresentation n)

def character (ρ : FigureEightGroup →* SL2C) (g : FigureEightGroup) : ℂ :=
  Matrix.trace (ρ g : Matrix (Fin 2) (Fin 2) ℂ)

theorem complex_trace_cast (n : ℕ) (g : FigureEightGroup) :
    character (complexRepresentation n) g =
      ((Matrix.trace (integerRepresentation n g : Matrix (Fin 2) (Fin 2) ℤ) : ℤ) : ℂ) := by
  change Matrix.trace ((Int.castRingHom ℂ).mapMatrix
    (integerRepresentation n g : Matrix (Fin 2) (Fin 2) ℤ)) = _
  simp [Matrix.trace, Fin.sum_univ_succ]

theorem all_traces_integral (n : ℕ) (g : FigureEightGroup) :
    ∃ z : ℤ, character (complexRepresentation n) g = (z:ℂ) :=
  ⟨_, complex_trace_cast n g⟩

theorem character_loop_a (n : ℕ) : character (complexRepresentation n) (loop 0)=2 := by
  rw [complex_trace_cast, integerRepresentation_loop]
  simp [generatorImages, Matrix.trace]

theorem character_loop_b (n : ℕ) : character (complexRepresentation n) (loop 1)=2 := by
  rw [complex_trace_cast, integerRepresentation_loop]
  simp [generatorImages, Matrix.trace]

theorem character_loop_t (n : ℕ) :
    character (complexRepresentation n) (loop 2)=(parameter n:ℂ) := by
  rw [complex_trace_cast, integerRepresentation_loop]
  simp [generatorImages, companion, Matrix.trace, Fin.sum_univ_succ]

theorem trace_conjugation (U A : SL2C) :
    Matrix.trace ((U*A*U⁻¹ : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) =
      Matrix.trace (A : Matrix (Fin 2) (Fin 2) ℂ) := by
  change Matrix.trace ((U : Matrix (Fin 2) (Fin 2) ℂ)*
    (A : Matrix (Fin 2) (Fin 2) ℂ)*((U⁻¹ : SL2C) : Matrix (Fin 2) (Fin 2) ℂ)) = _
  rw [Matrix.trace_mul_cycle]
  change Matrix.trace (((U⁻¹*U : SL2C) : Matrix (Fin 2) (Fin 2) ℂ)*
    (A : Matrix (Fin 2) (Fin 2) ℂ)) = _
  simp

theorem characters_equal_of_conjugate (ρ σ : FigureEightGroup →* SL2C)
    (U : SL2C) (h : ∀ g, σ g=U*ρ g*U⁻¹) : character σ=character ρ := by
  funext g
  unfold character
  rw [h g, trace_conjugation]

def allCharacters : Set (FigureEightGroup → ℂ) := Set.range character

def integralCharacters : Set (FigureEightGroup → ℂ) :=
  {χ | χ ∈ allCharacters ∧ ∀ g, ∃ z : ℤ, χ g=(z:ℂ)}

theorem family_integral (n : ℕ) : character (complexRepresentation n) ∈ integralCharacters :=
  ⟨⟨complexRepresentation n,rfl⟩,all_traces_integral n⟩

theorem character_family_injective : Function.Injective (fun n => character (complexRepresentation n)) := by
  intro n m h
  have ht := congrFun h (loop 2)
  change character (complexRepresentation n) (loop 2) =
    character (complexRepresentation m) (loop 2) at ht
  rw [character_loop_t, character_loop_t] at ht
  apply parameter_injective
  exact_mod_cast ht

theorem integral_characters_infinite : Set.Infinite integralCharacters := by
  apply (Set.infinite_range_of_injective character_family_injective).mono
  rintro χ ⟨n,rfl⟩
  exact family_integral n

theorem integral_characters_not_finite : ¬Set.Finite integralCharacters :=
  integral_characters_infinite

theorem family_not_conjugate {n m : ℕ} (hnm : n≠m) :
    ¬∃ U : SL2C, ∀ g, complexRepresentation m g=U*complexRepresentation n g*U⁻¹ := by
  rintro ⟨U,hU⟩
  apply hnm
  apply character_family_injective
  exact (characters_equal_of_conjugate _ _ U hU).symm

def traceDefect : MvPolynomial (Fin 3) ℤ :=
  MvPolynomial.X 2 ^ 2 - MvPolynomial.X 0 - MvPolynomial.X 1 - 1

def characterEquations : Fin 3 → MvPolynomial (Fin 3) ℤ :=
  ![(MvPolynomial.X 0 - 1) * (MvPolynomial.X 1 - 1) - 1,
    (MvPolynomial.X 0 - 2) * traceDefect,
    (MvPolynomial.X 1 - 2) * traceDefect]

def integralTraceCurve : Set (Fin 3 → ℤ) :=
  {p | ∀ i, MvPolynomial.eval p (characterEquations i)=0}

def integerPoint (n : ℕ) : Fin 3 → ℤ := ![2,2,parameter n]

theorem integralTraceCurve_iff (p : Fin 3 → ℤ) : p ∈ integralTraceCurve ↔
    (p 0=2 ∧ p 1=2) ∨ ((p 0-1)*(p 1-1)=1 ∧ p 2^2=p 0+p 1+1) := by
  constructor
  · intro h
    have h0 : (p 0-1)*(p 1-1)-1=0 := by
      simpa [characterEquations] using h 0
    have h1 : (p 0-2)*(p 2^2-p 0-p 1-1)=0 := by
      simpa [characterEquations, traceDefect] using h 1
    have h2 : (p 1-2)*(p 2^2-p 0-p 1-1)=0 := by
      simpa [characterEquations, traceDefect] using h 2
    by_cases hd : p 2^2-p 0-p 1-1=0
    · exact Or.inr ⟨sub_eq_zero.mp h0, by omega⟩
    · have hx := (mul_eq_zero.mp h1).resolve_right hd
      have hy := (mul_eq_zero.mp h2).resolve_right hd
      exact Or.inl ⟨sub_eq_zero.mp hx,sub_eq_zero.mp hy⟩
  · rintro (⟨h0,h1⟩ | ⟨hp,hs⟩) i
    · fin_cases i <;> simp [characterEquations,traceDefect,h0,h1]
    · have hd : p 2^2-p 0-p 1-1=0 := by omega
      fin_cases i <;> simp [characterEquations,traceDefect,hp,hd]

theorem integerPoint_mem_curve (n : ℕ) : integerPoint n ∈ integralTraceCurve := by
  intro i
  fin_cases i <;> simp [characterEquations, traceDefect, integerPoint]

def traceCoordinates (χ : FigureEightGroup → ℂ) : Fin 3 → ℂ :=
  ![χ (loop 0),χ (loop 1),χ (loop 2)]

theorem actual_coordinates (n : ℕ) :
    traceCoordinates (character (complexRepresentation n)) =
      fun i => (integerPoint n i : ℂ) := by
  funext i
  fin_cases i <;> simp [traceCoordinates, integerPoint, character_loop_a, character_loop_t,
    character_loop_b]

theorem integerPoint_injective : Function.Injective integerPoint := by
  intro n m h
  apply parameter_injective
  have hh := congrFun h 2
  simpa [integerPoint] using hh

theorem integral_trace_curve_infinite : Set.Infinite integralTraceCurve := by
  apply (Set.infinite_range_of_injective integerPoint_injective).mono
  rintro p ⟨n,rfl⟩
  exact integerPoint_mem_curve n

theorem curve_points_are_realized (n : ℕ) : ∃ ρ : FigureEightGroup →* SL2C,
    traceCoordinates (character ρ)=(fun i => (integerPoint n i : ℂ)) ∧
      ∀ g, ∃ z : ℤ, character ρ g=(z:ℂ) :=
  ⟨complexRepresentation n,actual_coordinates n,all_traces_integral n⟩

theorem actual_integral_points_infinite :
    Set.Infinite {p : Fin 3 → ℤ | p ∈ integralTraceCurve ∧
      ∃ ρ : FigureEightGroup →* SL2C,
        traceCoordinates (character ρ)=(fun i => (p i : ℂ)) ∧
          ∀ g, ∃ z : ℤ, character ρ g=(z:ℂ)} := by
  apply (Set.infinite_range_of_injective integerPoint_injective).mono
  rintro p ⟨n,rfl⟩
  exact ⟨integerPoint_mem_curve n,curve_points_are_realized n⟩

end TLMC1734
