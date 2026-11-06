import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace TLMC568

abbrev Index := Fin 3
abbrev Polynomials := MvPolynomial Index ℚ
abbrev Ambient := FractionRing Polynomials

def initialCluster (i : Index) : Ambient :=
  algebraMap Polynomials Ambient (MvPolynomial.X i)

theorem initial_independent : AlgebraicIndependent ℚ initialCluster := by
  exact (MvPolynomial.algebraicIndependent_X Index ℚ).map'
    (f := IsScalarTower.toAlgHom ℚ Polynomials Ambient)
    (IsFractionRing.injective Polynomials Ambient)

theorem initial_generates :
    IntermediateField.adjoin ℚ (Set.range initialCluster) = ⊤ := by
  let S := IntermediateField.adjoin ℚ (Set.range initialCluster)
  have hp (p : Polynomials) : algebraMap Polynomials Ambient p ∈ S := by
    induction p using MvPolynomial.induction_on with
    | C c =>
        change (algebraMap Polynomials Ambient) (algebraMap ℚ Polynomials c) ∈ S
        rw [← IsScalarTower.algebraMap_apply ℚ Polynomials Ambient]
        exact S.algebraMap_mem c
    | add p q hp hq => simpa only [map_add] using S.add_mem hp hq
    | mul_X p i hp =>
        exact (map_mul (algebraMap Polynomials Ambient) p (MvPolynomial.X i)) ▸
          S.mul_mem hp (IntermediateField.subset_adjoin ℚ _ ⟨i, rfl⟩)
  apply top_unique
  intro x _
  obtain ⟨p, q, _, rfl⟩ := IsFractionRing.div_surjective Polynomials x
  exact S.div_mem (hp p) (hp q)

theorem independent_of_generates (v : Index → Ambient)
    (h : IntermediateField.adjoin ℚ (Set.range v) = ⊤) :
    AlgebraicIndependent ℚ v := by
  have hf : Algebra.IsAlgebraic (IntermediateField.adjoin ℚ (Set.range v)) Ambient := by
    refine ⟨fun y => ?_⟩
    have hy : y ∈ IntermediateField.adjoin ℚ (Set.range v) := by rw [h]; trivial
    exact isAlgebraic_algebraMap (⟨y, hy⟩ : IntermediateField.adjoin ℚ (Set.range v))
  let : Algebra.IsAlgebraic (Algebra.adjoin ℚ (Set.range v)) Ambient :=
    IntermediateField.isAlgebraic_adjoin_iff_top.mp hf
  exact (Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg_of_finite ℚ v
    initial_independent.cardinalMk_le_trdeg).1

def markovMatrix : Matrix Index Index ℤ := !![0, 2, -2; -2, 0, 2; 2, -2, 0]

def triangleAdjacency (i j : Index) : ℤ :=
  if j = i + 1 then 1 else if i = j + 1 then -1 else 0

def twoTriangleAdjacency : Matrix Index Index ℤ :=
  fun i j => ∑ _ : Fin 2, triangleAdjacency i j

theorem twoTriangleAdjacency_eq : twoTriangleAdjacency = markovMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [twoTriangleAdjacency, triangleAdjacency, markovMatrix, Fin.sum_univ_two] <;>
    decide +kernel

def matrixMutation (B : Matrix Index Index ℤ) (k : Index) : Matrix Index Index ℤ :=
  fun i j => if i = k ∨ j = k then -B i j
    else B i j + (|B i k| * B k j + B i k * |B k j|) / 2

theorem markov_skew : markovMatrix.transpose = -markovMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [markovMatrix, Matrix.transpose_apply]

theorem mutation_markov (k : Index) : matrixMutation markovMatrix k = -markovMatrix := by
  fin_cases k <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [matrixMutation, markovMatrix]

theorem mutation_neg_markov (k : Index) : matrixMutation (-markovMatrix) k = markovMatrix := by
  fin_cases k <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [matrixMutation, markovMatrix]

def exchangeNumerator (v : Index → Ambient) (k : Index) : Ambient :=
  v (k + 1) ^ 2 + v (k + 2) ^ 2

theorem next_ne (k : Index) : k + 1 ≠ k := by fin_cases k <;> decide +kernel
theorem other_ne (k : Index) : k + 2 ≠ k := by fin_cases k <;> decide +kernel

theorem exchangeNumerator_ne_zero (v : Index → Ambient)
    (hv : AlgebraicIndependent ℚ v) (k : Index) : exchangeNumerator v k ≠ 0 := by
  let p : Polynomials := MvPolynomial.X (k + 1) ^ 2 + MvPolynomial.X (k + 2) ^ 2
  have hp : p ≠ 0 := by
    intro h
    have := congrArg (MvPolynomial.eval (fun _ : Index => (1 : ℚ))) h
    norm_num [p] at this
  have h := (algebraicIndependent_iff_injective_aeval.mp hv).ne hp
  simpa only [map_zero, p, map_add, map_pow, MvPolynomial.aeval_X, exchangeNumerator] using h

def mutateCluster (v : Index → Ambient) (k : Index) : Index → Ambient :=
  Function.update v k (exchangeNumerator v k / v k)

theorem mutate_generates (v : Index → Ambient) (hv : AlgebraicIndependent ℚ v)
    (hg : IntermediateField.adjoin ℚ (Set.range v) = ⊤) (k : Index) :
    IntermediateField.adjoin ℚ (Set.range (mutateCluster v k)) = ⊤ := by
  let S := IntermediateField.adjoin ℚ (Set.range (mutateCluster v k))
  have hm (i : Index) : mutateCluster v k i ∈ S :=
    IntermediateField.subset_adjoin ℚ _ ⟨i, rfl⟩
  have ho (i : Index) (hi : i ≠ k) : v i ∈ S := by
    simpa only [mutateCluster, Function.update_of_ne hi] using hm i
  have hn : exchangeNumerator v k ∈ S :=
    S.add_mem (S.pow_mem (ho _ (next_ne k)) 2) (S.pow_mem (ho _ (other_ne k)) 2)
  have hk : v k ∈ S := by
    have hquot : exchangeNumerator v k / v k ∈ S := by
      simpa only [mutateCluster, Function.update_self] using hm k
    have hrec : exchangeNumerator v k / (exchangeNumerator v k / v k) = v k := by
      field_simp [exchangeNumerator_ne_zero v hv k, hv.ne_zero k]
    exact hrec ▸ S.div_mem hn hquot
  apply top_unique
  rw [← hg]
  apply IntermediateField.adjoin_le_iff.mpr
  rintro _ ⟨i, rfl⟩
  change v i ∈ S
  by_cases hi : i = k
  · simpa only [hi] using hk
  · exact ho i hi

@[ext] structure Seed where
  cluster : Index → Ambient
  negative : Bool
  independent : AlgebraicIndependent ℚ cluster
  generates : IntermediateField.adjoin ℚ (Set.range cluster) = ⊤

def Seed.exchangeMatrix (s : Seed) : Matrix Index Index ℤ :=
  if s.negative then -markovMatrix else markovMatrix

def initialSeed : Seed := ⟨initialCluster, false, initial_independent, initial_generates⟩

def Seed.mutate (s : Seed) (k : Index) : Seed where
  cluster := mutateCluster s.cluster k
  negative := !s.negative
  independent := independent_of_generates _ (mutate_generates _ s.independent s.generates k)
  generates := mutate_generates _ s.independent s.generates k

theorem Seed.matrix_mutation (s : Seed) (k : Index) :
    (s.mutate k).exchangeMatrix = matrixMutation s.exchangeMatrix k := by
  cases h : s.negative <;>
    simp [Seed.exchangeMatrix, Seed.mutate, h, mutation_markov, mutation_neg_markov]

theorem Seed.exchange_identity (s : Seed) (k : Index) :
    s.cluster k * (s.mutate k).cluster k =
      s.cluster (k + 1) ^ 2 + s.cluster (k + 2) ^ 2 := by
  simp only [Seed.mutate, mutateCluster, Function.update_self]
  exact mul_div_cancel₀ _ (s.independent.ne_zero k)

theorem Seed.mutate_involutive (s : Seed) (k : Index) : (s.mutate k).mutate k = s := by
  have hn := exchangeNumerator_ne_zero s.cluster s.independent k
  have hk := s.independent.ne_zero k
  cases s with
  | mk v b hi hg =>
    apply Seed.ext
    · funext i
      by_cases h : i = k
      · subst i
        simp only [Seed.mutate, mutateCluster, Function.update_self, exchangeNumerator,
          Function.update_of_ne (next_ne k), Function.update_of_ne (other_ne k)]
        change (v (k + 1) ^ 2 + v (k + 2) ^ 2) /
          ((v (k + 1) ^ 2 + v (k + 2) ^ 2) / v k) = v k
        have hn' : v (k + 1) ^ 2 + v (k + 2) ^ 2 ≠ 0 := hn
        field_simp [hn', hk]
      · simp only [Seed.mutate, mutateCluster, Function.update_of_ne h]
    · simp [Seed.mutate]

def reachableSeed : List Index → Seed
  | [] => initialSeed
  | k :: w => (reachableSeed w).mutate k

def clusterVariables : Set Ambient :=
  {z | ∃ (w : List Index) (i : Index), (reachableSeed w).cluster i = z}

def clusterAlgebra : Subalgebra ℤ Ambient := Algebra.adjoin ℤ clusterVariables

theorem clusterVariable_mem_algebra {z : Ambient} (hz : z ∈ clusterVariables) :
    z ∈ clusterAlgebra := Algebra.subset_adjoin hz

theorem reachable_valid (w : List Index) :
    AlgebraicIndependent ℚ (reachableSeed w).cluster ∧
      IntermediateField.adjoin ℚ (Set.range (reachableSeed w).cluster) = ⊤ :=
  ⟨(reachableSeed w).independent, (reachableSeed w).generates⟩

def denominator : Polynomials := MvPolynomial.X 0 * MvPolynomial.X 1
abbrev LaurentModel := Localization.Away denominator

def localCoordinate (i : Index) : LaurentModel :=
  algebraMap Polynomials LaurentModel (MvPolynomial.X i)

def toAmbient : LaurentModel →+* Ambient :=
  IsLocalization.Away.lift denominator (by
    apply isUnit_iff_ne_zero.mpr
    simpa only [denominator, map_mul, initialCluster] using
      mul_ne_zero (initial_independent.ne_zero 0) (initial_independent.ne_zero 1))

theorem toAmbient_coordinate (i : Index) : toAmbient (localCoordinate i) = initialCluster i := by
  simp [toAmbient, localCoordinate, initialCluster]

theorem toAmbient_injective : Function.Injective toAmbient := by
  apply (IsLocalization.injective_iff_map_algebraMap_eq
    (Submonoid.powers denominator) toAmbient).mpr
  intro p q
  constructor
  · exact congrArg toAmbient
  · intro h
    have h' : algebraMap Polynomials Ambient p = algebraMap Polynomials Ambient q := by
      simpa only [toAmbient, IsLocalization.Away.lift_eq] using h
    exact congrArg (algebraMap Polynomials LaurentModel)
      (IsFractionRing.injective Polynomials Ambient h')

def specialize : LaurentModel →+* ℚ :=
  IsLocalization.Away.lift denominator (g := MvPolynomial.eval (fun _ : Index => (1 : ℚ)))
    (by norm_num [denominator])

theorem specialize_coordinate (i : Index) : specialize (localCoordinate i) = 1 := by
  simp [specialize, localCoordinate]

def linearCoefficient : LaurentModel :=
  (localCoordinate 0 ^ 2 + localCoordinate 1 ^ 2 + localCoordinate 2 ^ 2) *
    IsLocalization.Away.invSelf denominator

theorem linearCoefficient_identity :
    linearCoefficient * localCoordinate 0 * localCoordinate 1 =
      localCoordinate 0 ^ 2 + localCoordinate 1 ^ 2 + localCoordinate 2 ^ 2 := by
  have h : (localCoordinate 0 * localCoordinate 1) *
      IsLocalization.Away.invSelf denominator = 1 := by
    simpa only [denominator, map_mul, localCoordinate] using
      IsLocalization.Away.mul_invSelf (S := LaurentModel) denominator
  dsimp only [linearCoefficient]
  calc
    _ = (localCoordinate 0 ^ 2 + localCoordinate 1 ^ 2 + localCoordinate 2 ^ 2) *
        ((localCoordinate 0 * localCoordinate 1) *
          IsLocalization.Away.invSelf denominator) := by ring
    _ = _ := by rw [h, mul_one]

theorem specialize_linearCoefficient : specialize linearCoefficient = 3 := by
  have h := congrArg specialize linearCoefficient_identity
  norm_num [map_mul, map_add, map_pow, specialize_coordinate] at h
  exact h

def localSequence : ℕ → LaurentModel
  | 0 => localCoordinate 0
  | 1 => localCoordinate 1
  | n + 2 => linearCoefficient * localSequence (n + 1) - localSequence n

theorem localSequence_invariant (n : ℕ) :
    localSequence n ^ 2 + localSequence (n + 1) ^ 2 + localCoordinate 2 ^ 2 =
      linearCoefficient * localSequence n * localSequence (n + 1) := by
  induction n with
  | zero => exact linearCoefficient_identity.symm
  | succ n ih =>
    simp only [localSequence] at *
    linear_combination ih

theorem localSequence_exchange (n : ℕ) :
    localSequence n * localSequence (n + 2) =
      localSequence (n + 1) ^ 2 + localCoordinate 2 ^ 2 := by
  rw [localSequence]
  linear_combination -(localSequence_invariant n)

def positiveMonomial (v : Index → Ambient) (B : Matrix Index Index ℤ) (k : Index) : Ambient :=
  ∏ i : Index, if 0 < B i k then v i ^ (B i k).toNat else 1

def negativeMonomial (v : Index → Ambient) (B : Matrix Index Index ℤ) (k : Index) : Ambient :=
  ∏ i : Index, if B i k < 0 then v i ^ (-B i k).toNat else 1

theorem markov_monomials (v : Index → Ambient) (k : Index) :
    positiveMonomial v markovMatrix k + negativeMonomial v markovMatrix k =
      exchangeNumerator v k := by
  fin_cases k <;>
    simp [positiveMonomial, negativeMonomial, Fin.prod_univ_three, markovMatrix,
      exchangeNumerator, add_comm]

theorem neg_markov_monomials (v : Index → Ambient) (k : Index) :
    positiveMonomial v (-markovMatrix) k + negativeMonomial v (-markovMatrix) k =
      exchangeNumerator v k := by
  fin_cases k <;>
    simp [positiveMonomial, negativeMonomial, Fin.prod_univ_three, markovMatrix,
      exchangeNumerator, add_comm]

theorem Seed.standard_exchange_relation (s : Seed) (k : Index) :
    s.cluster k * (s.mutate k).cluster k =
      positiveMonomial s.cluster s.exchangeMatrix k +
        negativeMonomial s.cluster s.exchangeMatrix k := by
  rw [s.exchange_identity]
  change exchangeNumerator s.cluster k = _
  cases h : s.negative <;>
    simp [Seed.exchangeMatrix, h, markov_monomials, neg_markov_monomials]

theorem Seed.skew_symmetric (s : Seed) : s.exchangeMatrix.transpose = -s.exchangeMatrix := by
  cases h : s.negative <;> simp [Seed.exchangeMatrix, h, markov_skew]

theorem Seed.mutate_other (s : Seed) (k i : Index) (h : i ≠ k) :
    (s.mutate k).cluster i = s.cluster i := by
  simp only [Seed.mutate, mutateCluster, Function.update_of_ne h]

theorem Seed.mutate_same (s : Seed) (k : Index) :
    (s.mutate k).cluster k = exchangeNumerator s.cluster k / s.cluster k := by
  simp only [Seed.mutate, mutateCluster, Function.update_self]

def specializedSequence (n : ℕ) : ℚ := specialize (localSequence n)

theorem specialized_zero : specializedSequence 0 = 1 := by
  simp [specializedSequence, localSequence, specialize_coordinate]

theorem specialized_one : specializedSequence 1 = 1 := by
  simp [specializedSequence, localSequence, specialize_coordinate]

theorem specialized_step (n : ℕ) :
    specializedSequence (n + 2) = 3 * specializedSequence (n + 1) - specializedSequence n := by
  simp only [specializedSequence, localSequence, map_sub, map_mul, specialize_linearCoefficient]

theorem specialized_growth (n : ℕ) :
    0 < specializedSequence (n + 1) ∧ specializedSequence n ≤ specializedSequence (n + 1) := by
  induction n with
  | zero => norm_num [specialized_zero, specialized_one]
  | succ n ih =>
    change 0 < specializedSequence (n + 2) ∧
      specializedSequence (n + 1) ≤ specializedSequence (n + 2)
    rw [specialized_step]
    constructor <;> linarith [ih.1, ih.2]

theorem specialized_positive (n : ℕ) : 0 < specializedSequence n := by
  cases n with
  | zero => norm_num [specialized_zero]
  | succ n => exact (specialized_growth n).1

theorem specialized_strict : StrictMono (fun n : ℕ => specializedSequence (n + 1)) := by
  apply strictMono_nat_of_lt_succ
  intro n
  change specializedSequence (n + 1) < specializedSequence (n + 2)
  rw [specialized_step]
  linarith [(specialized_growth n).1, (specialized_growth n).2]

def ambientSequence (n : ℕ) : Ambient := toAmbient (localSequence n)

theorem ambientSequence_zero : ambientSequence 0 = initialCluster 0 := by
  simp [ambientSequence, localSequence, toAmbient_coordinate]

theorem ambientSequence_one : ambientSequence 1 = initialCluster 1 := by
  simp [ambientSequence, localSequence, toAmbient_coordinate]

theorem ambientSequence_ne_zero (n : ℕ) : ambientSequence n ≠ 0 := by
  intro h
  have hz : localSequence n = 0 := toAmbient_injective (by simpa [ambientSequence] using h)
  have hs : specializedSequence n = 0 := by simp [specializedSequence, hz]
  exact (ne_of_gt (specialized_positive n)) hs

theorem ambientSequence_step (n : ℕ) :
    ambientSequence (n + 2) =
      (ambientSequence (n + 1) ^ 2 + initialCluster 2 ^ 2) / ambientSequence n := by
  apply (eq_div_iff (ambientSequence_ne_zero n)).mpr
  have h := congrArg toAmbient (localSequence_exchange n)
  simpa only [map_mul, map_add, map_pow, toAmbient_coordinate, ambientSequence, mul_comm] using h

def alternatingWord : ℕ → List Index
  | 0 => []
  | n + 1 => 1 :: 0 :: alternatingWord n

theorem alternating_cluster (n : ℕ) :
    (reachableSeed (alternatingWord n)).cluster =
      ![ambientSequence (2 * n), ambientSequence (2 * n + 1), initialCluster 2] := by
  induction n with
  | zero =>
    funext i
    fin_cases i <;>
      simp [alternatingWord, reachableSeed, initialSeed, ambientSequence_zero, ambientSequence_one]
  | succ n ih =>
    let s := reachableSeed (alternatingWord n)
    have hi0 : s.cluster 0 = ambientSequence (2 * n) := congrFun ih 0
    have hi1 : s.cluster 1 = ambientSequence (2 * n + 1) := congrFun ih 1
    have hi2 : s.cluster 2 = initialCluster 2 := congrFun ih 2
    have h0 : (s.mutate 0).cluster 0 = ambientSequence (2 * n + 2) := by
      rw [Seed.mutate_same]
      change (s.cluster 1 ^ 2 + s.cluster 2 ^ 2) / s.cluster 0 = _
      rw [hi0, hi1, hi2]
      exact (ambientSequence_step (2 * n)).symm
    have h1 : ((s.mutate 0).mutate 1).cluster 1 = ambientSequence (2 * n + 3) := by
      rw [Seed.mutate_same]
      change ((s.mutate 0).cluster 2 ^ 2 + (s.mutate 0).cluster 0 ^ 2) /
        (s.mutate 0).cluster 1 = _
      rw [Seed.mutate_other s 0 2 (by decide +kernel),
        Seed.mutate_other s 0 1 (by decide +kernel), hi2, hi1, h0]
      have h := (ambientSequence_step (2 * n + 1)).symm
      norm_num only [Nat.add_assoc] at h
      simpa only [add_comm (initialCluster 2 ^ 2)] using h
    funext i
    fin_cases i
    · change ((s.mutate 0).mutate 1).cluster 0 = ambientSequence (2 * (n + 1))
      rw [Seed.mutate_other (s.mutate 0) 1 0 (by decide +kernel)]
      simpa only [show 2 * (n + 1) = 2 * n + 2 by omega] using h0
    · change ((s.mutate 0).mutate 1).cluster 1 = ambientSequence (2 * (n + 1) + 1)
      simpa only [show 2 * (n + 1) + 1 = 2 * n + 3 by omega] using h1
    · change ((s.mutate 0).mutate 1).cluster 2 = initialCluster 2
      rw [Seed.mutate_other (s.mutate 0) 1 2 (by decide +kernel),
        Seed.mutate_other s 0 2 (by decide +kernel), hi2]

def infiniteFamily (n : ℕ) : Ambient := ambientSequence (2 * n + 1)

theorem infiniteFamily_mem (n : ℕ) : infiniteFamily n ∈ clusterVariables := by
  refine ⟨alternatingWord n, 1, ?_⟩
  exact congrFun (alternating_cluster n) 1

theorem infiniteFamily_injective : Function.Injective infiniteFamily := by
  intro a b hab
  have hl : localSequence (2 * a + 1) = localSequence (2 * b + 1) := toAmbient_injective hab
  have he : specializedSequence (2 * a + 1) = specializedSequence (2 * b + 1) :=
    congrArg specialize hl
  have h := specialized_strict.injective he
  omega

theorem clusterVariables_infinite : clusterVariables.Infinite := by
  apply (Set.infinite_range_of_injective infiniteFamily_injective).mono
  rintro _ ⟨n, rfl⟩
  exact infiniteFamily_mem n

def printedFormula (g : ℕ) : ℕ :=
  6 * g - 3 + ∑ i ∈ Finset.range (2 * g + 1), 2 ^ i * Nat.choose (2 * g) i

theorem printedFormula_one : printedFormula 1 = 12 := by
  norm_num [printedFormula, Finset.sum_range_succ, Nat.choose]

theorem no_finite_cluster_count (N : ℕ) :
    ¬ ∃ s : Finset Ambient, s.card = N ∧ (↑s : Set Ambient) = clusterVariables := by
  rintro ⟨s, _, hs⟩
  exact clusterVariables_infinite (hs ▸ s.finite_toSet)

theorem printed_finite_formula_false :
    ¬ ∃ s : Finset Ambient, s.card = printedFormula 1 ∧
      (↑s : Set Ambient) = clusterVariables := no_finite_cluster_count _

theorem complete_counterexample :
    printedFormula 1 = 12 ∧ clusterVariables.Infinite ∧
    (∀ w : List Index, AlgebraicIndependent ℚ (reachableSeed w).cluster ∧
      IntermediateField.adjoin ℚ (Set.range (reachableSeed w).cluster) = ⊤) ∧
    (∀ z ∈ clusterVariables, z ∈ clusterAlgebra) ∧
    (¬ ∃ s : Finset Ambient, s.card = 12 ∧ (↑s : Set Ambient) = clusterVariables) :=
  ⟨printedFormula_one, clusterVariables_infinite, reachable_valid,
    fun _ h => clusterVariable_mem_algebra h, no_finite_cluster_count 12⟩

end TLMC568
