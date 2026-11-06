import Mathlib.Dynamics.TopologicalEntropy.CoverEntropy
import Mathlib.Topology.UniformSpace.Pi
import Mathlib.Topology.UniformSpace.DiscreteUniformity
import Mathlib.Topology.Compactness.Compact
import Mathlib.Tactic

open Set Filter UniformSpace
open scoped Uniformity Topology

noncomputable section
namespace Conjecture9624

abbrev Alphabet := Fin 3
instance : UniformSpace Alphabet := ⊥
abbrev Config := ℤ → Alphabet

def shift (x : Config) : Config := fun k => x (k + 1)
def unshift (x : Config) : Config := fun k => x (k - 1)

def shiftHomeomorph : Config ≃ₜ Config where
  toFun := shift
  invFun := unshift
  left_inv x := by ext k; simp [shift, unshift]
  right_inv x := by ext k; simp [shift, unshift]
  continuous_toFun := continuous_pi fun k => continuous_apply (k + 1)
  continuous_invFun := continuous_pi fun k => continuous_apply (k - 1)

theorem shift_surjective : Function.Surjective shift := shiftHomeomorph.surjective

theorem shift_uniformContinuous : UniformContinuous shift :=
  uniformContinuous_pi.mpr fun k => Pi.uniformContinuous_proj (fun _ : ℤ => Alphabet) (k+1)

theorem shift_iterate (n : ℕ) (x : Config) (k : ℤ) :
    shift^[n] x k = x (k + (n : ℤ)) := by
  induction n generalizing k with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    change shift^[n] x (k+1) = _
    rw [ih]
    congr 1
    push_cast
    ring

def HasRadius (f : Config → Config) (r : ℕ) : Prop :=
  ∃ rule : (Fin (2*r+1) → Alphabet) → Alphabet,
    ∀ x k, f x k = rule (fun i => x (k + (i : ℕ) - (r : ℤ)))

theorem shift_radius_one : HasRadius shift 1 := by
  refine ⟨fun w => w 2, ?_⟩
  intro x k
  simp [shift]
  congr 1
  ring

theorem unshift_radius_one : HasRadius unshift 1 := by
  refine ⟨fun w => w 0, ?_⟩
  intro x k
  simp [unshift]

theorem shift_not_radius_zero : ¬ HasRadius shift 0 := by
  rintro ⟨rule, hrule⟩
  let x : Config := fun _ => 0
  let y : Config := fun k => if k = 1 then 1 else 0
  have hblock : (fun i : Fin (2*0+1) => x (0 + (i : ℕ) - (0 : ℤ))) =
      (fun i : Fin (2*0+1) => y (0 + (i : ℕ) - (0 : ℤ))) := by
    funext i
    fin_cases i
    norm_num [x, y]
  have hx := hrule x 0
  have hy := hrule y 0
  rw [hblock] at hx
  have heq := hx.trans hy.symm
  norm_num [shift, x, y] at heq

theorem shift_radius_minimal (r : ℕ) (hr : HasRadius shift r) : 1 ≤ r := by
  by_contra h
  have : r = 0 := by omega
  subst r
  exact shift_not_radius_zero hr

theorem shift_commutes : Function.Commute shift shift := fun _ => rfl

theorem configuration_space_compact : IsCompact (univ : Set Config) := isCompact_univ

def zeroEntourage : Set (Config × Config) := {p | p.1 0 = p.2 0}

theorem zeroEntourage_uniform : zeroEntourage ∈ 𝓤 Config := by
  have h := (Pi.uniformContinuous_proj (fun _ : ℤ => Alphabet) 0)
  have hd : idRel ∈ 𝓤 Alphabet := DiscreteUniformity.idRel_mem_uniformity Alphabet
  exact (uniformContinuous_def.mp h) _ hd

abbrev Word (n : ℕ) := Fin n → Alphabet

def readWord (n : ℕ) (x : Config) : Word n := fun i => x (i : ℕ)

def extendWord {n : ℕ} (w : Word n) : Config := fun k =>
  if hk : k.toNat < n ∧ 0 ≤ k then w ⟨k.toNat, hk.1⟩ else 0

@[simp] theorem read_extend (n : ℕ) (w : Word n) : readWord n (extendWord w) = w := by
  funext i
  simp [readWord, extendWord, i.isLt]

theorem full_language (n : ℕ) : Set.range (readWord n) = univ := by
  apply Set.range_eq_univ.mpr
  intro w
  exact ⟨extendWord w, read_extend n w⟩

theorem word_card (n : ℕ) : Fintype.card (Word n) = 3^n := by
  simp [Word, Alphabet]

theorem dynBall_iff (n : ℕ) (x y : Config) :
    y ∈ ball x (Dynamics.dynEntourage shift zeroEntourage n) ↔ readWord n x = readWord n y := by
  rw [Dynamics.mem_ball_dynEntourage]
  simp only [ball, zeroEntourage, mem_preimage, mem_setOf_eq, shift_iterate, zero_add]
  constructor
  · intro h
    funext i
    exact h i i.isLt
  · intro h k hk
    exact congrFun h ⟨k,hk⟩

theorem cylinder_cover_lower (n : ℕ) (s : Finset Config)
    (hs : Dynamics.IsDynCoverOf shift univ zeroEntourage n s) : 3^n ≤ s.card := by
  classical
  have surj : Function.Surjective (fun x : s => readWord n x.val) := by
    intro w
    have hh := hs (show extendWord w ∈ (univ : Set Config) from mem_univ _)
    simp only [Dynamics.IsDynCoverOf, mem_iUnion, exists_prop] at hh
    obtain ⟨x, hx, hclose⟩ := hh
    refine ⟨⟨x,hx⟩, ?_⟩
    rw [← read_extend n w]
    exact (dynBall_iff n x (extendWord w)).mp hclose
  have hh := Fintype.card_le_of_surjective _ surj
  simpa [word_card] using hh

theorem cylinder_cover_upper (n : ℕ) :
    ∃ s : Finset Config, Dynamics.IsDynCoverOf shift univ zeroEntourage n s ∧ s.card = 3^n := by
  classical
  let s := Finset.univ.image (extendWord (n := n))
  refine ⟨s, ?_, ?_⟩
  · intro x _
    simp only [mem_iUnion, exists_prop]
    refine ⟨extendWord (readWord n x), ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨readWord n x, Finset.mem_univ _, rfl⟩
    · rw [dynBall_iff, read_extend]
  · have hinj : Function.Injective (extendWord (n := n)) := by
      intro a b hab
      have := congrArg (readWord n) hab
      simpa using this
    rw [Finset.card_image_of_injective _ hinj]
    exact word_card n

theorem cylinder_coverMincard (n : ℕ) :
    Dynamics.coverMincard shift univ zeroEntourage n = (3^n : ℕ) := by
  apply le_antisymm
  · obtain ⟨s,hs,hcard⟩ := cylinder_cover_upper n
    simpa [hcard] using hs.coverMincard_le_card
  · unfold Dynamics.coverMincard
    refine le_iInf fun s => le_iInf fun hs => ?_
    exact_mod_cast cylinder_cover_lower n s hs

theorem cylinder_entropy :
    Dynamics.coverEntropyEntourage shift univ zeroEntourage = ENNReal.log 3 := by
  unfold Dynamics.coverEntropyEntourage
  simp_rw [cylinder_coverMincard]
  simpa using (ExpGrowth.expGrowthSup_pow (b := (3 : ENNReal)))

theorem log_three_le_topologicalEntropy :
    ENNReal.log 3 ≤ Dynamics.coverEntropy shift univ := by
  rw [← cylinder_entropy]
  exact Dynamics.coverEntropyEntourage_le_coverEntropy shift univ zeroEntourage_uniform

theorem counterexample :
    HasRadius shift 1 ∧ Function.Surjective shift ∧
      (Real.log 2 : EReal) < Dynamics.coverEntropy shift univ := by
  refine ⟨shift_radius_one, shift_surjective, ?_⟩
  have hlog : Real.log 2 < Real.log 3 := Real.log_lt_log (by norm_num) (by norm_num)
  have hh : (Real.log 2 : EReal) < ENNReal.log 3 := by
    rw [show (3 : ENNReal) = ENNReal.ofReal 3 by norm_num,
      ENNReal.log_ofReal_of_pos (by norm_num)]
    exact_mod_cast hlog
  exact hh.trans_le log_three_le_topologicalEntropy

theorem radius_entropy_law_false :
    ¬ ∀ (f : Config ≃ₜ Config) (r : ℕ),
      Function.Commute (f : Config → Config) shift → HasRadius f r →
      Dynamics.coverEntropy f univ ≤ ((r : ℝ) * Real.log 2 : ℝ) := by
  intro h
  have hh := h shiftHomeomorph 1 shift_commutes shift_radius_one
  apply counterexample.2.2.not_le
  simpa [shiftHomeomorph] using hh

#print axioms shiftHomeomorph
#print axioms cylinder_coverMincard
#print axioms cylinder_entropy
#print axioms counterexample
#print axioms shift_radius_minimal
#print axioms radius_entropy_law_false
end Conjecture9624
