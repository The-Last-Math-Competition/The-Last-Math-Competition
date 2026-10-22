import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.NormNum

namespace TLMC742
open Set Function

abbrev Z2 := PadicInt 2
noncomputable def odometer (x : Z2) : Z2 := x + 1

theorem odometer_lipschitz : LipschitzWith 1 odometer := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp [odometer]

theorem odometer_iterate (n : ℕ) (x : Z2) : odometer^[n] x = x + n := by
  induction n with
  | zero => simp
  | succ n ih => simp [Function.iterate_succ_apply', ih, odometer, add_assoc]

theorem odometer_dense_orbit (x : Z2) :
    Dense (Set.range fun n : ℕ => odometer^[n] x) := by
  have h := (Homeomorph.addLeft x).surjective.denseRange.comp
    (PadicInt.denseRange_natCast (p := 2)) (Homeomorph.addLeft x).continuous
  simpa [Function.comp_def, odometer_iterate, DenseRange] using h

/-- A minimal closed subsystem: every forward orbit is dense in the
nonempty closed invariant underlying set. -/
def IsMinimalComponent (f : Z2 → Z2) (K : Set Z2) : Prop :=
  K.Nonempty ∧ IsClosed K ∧ MapsTo f K K ∧
    ∀ x ∈ K, closure (Set.range fun n : ℕ => f^[n] x) = K

theorem odometer_minimal_iff (K : Set Z2) :
    IsMinimalComponent odometer K ↔ K = Set.univ := by
  constructor
  · rintro ⟨hne, _, _, h⟩
    obtain ⟨x, hx⟩ := hne
    rw [← h x hx, (odometer_dense_orbit x).closure_eq]
  · rintro rfl
    exact ⟨Set.univ_nonempty, isClosed_univ, Set.mapsTo_univ _ _,
      fun x _ => (odometer_dense_orbit x).closure_eq⟩

theorem minimal_component_count :
    Nat.card {K : Set Z2 // IsMinimalComponent odometer K} = 1 := by
  rw [Nat.card_eq_one_iff_exists]
  refine ⟨⟨Set.univ, (odometer_minimal_iff _).mpr rfl⟩, ?_⟩
  intro K
  apply Subtype.ext
  exact (odometer_minimal_iff _).mp K.property

theorem counterexample :
    ∃ f : Z2 → Z2, LipschitzWith 1 f ∧
      Nat.card {K : Set Z2 // IsMinimalComponent f K} ≠ 2 ^ (2 - 1) := by
  refine ⟨odometer, odometer_lipschitz, ?_⟩
  rw [minimal_component_count]
  norm_num

noncomputable def translation (a : Z2) (x : Z2) : Z2 := x + a

theorem translation_lipschitz (a : Z2) : LipschitzWith 1 (translation a) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp [translation]

theorem translation_iterate (a : Z2) (n : ℕ) (x : Z2) :
    (translation a)^[n] x = x + n * a := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp [Function.iterate_succ_apply', ih, translation, Nat.cast_add,
      add_mul, add_assoc]

theorem translation_dense_orbit (a : Z2) (ha : IsUnit a) (x : Z2) :
    Dense (Set.range fun n : ℕ => (translation a)^[n] x) := by
  have hsurj : Function.Surjective (fun y : Z2 => y * a) := by
    rcases ha with ⟨u, rfl⟩
    intro y
    refine ⟨y * ↑u⁻¹, ?_⟩
    simp [mul_assoc]
  have hd := hsurj.denseRange.comp (PadicInt.denseRange_natCast (p := 2))
    (continuous_id.mul_const a)
  have h := (Homeomorph.addLeft x).surjective.denseRange.comp hd
    (Homeomorph.addLeft x).continuous
  simpa [Function.comp_def, translation_iterate, DenseRange] using h

def IsMinimalMap (f : Z2 → Z2) : Prop :=
  LipschitzWith 1 f ∧ ∀ x, Dense (Set.range fun n : ℕ => f^[n] x)

theorem translation_minimal (a : Z2) (ha : IsUnit a) :
    IsMinimalMap (translation a) :=
  ⟨translation_lipschitz a, translation_dense_orbit a ha⟩

noncomputable def threeMinimalMaps (i : Fin 3) : {f : Z2 → Z2 // IsMinimalMap f} :=
  ⟨translation (2 * (i.val : Z2) + 1), translation_minimal _ (by
    have h : IsUnit (((2 * i.val + 1 : ℕ) : Z2)) := by
      rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
      norm_num [Nat.coprime_add_self_left, Nat.coprime_mul_iff_left]
    simpa using h)⟩

theorem threeMinimalMaps_injective : Function.Injective threeMinimalMaps := by
  intro i j hij
  have h := congrArg (fun f : {f : Z2 → Z2 // IsMinimalMap f} => f.val 0) hij
  simp only [threeMinimalMaps, translation, zero_add] at h
  have he : 2 * i.val + 1 = 2 * j.val + 1 := by exact_mod_cast h
  apply Fin.ext
  omega

theorem not_exactly_two_minimal_maps :
    ¬ Nonempty ({f : Z2 → Z2 // IsMinimalMap f} ≃ Fin (2 ^ (2 - 1))) := by
  rintro ⟨e⟩
  have h := Fintype.card_le_of_injective (e ∘ threeMinimalMaps)
    (e.injective.comp threeMinimalMaps_injective)
  norm_num at h

end TLMC742
