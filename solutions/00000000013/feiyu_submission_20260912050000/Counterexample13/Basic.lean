import Std

set_option maxRecDepth 1000000

namespace Counterexample13

/-- A number is composite when it has a proper divisor strictly larger than `1`.
The divisor is represented by `Fin n`, so it is automatically smaller than `n`. -/
def Composite (n : Nat) : Prop :=
  ∃ d : Fin n, 1 < d.val ∧ d.val ∣ n

/-- The 28 integers in `[2^8, 2^9)` whose binary expansion has exactly three `1`s. -/
def candidates : List Nat :=
  [259, 261, 262, 265, 266, 268, 273, 274,
   276, 280, 289, 290, 292, 296, 304, 321,
   322, 324, 328, 336, 352, 385, 386, 388,
   392, 400, 416, 448]

theorem candidate_259 : Composite 259 := by
  exact ⟨⟨7, by decide⟩, by decide, by exact ⟨37, by decide⟩⟩

theorem candidate_261 : Composite 261 := by
  exact ⟨⟨3, by decide⟩, by decide, by exact ⟨87, by decide⟩⟩

theorem candidate_262 : Composite 262 := by
  exact ⟨⟨2, by decide⟩, by decide, by exact ⟨131, by decide⟩⟩

theorem candidate_265 : Composite 265 := by
  exact ⟨⟨5, by decide⟩, by decide, by exact ⟨53, by decide⟩⟩

theorem candidate_266 : Composite 266 := by
  exact ⟨⟨2, by decide⟩, by decide, by exact ⟨133, by decide⟩⟩

theorem candidate_268 : Composite 268 := by
  exact ⟨⟨2, by decide⟩, by decide, by exact ⟨134, by decide⟩⟩

theorem candidate_273 : Composite 273 := by
  exact ⟨⟨3, by decide⟩, by decide, by exact ⟨91, by decide⟩⟩

theorem candidate_274 : Composite 274 := by
  exact ⟨⟨2, by decide⟩, by decide, by exact ⟨137, by decide⟩⟩

theorem candidate_276 : Composite 276 := by
  exact ⟨⟨2, by decide⟩, by decide, by exact ⟨138, by decide⟩⟩

theorem candidate_280 : Composite 280 := by
  exact ⟨⟨2, by decide⟩, by decide, by exact ⟨140, by decide⟩⟩

theorem candidate_289 : Composite 289 := by
  exact ⟨⟨17, by decide⟩, by decide, by exact ⟨17, by decide⟩⟩

theorem candidate_290 : Composite 290 := by
  exact ⟨⟨2, by decide⟩, by decide, by exact ⟨145, by decide⟩⟩

theorem candidate_292 : Composite 292 := by
  exact ⟨⟨2, by decide⟩, by decide, by exact ⟨146, by decide⟩⟩

theorem candidate_296 : Composite 296 := by
  exact ⟨⟨2, by decide⟩, by decide, by exact ⟨148, by decide⟩⟩

theorem candidate_304 : Composite 304 := by
  exact ⟨⟨2, by decide⟩, by decide, by exact ⟨152, by decide⟩⟩

theorem candidate_321 : Composite 321 := by
  exact ⟨⟨3, by decide⟩, by decide, by exact ⟨107, by decide⟩⟩

theorem candidate_322 : Composite 322 := by
  exact ⟨⟨2, by decide⟩, by decide, by exact ⟨161, by decide⟩⟩

theorem candidate_324 : Composite 324 := by
  exact ⟨⟨2, by decide⟩, by decide, by exact ⟨162, by decide⟩⟩

theorem candidate_328 : Composite 328 := by
  exact ⟨⟨2, by decide⟩, by decide, by exact ⟨164, by decide⟩⟩

theorem candidate_336 : Composite 336 := by
  exact ⟨⟨2, by decide⟩, by decide, by exact ⟨168, by decide⟩⟩

theorem candidate_352 : Composite 352 := by
  exact ⟨⟨2, by decide⟩, by decide, by exact ⟨176, by decide⟩⟩

theorem candidate_385 : Composite 385 := by
  exact ⟨⟨5, by decide⟩, by decide, by exact ⟨77, by decide⟩⟩

theorem candidate_386 : Composite 386 := by
  exact ⟨⟨2, by decide⟩, by decide, by exact ⟨193, by decide⟩⟩

theorem candidate_388 : Composite 388 := by
  exact ⟨⟨2, by decide⟩, by decide, by exact ⟨194, by decide⟩⟩

theorem candidate_392 : Composite 392 := by
  exact ⟨⟨2, by decide⟩, by decide, by exact ⟨196, by decide⟩⟩

theorem candidate_400 : Composite 400 := by
  exact ⟨⟨2, by decide⟩, by decide, by exact ⟨200, by decide⟩⟩

theorem candidate_416 : Composite 416 := by
  exact ⟨⟨2, by decide⟩, by decide, by exact ⟨208, by decide⟩⟩

theorem candidate_448 : Composite 448 := by
  exact ⟨⟨2, by decide⟩, by decide, by exact ⟨224, by decide⟩⟩

/-- Every candidate in the explicit list is composite. -/
theorem all_candidates_composite :
    ∀ n, n ∈ candidates → Composite n := by
  intro n hn
  simp [candidates] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  · exact candidate_259
  · exact candidate_261
  · exact candidate_262
  · exact candidate_265
  · exact candidate_266
  · exact candidate_268
  · exact candidate_273
  · exact candidate_274
  · exact candidate_276
  · exact candidate_280
  · exact candidate_289
  · exact candidate_290
  · exact candidate_292
  · exact candidate_296
  · exact candidate_304
  · exact candidate_321
  · exact candidate_322
  · exact candidate_324
  · exact candidate_328
  · exact candidate_336
  · exact candidate_352
  · exact candidate_385
  · exact candidate_386
  · exact candidate_388
  · exact candidate_392
  · exact candidate_400
  · exact candidate_416
  · exact candidate_448

/-- A natural number is prime in the elementary sense used here. -/
def Prime (n : Nat) : Prop :=
  1 < n ∧ ¬ Composite n

/-- The exact three-one binary patterns in `[2^8, 2^9)`, written by their
three nonzero binary positions. The leading position is `8`; the other two
positions are distinct elements of `Fin 8`. -/
def ThreeOnePattern8 (p : Nat) : Prop :=
  ∃ a b : Fin 8, b.val < a.val ∧
    p = 2 ^ 8 + 2 ^ a.val + 2 ^ b.val

/-- Every three-one binary pattern in `[2^8, 2^9)` is composite. -/
theorem all_three_one_patterns_composite :
    ∀ (a b : Fin 8), b.val < a.val →
      Composite (2 ^ 8 + 2 ^ a.val + 2 ^ b.val) := by
  change ∀ (a b : Fin 8), b.val < a.val →
    ∃ d : Fin (2 ^ 8 + 2 ^ a.val + 2 ^ b.val),
      1 < d.val ∧ d.val ∣ (2 ^ 8 + 2 ^ a.val + 2 ^ b.val)
  decide

/-- The conjecture is false at `n = 8`: no three-one binary pattern in the
interval is prime. -/
theorem counterexample_n8 :
    ¬ ∃ p, ThreeOnePattern8 p ∧ Prime p := by
  intro h
  rcases h with ⟨p, ⟨a, b, hab, rfl⟩, hp⟩
  exact hp.2 (all_three_one_patterns_composite a b hab)

end Counterexample13
