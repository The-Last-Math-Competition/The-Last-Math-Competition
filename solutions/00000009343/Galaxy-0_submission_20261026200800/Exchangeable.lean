import Std

/-! A genuine two-atom counterexample to an exchangeability-only zero-one law.
The classical iid Hewitt--Savage theorem is not the target. -/
namespace TLMC9343

abbrev Outcome := Bool
abbrev Sequence := Nat → Bool
abbrev Event := Outcome → Prop
abbrev SequenceEvent := Sequence → Prop

/-- The uniform probability on the full power set of the two-element space. -/
noncomputable def probability (E : Event) : Rat := by
  classical
  exact (if E false then (1 : Rat) / 2 else 0) +
    (if E true then (1 : Rat) / 2 else 0)

theorem probability_empty : probability (fun _ => False) = 0 := by
  simp [probability]; decide +kernel
theorem probability_universe : probability (fun _ => True) = 1 := by
  simp [probability]; decide +kernel

theorem probability_bounds (E : Event) : 0 ≤ probability E ∧ probability E ≤ 1 := by
  classical
  by_cases h0 : E false <;> by_cases h1 : E true <;>
    simp [probability, h0, h1] <;> decide +kernel

theorem probability_ext {E F : Event} (h : ∀ b, E b ↔ F b) :
    probability E = probability F := by
  have he : E = F := funext (fun b => propext (h b))
  rw [he]

theorem probability_disjoint_add (E F : Event)
    (h : ∀ b, ¬ (E b ∧ F b)) :
    probability (fun b => E b ∨ F b) = probability E + probability F := by
  classical
  have h0 := h false
  have h1 := h true
  by_cases e0 : E false <;> by_cases e1 : E true <;>
    by_cases f0 : F false <;> by_cases f1 : F true <;>
    simp_all [probability] <;> decide +kernel

/-- In a disjoint countable family on the two-point space, only finitely many
indices can have a nonempty event. This supplies the finite-space reduction
of countable additivity, without any independence assumption. -/
theorem disjoint_family_eventually_empty (E : Nat → Event)
    (h : ∀ i j, i ≠ j → ∀ b, ¬ (E i b ∧ E j b)) :
    ∃ N, ∀ n, N < n → ∀ b, ¬ E n b := by
  classical
  have atom_bound : ∀ b : Bool, ∃ N, ∀ n, N < n → ¬ E n b := by
    intro b
    by_cases he : ∃ k, E k b
    · obtain ⟨k, hk⟩ := he
      refine ⟨k, ?_⟩
      intro n hn hen
      exact h k n (by omega) b ⟨hk, hen⟩
    · refine ⟨0, ?_⟩
      intro n _ hen
      exact he ⟨n, hen⟩
  obtain ⟨i, hi⟩ := atom_bound false
  obtain ⟨j, hj⟩ := atom_bound true
  refine ⟨i+j, ?_⟩
  intro n hn b
  cases b with
  | false => exact hi n (by omega)
  | true => exact hj n (by omega)

def prefixEvent (E : Nat → Event) (M : Nat) : Event :=
  fun b => ∃ n, n < M ∧ E n b

noncomputable def prefixProbabilitySum (E : Nat → Event) : Nat → Rat
  | 0 => 0
  | M+1 => prefixProbabilitySum E M + probability (E M)

theorem prefix_probability (E : Nat → Event)
    (h : ∀ i j, i ≠ j → ∀ b, ¬ (E i b ∧ E j b)) (M : Nat) :
    probability (prefixEvent E M) = prefixProbabilitySum E M := by
  induction M with
  | zero =>
    have he : ∀ b, prefixEvent E 0 b ↔ False := by
      intro b
      simp [prefixEvent]
    rw [probability_ext he, probability_empty]
    rfl
  | succ M ih =>
    have he : ∀ b, prefixEvent E (M+1) b ↔ prefixEvent E M b ∨ E M b := by
      intro b
      constructor
      · rintro ⟨n, hn, hen⟩
        by_cases heq : n = M
        · exact Or.inr (heq ▸ hen)
        · exact Or.inl ⟨n, by omega, hen⟩
      · intro hb
        rcases hb with ⟨n, hn, hen⟩ | hem
        · exact ⟨n, by omega, hen⟩
        · exact ⟨M, by omega, hem⟩
    have hd : ∀ b, ¬ (prefixEvent E M b ∧ E M b) := by
      rintro b ⟨⟨n, hn, hen⟩, hem⟩
      exact h n M (by omega) b ⟨hen, hem⟩
    rw [probability_ext he, probability_disjoint_add _ _ hd, ih]
    rfl

/-- Exact countable additivity in this finite probability space: the partial
sums of a disjoint sequence stabilize to the probability of its countable union. -/
theorem countable_union_probability (E : Nat → Event)
    (h : ∀ i j, i ≠ j → ∀ b, ¬ (E i b ∧ E j b)) :
    ∃ N, ∀ M, N ≤ M →
      probability (fun b => ∃ n, E n b) = prefixProbabilitySum E M := by
  obtain ⟨N, hN⟩ := disjoint_family_eventually_empty E h
  refine ⟨N+1, ?_⟩
  intro M hM
  have he : ∀ b, (∃ n, E n b) ↔ prefixEvent E M b := by
    intro b
    constructor
    · rintro ⟨n, hn⟩
      have hnN : n ≤ N := by
        by_cases hh : n ≤ N
        · exact hh
        · exact False.elim (hN n (by omega) b hn)
      exact ⟨n, by omega, hn⟩
    · rintro ⟨n, _, hn⟩
      exact ⟨n, hn⟩
  rw [probability_ext he]
  exact prefix_probability E h M

/-- Relabel coordinates. No finite-support restriction is imposed here. -/
def relabel (π : Nat → Nat) (x : Sequence) : Sequence := fun n => x (π n)
def Surjective (π : Nat → Nat) : Prop := ∀ n, ∃ m, π m = n
def Bijective (π : Nat → Nat) : Prop :=
  (∀ m n, π m = π n → m = n) ∧ Surjective π

/-- The random sequence is the same fair bit at every coordinate. -/
def X (b : Outcome) : Sequence := fun _ => b

/-- Equality holds for each outcome, stronger than equality in distribution. -/
theorem constant_relabel (b : Outcome) (π : Nat → Nat) : relabel π (X b) = X b := rfl

/-- Full distributional exchangeability, for every event, every coordinate bijection. -/
def Exchangeable (Y : Outcome → Sequence) : Prop :=
  ∀ π, Bijective π → ∀ E : SequenceEvent,
    probability (fun b => E (relabel π (Y b))) = probability (fun b => E (Y b))

theorem X_exchangeable : Exchangeable X := by
  intro π _ E
  rfl

/-- An invariant event on the entire sequence space, not just on the support. -/
def allOnes (x : Sequence) : Prop := ∀ n, x n = true

def Symmetric (E : SequenceEvent) : Prop :=
  ∀ π, Bijective π → ∀ x, E (relabel π x) ↔ E x

theorem allOnes_surjective_invariant (π : Nat → Nat) (hπ : Surjective π)
    (x : Sequence) : allOnes (relabel π x) ↔ allOnes x := by
  constructor
  · intro h n
    obtain ⟨m, hm⟩ := hπ n
    have hval := h m
    simpa [relabel, hm] using hval
  · intro h n
    exact h (π n)

theorem allOnes_symmetric : Symmetric allOnes := by
  intro π hπ x
  exact allOnes_surjective_invariant π hπ.2 x

theorem pullback_allOnes (b : Outcome) : allOnes (X b) ↔ b = true := by
  constructor
  · intro h
    exact h 0
  · intro h n
    exact h

theorem allOnes_probability : probability (fun b => allOnes (X b)) = 1 / 2 := by
  rw [probability_ext pullback_allOnes]
  simp [probability]; decide +kernel

theorem probability_half_not_zero : (1 / 2 : Rat) ≠ 0 := by decide +kernel
theorem probability_half_not_one : (1 / 2 : Rat) ≠ 1 := by decide +kernel

/-- A necessary restriction of the printed exchangeable zero-one assertion to
this genuine probability space. This is NOT the iid Hewitt--Savage theorem. -/
def ExchangeableZeroOne : Prop :=
  ∀ Y : Outcome → Sequence, Exchangeable Y → ∀ E : SequenceEvent, Symmetric E →
    probability (fun b => E (Y b)) = 0 ∨ probability (fun b => E (Y b)) = 1

theorem counterexample : Exchangeable X ∧ Symmetric allOnes ∧
    probability (fun b => allOnes (X b)) = 1 / 2 :=
  ⟨X_exchangeable, allOnes_symmetric, allOnes_probability⟩

theorem conjecture_exchangeability_only_false : ¬ ExchangeableZeroOne := by
  intro h
  have hf := h X X_exchangeable allOnes allOnes_symmetric
  rw [allOnes_probability] at hf
  cases hf with
  | inl hz => exact probability_half_not_zero hz
  | inr ho => exact probability_half_not_one ho

/-- The failure of independence is explicit: P(X0=1,X1=1)=1/2,
whereas P(X0=1)P(X1=1)=1/4. -/
theorem coordinate_marginal (n : Nat) : probability (fun b => X b n = true) = 1 / 2 := by
  simp [probability, X]; decide +kernel

theorem coordinate_joint :
    probability (fun b => X b 0 = true ∧ X b 1 = true) = 1 / 2 := by
  simp [probability, X]; decide +kernel

theorem not_independent_first_two :
    probability (fun b => X b 0 = true ∧ X b 1 = true) ≠
      probability (fun b => X b 0 = true) * probability (fun b => X b 1 = true) := by
  rw [coordinate_joint, coordinate_marginal, coordinate_marginal]
  decide +kernel

end TLMC9343
