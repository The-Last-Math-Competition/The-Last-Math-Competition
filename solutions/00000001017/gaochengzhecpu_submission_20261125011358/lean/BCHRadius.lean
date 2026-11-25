import Std

namespace C1017

private instance decidableFinForall {n : Nat} {P : Fin n → Prop}
    [dec : (i : Fin n) → Decidable (P i)] : Decidable (∀ i, P i) := by
  induction n with
  | zero => exact isTrue (fun i => Fin.elim0 i)
  | succ n ih =>
    letI : Decidable (∀ i : Fin n, P i.succ) := ih
    exact decidable_of_iff _ Fin.forall_fin_succ.symm

private instance decidableFinExists {n : Nat} {P : Fin n → Prop}
    [dec : (i : Fin n) → Decidable (P i)] : Decidable (∃ i, P i) := by
  induction n with
  | zero => exact isFalse (fun ⟨i, _⟩ => Fin.elim0 i)
  | succ n ih =>
    letI : Decidable (∃ i : Fin n, P i.succ) := ih
    exact decidable_of_iff _ Fin.exists_fin_succ.symm

/-- A binary word represents the polynomial with the least significant bit as its constant. -/
abbrev Word := Fin (2 ^ 7)

def distance (w v : Word) : Nat :=
  (List.finRange 7).countP fun i =>
    (BitVec.ofFin w).getLsbD i.val != (BitVec.ofFin v).getLsbD i.val

/-- Multiply binary polynomials using shift and XOR on seven coefficient bits.
For both encoders below, the product degree is at most six. -/
def encode (generator : BitVec 7) (q : Fin (2 ^ k)) : Word :=
  ((List.finRange k).foldl (fun (accum : BitVec 7) (i : Fin k) =>
    if (BitVec.ofFin q).getLsbD i.val then accum ^^^ (generator <<< i.val) else accum) 0).toFin

def hammingGenerator : BitVec 7 := 11
def repetitionGenerator : BitVec 7 := 127

def hammingEncoder (q : Fin (2 ^ 4)) : Word := encode hammingGenerator q
def repetitionEncoder (q : Fin (2 ^ 1)) : Word := encode repetitionGenerator q

/-- Multiplication by alpha in F₂[alpha]/(alpha³+alpha+1), using alpha³=alpha+1. -/
def multiplyAlpha (w : BitVec 3) : BitVec 3 :=
  (w <<< (1 : Nat)) ^^^ (if w.getLsbD 2 then 3 else 0)

def alphaPower : Nat → BitVec 3
  | 0 => 1
  | n + 1 => multiplyAlpha (alphaPower n)

theorem alpha_order_seven :
    alphaPower 7 = 1 ∧ ∀ j : Fin 7, j.val ≠ 0 → alphaPower j.val ≠ 1 := by
  decide

def evaluateAtAlphaPower (w : Word) (p : Nat) : BitVec 3 :=
  (List.finRange 7).foldl (init := 0) fun accum i =>
    if (BitVec.ofFin w).getLsbD i.val then accum ^^^ alphaPower (p * i.val) else accum

/-- For a designed distance of `roots + 1`, the starting exponent is one. -/
def rootConditions (roots : Nat) (w : Word) : Prop :=
  ∀ j : Fin roots, evaluateAtAlphaPower w (j.val + 1) = 0

private instance (roots : Nat) (w : Word) : Decidable (rootConditions roots w) := by
  unfold rootConditions
  infer_instance

set_option maxRecDepth 3072 in
set_option maxHeartbeats 2500000 in
theorem hamming_designed_distance_three :
    ∀ w : Word, (∃ q, hammingEncoder q = w) ↔ rootConditions 2 w := by
  decide

set_option maxRecDepth 3072 in
set_option maxHeartbeats 2500000 in
theorem repetition_designed_distance_seven :
    ∀ w : Word, (∃ q, repetitionEncoder q = w) ↔ rootConditions 6 w := by
  decide

def Covers (encoder : Fin n → Word) (r : Nat) : Prop :=
  ∀ w : Word, ∃ q, distance w (encoder q) ≤ r

def HasCoveringRadius (encoder : Fin n → Word) (r : Nat) : Prop :=
  Covers encoder r ∧ ∀ smaller < r, ¬ Covers encoder smaller

private theorem covers_mono {encoder : Fin n → Word} {r s : Nat} (bound : r ≤ s)
    (cover : Covers encoder r) : Covers encoder s := by
  intro w
  obtain ⟨q, close⟩ := cover w
  exact ⟨q, Nat.le_trans close bound⟩

set_option maxRecDepth 3072 in
set_option maxHeartbeats 2500000 in
theorem hamming_covers_one : Covers hammingEncoder 1 := by
  unfold Covers
  decide

theorem hamming_does_not_cover_zero : ¬ Covers hammingEncoder 0 := by
  intro cover
  have notCovered : ¬ (∃ q, distance 1 (hammingEncoder q) ≤ 0) := by decide
  exact notCovered (cover 1)

theorem hamming_radius_one : HasCoveringRadius hammingEncoder 1 := by
  refine ⟨hamming_covers_one, ?_⟩
  intro smaller strict cover
  exact hamming_does_not_cover_zero (covers_mono (by omega : smaller ≤ 0) cover)

set_option maxRecDepth 3072 in
set_option maxHeartbeats 2500000 in
theorem repetition_covers_three : Covers repetitionEncoder 3 := by
  unfold Covers
  decide

theorem repetition_does_not_cover_two : ¬ Covers repetitionEncoder 2 := by
  intro cover
  have notCovered : ¬ (∃ q, distance 7 (repetitionEncoder q) ≤ 2) := by decide
  exact notCovered (cover 7)

theorem repetition_radius_three : HasCoveringRadius repetitionEncoder 3 := by
  refine ⟨repetition_covers_three, ?_⟩
  intro smaller strict cover
  exact repetition_does_not_cover_two (covers_mono (by omega : smaller ≤ 2) cover)

def proposedRadius (m : Nat) : Nat := 2 ^ ((m + 1) / 2) - 1

theorem counterexample :
    (2 ^ 3 - 1 : Nat) = 7 ∧ proposedRadius 3 = 3 ∧
      HasCoveringRadius hammingEncoder 1 ∧ HasCoveringRadius repetitionEncoder 3 ∧
      ¬ HasCoveringRadius hammingEncoder (proposedRadius 3) := by
  refine ⟨by decide, by decide, hamming_radius_one, repetition_radius_three, ?_⟩
  intro hypothesized
  exact hypothesized.2 1 (by decide) hamming_covers_one

theorem no_common_radius :
    ¬ ∃ r, HasCoveringRadius hammingEncoder r ∧ HasCoveringRadius repetitionEncoder r := by
  rintro ⟨r, hamming, repetition⟩
  by_cases small : r < 3
  · exact repetition_radius_three.2 r small repetition.1
  · have strict : 1 < r := by omega
    exact hamming.2 1 strict hamming_covers_one

def CoversByRoots (roots r : Nat) : Prop :=
  ∀ w : Word, ∃ c : Word, rootConditions roots c ∧ distance w c ≤ r

def RootCodeRadius (roots r : Nat) : Prop :=
  CoversByRoots roots r ∧ ∀ smaller < r, ¬ CoversByRoots roots smaller

private theorem covers_iff_roots {encoder : Fin n → Word} {roots r : Nat}
    (representation : ∀ w, (∃ q, encoder q = w) ↔ rootConditions roots w) :
    Covers encoder r ↔ CoversByRoots roots r := by
  constructor
  · intro covered w
    obtain ⟨q, close⟩ := covered w
    exact ⟨encoder q, (representation (encoder q)).mp ⟨q, rfl⟩, close⟩
  · intro covered w
    obtain ⟨c, rootsHold, close⟩ := covered w
    obtain ⟨q, rfl⟩ := (representation c).mpr rootsHold
    exact ⟨q, close⟩

private theorem radius_iff_roots {encoder : Fin n → Word} {roots r : Nat}
    (representation : ∀ w, (∃ q, encoder q = w) ↔ rootConditions roots w) :
    HasCoveringRadius encoder r ↔ RootCodeRadius roots r := by
  simp only [HasCoveringRadius, RootCodeRadius, covers_iff_roots representation]

theorem bch_counterexample :
    (2 ^ 3 - 1 : Nat) = 7 ∧ proposedRadius 3 = 3 ∧
      RootCodeRadius 2 1 ∧ RootCodeRadius 6 3 ∧ ¬ RootCodeRadius 2 (proposedRadius 3) := by
  obtain ⟨length, predicted, hamming, repetition, refuted⟩ := counterexample
  refine ⟨length, predicted, (radius_iff_roots hamming_designed_distance_three).mp hamming,
    (radius_iff_roots repetition_designed_distance_seven).mp repetition, ?_⟩
  exact fun h => refuted ((radius_iff_roots hamming_designed_distance_three).mpr h)

#print axioms hamming_designed_distance_three
#print axioms repetition_designed_distance_seven
#print axioms bch_counterexample
#print axioms no_common_radius

end C1017
