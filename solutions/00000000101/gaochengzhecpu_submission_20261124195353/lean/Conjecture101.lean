import Std

namespace Conjecture101

def Prime (p : Nat) : Prop := 2 ≤ p ∧ ∀ d : Nat, d ∣ p → d = 1 ∨ d = p

def ConstantPrime (block : List Nat) : Prop :=
  ∃ p, Prime p ∧ ∀ gap ∈ block, gap = p

/-- An admissible gap word has positive distances and no nonempty nonconstant-
    prime block with every distance less than the length of the block. -/
def Admissible (gaps : List Nat) : Prop :=
  (∀ gap ∈ gaps, 0 < gap) ∧
  ∀ block : List Nat, block <:+: gaps →
    block = [] ∨ ConstantPrime block ∨ ∃ gap ∈ block, block.length ≤ gap

theorem admissible_nil : Admissible [] := by
  constructor
  · simp
  · intro block isInfix
    exact Or.inl (List.infix_nil.mp isInfix)

private theorem prefix_left_or_contains_join {block left right : List Nat} {join : Nat}
    (isPrefix : block <+: left ++ join :: right) :
    block <+: left ∨ join ∈ block := by
  induction left generalizing block with
  | nil =>
    cases block with
    | nil => exact Or.inl List.nil_prefix
    | cons gap tail =>
      have align : gap = join := (List.cons_prefix_cons.mp isPrefix).1
      exact Or.inr (align ▸ List.mem_cons_self)
  | cons gap rest ih =>
    cases block with
    | nil => exact Or.inl List.nil_prefix
    | cons first tail =>
      obtain ⟨same, tailPrefix⟩ := List.cons_prefix_cons.mp isPrefix
      rcases ih tailPrefix with leftPrefix | hasJoin
      · exact Or.inl (List.cons_prefix_cons.mpr ⟨same, leftPrefix⟩)
      · exact Or.inr (List.mem_cons_of_mem _ hasJoin)

private theorem infix_left_or_right_or_contains_join
    {block left right : List Nat} {join : Nat}
    (isInfix : block <:+: left ++ join :: right) :
    block <:+: left ∨ (block <:+: right ∨ join ∈ block) := by
  induction left with
  | nil =>
    rcases List.infix_cons_iff.mp isInfix with isPrefix | inRight
    · rcases prefix_left_or_contains_join (left := []) isPrefix with inLeft | hasJoin
      · exact Or.inl inLeft.isInfix
      · exact Or.inr (Or.inr hasJoin)
    · exact Or.inr (Or.inl inRight)
  | cons gap rest ih =>
    rcases List.infix_cons_iff.mp isInfix with isPrefix | infixTail
    · rcases prefix_left_or_contains_join (left := gap :: rest) isPrefix with inLeft | hasJoin
      · exact Or.inl inLeft.isInfix
      · exact Or.inr (Or.inr hasJoin)
    · rcases ih infixTail with inLeft | inRight | hasJoin
      · exact Or.inl (List.infix_cons inLeft)
      · exact Or.inr (Or.inl inRight)
      · exact Or.inr (Or.inr hasJoin)

theorem bridge_gaps {left right : List Nat} {join : Nat}
    (leftAllowed : Admissible left) (rightAllowed : Admissible right)
    (large : left.length + right.length + 1 ≤ join) :
    Admissible (left ++ join :: right) := by
  constructor
  · intro gap member
    rcases List.mem_append.mp member with inLeft | afterLeft
    · exact leftAllowed.1 gap inLeft
    · rcases List.mem_cons.mp afterLeft with rfl | inRight
      · omega
      · exact rightAllowed.1 gap inRight
  · intro block isInfix
    rcases infix_left_or_right_or_contains_join isInfix with inLeft | inRight | hasJoin
    · exact leftAllowed.2 block inLeft
    · exact rightAllowed.2 block inRight
    · right
      right
      refine ⟨join, hasJoin, ?_⟩
      have bound := isInfix.length_le
      simp only [List.length_append, List.length_cons] at bound
      omega

/-- The run-length representation of a finite binary word. The leading and
    trailing zero counts do not form any complete gap between ones. -/
inductive BinaryWord where
  | zeros (length : Nat)
  | marked (leadingZeros : Nat) (gaps : List Nat) (trailingZeros : Nat)

def allowed : BinaryWord → Prop
  | .zeros _ => True
  | .marked _ gaps _ => Admissible gaps

def joinWithZeros (left : BinaryWord) (zeros : Nat) (right : BinaryWord) : BinaryWord :=
  match left, right with
  | .zeros m, .zeros n => .zeros (m + zeros + n)
  | .zeros m, .marked leading gaps trailing => .marked (m + zeros + leading) gaps trailing
  | .marked leading gaps trailing, .zeros n => .marked leading gaps (trailing + zeros + n)
  | .marked leading leftGaps trailing, .marked first rightGaps last =>
      .marked leading (leftGaps ++ (trailing + zeros + first + 1) :: rightGaps) last

theorem transitive_language (left right : BinaryWord)
    (leftAllowed : allowed left) (rightAllowed : allowed right) :
    ∃ zeros, allowed (joinWithZeros left zeros right) := by
  cases left with
  | zeros m =>
    cases right with
    | zeros n => exact ⟨0, trivial⟩
    | marked leading gaps trailing => exact ⟨0, rightAllowed⟩
  | marked leading leftGaps trailing =>
    cases right with
    | zeros n => exact ⟨0, leftAllowed⟩
    | marked first rightGaps last =>
      refine ⟨leftGaps.length + rightGaps.length, ?_⟩
      apply bridge_gaps leftAllowed rightAllowed
      omega

def repeatBlock (copies : Nat) (block : List Nat) : List Nat :=
  (List.replicate copies block).flatten

@[simp] theorem repeatBlock_length (copies : Nat) (block : List Nat) :
    (repeatBlock copies block).length = copies * block.length := by
  simp [repeatBlock]

theorem repeatBlock_mem {copies : Nat} {block : List Nat} {gap : Nat}
    (member : gap ∈ repeatBlock copies block) : gap ∈ block := by
  obtain ⟨inner, inInner, inCopies⟩ := List.mem_flatten.mp member
  simpa only [List.eq_of_mem_replicate inInner] using inCopies

theorem mem_repeatBlock {copies : Nat} {block : List Nat} {gap : Nat}
    (positive : 0 < copies) (member : gap ∈ block) : gap ∈ repeatBlock copies block :=
  List.mem_flatten.mpr ⟨block, List.mem_replicate.mpr ⟨by omega, rfl⟩, member⟩

/-- A nonempty cycle can be repeated arbitrarily often in the language. -/
def AdmissibleCycle (cycle : List Nat) : Prop :=
  cycle ≠ [] ∧ ∀ copies, Admissible (repeatBlock copies cycle)

private theorem member_le_sum {gap : Nat} {block : List Nat} (member : gap ∈ block) :
    gap ≤ block.sum := by
  induction block with
  | nil => simp at member
  | cons head tail ih =>
    rw [List.sum_cons]
    rcases List.mem_cons.mp member with rfl | tailMember
    · omega
    · have bound := ih tailMember
      omega

theorem admissible_cycle_is_constant_prime {cycle : List Nat} (allowedCycle : AdmissibleCycle cycle) :
    ConstantPrime cycle := by
  let copies := cycle.sum + 1
  have cycleLength : 0 < cycle.length := List.length_pos_iff.mpr allowedCycle.1
  have bigLength : cycle.sum < (repeatBlock copies cycle).length := by
    rw [repeatBlock_length]
    have lower : copies ≤ copies * cycle.length := Nat.le_mul_of_pos_right copies cycleLength
    omega
  have partition := (allowedCycle.2 copies).2 _ List.infix_rfl
  rcases partition with empty | ⟨p, prime, allP⟩ | ⟨gap, member, bigGap⟩
  · have emptyLength := congrArg List.length empty
    simp only [List.length_nil] at emptyLength
    omega
  · exact ⟨p, prime, fun gap member => allP gap (mem_repeatBlock (by omega) member)⟩
  · have smallGap : gap ≤ cycle.sum := member_le_sum (repeatBlock_mem member)
    omega

/-- A least-period block cannot be two or more repeats of a shorter block. -/
def Primitive (cycle : List Nat) : Prop :=
  ∀ copies block, cycle = repeatBlock copies block → copies ≤ 1

theorem singleton_primitive (p : Nat) : Primitive [p] := by
  intro copies block eq
  have lengths := congrArg List.length eq
  simp only [List.length_cons, List.length_nil, Nat.zero_add, repeatBlock_length] at lengths
  have positive : 0 < block.length := by
    by_cases zero : block.length = 0
    · simp [zero] at lengths
    · omega
  have copies_le := Nat.le_mul_of_pos_right copies positive
  omega

theorem singleton_admissible_cycle {p : Nat} (prime : Prime p) : AdmissibleCycle [p] := by
  constructor
  · simp
  · intro copies
    have allP (gap : Nat) (member : gap ∈ repeatBlock copies [p]) : gap = p :=
      List.mem_singleton.mp (repeatBlock_mem member)
    constructor
    · intro gap member
      rw [allP gap member]
      exact Nat.zero_lt_of_lt (Nat.lt_of_lt_of_le (by decide : 0 < 2) prime.1)
    · intro block isInfix
      exact Or.inr (Or.inl ⟨p, prime, fun gap member => allP gap (isInfix.mem member)⟩)

/-- The zero configuration has least period 1. A configuration with a 1 is
    represented over one least period by its nonempty primitive cyclic gaps. -/
def InPeriodSpectrum (period : Nat) : Prop :=
  period = 1 ∨ ∃ cycle : List Nat,
    AdmissibleCycle cycle ∧ Primitive cycle ∧ cycle.sum = period

theorem exact_least_period_spectrum (period : Nat) :
    InPeriodSpectrum period ↔ period = 1 ∨ Prime period := by
  constructor
  · intro h
    rcases h with one | ⟨cycle, valid, primitive, sum⟩
    · exact Or.inl one
    · obtain ⟨p, prime, allP⟩ := admissible_cycle_is_constant_prime valid
      have replicate : cycle = List.replicate cycle.length p := List.eq_replicate_of_mem allP
      have short := primitive cycle.length [p] (by simpa [repeatBlock] using replicate)
      have positive : 0 < cycle.length := List.length_pos_iff.mpr valid.1
      have single : cycle.length = 1 := by omega
      rw [single] at replicate
      rw [replicate] at sum
      simp at sum
      exact Or.inr (sum ▸ prime)
  · intro h
    rcases h with one | prime
    · exact Or.inl one
    · exact Or.inr ⟨[period], singleton_admissible_cycle prime,
        singleton_primitive period, by simp⟩

abbrev BinaryPoint := Int → Bool

def Gap (point : BinaryPoint) (start : Int) (distance : Nat) : Prop :=
  0 < distance ∧ point start = true ∧ point (start + (distance : Int)) = true ∧
    ∀ i : Nat, 0 < i → i < distance → point (start + (i : Int)) = false

inductive GapBlock (point : BinaryPoint) : Int → List Nat → Prop where
  | nil (start : Int) : GapBlock point start []
  | cons {start : Int} {distance : Nat} {tail : List Nat}
      (first : Gap point start distance)
      (rest : GapBlock point (start + (distance : Int)) tail) :
      GapBlock point start (distance :: tail)

/-- The same gap rule interpreted on actual two-sided binary configurations. -/
def InShift (point : BinaryPoint) : Prop :=
  ∀ start gaps, GapBlock point start gaps → Admissible gaps

def HasPeriod (point : BinaryPoint) (period : Nat) : Prop :=
  ∀ i : Int, point (i + (period : Int)) = point i

def HasLeastPeriod (point : BinaryPoint) (period : Nat) : Prop :=
  0 < period ∧ HasPeriod point period ∧
    ∀ q : Nat, 0 < q → HasPeriod point q → period ≤ q

def evenlySpaced (distance : Nat) (i : Int) : Bool := decide (i % (distance : Int) = 0)

theorem evenly_spaced_period (distance : Nat) : HasPeriod (evenlySpaced distance) distance := by
  intro i
  simp only [evenlySpaced, Int.add_emod_self]

theorem evenly_spaced_least_period {distance : Nat} (positive : 0 < distance) :
    HasLeastPeriod (evenlySpaced distance) distance := by
  refine ⟨positive, evenly_spaced_period distance, ?_⟩
  intro q qPositive qPeriod
  by_cases enough : distance ≤ q
  · exact enough
  · have stayOn := qPeriod 0
    simp only [evenlySpaced, Int.zero_add, Int.zero_emod, decide_true,
      decide_eq_true_eq, Int.emod_eq_of_lt (by omega : (0 : Int) ≤ q)
        (by omega : (q : Int) < distance)] at stayOn
    omega

theorem gap_le_period {point : BinaryPoint} {start : Int} {distance period : Nat}
    (gap : Gap point start distance) (positive : 0 < period)
    (periodic : HasPeriod point period) : distance ≤ period := by
  by_cases enough : distance ≤ period
  · exact enough
  · have blackout := gap.2.2.2 period positive (by omega)
    rw [periodic start, gap.2.1] at blackout
    contradiction

theorem evenly_spaced_gap {distance gap : Nat} {start : Int} (positive : 0 < distance)
    (hasGap : Gap (evenlySpaced distance) start gap) : gap = distance := by
  have upper := gap_le_period hasGap positive (evenly_spaced_period distance)
  by_cases same : gap = distance
  · exact same
  · have startMod : start % (distance : Int) = 0 := of_decide_eq_true hasGap.2.1
    have endMod : (start + (gap : Int)) % (distance : Int) = 0 :=
      of_decide_eq_true hasGap.2.2.1
    rw [Int.add_emod, startMod, Int.zero_add, Int.emod_emod,
      Int.emod_eq_of_lt (by omega) (by omega)] at endMod
    have gapPositive := hasGap.1
    omega

theorem evenly_spaced_mem_shift {p : Nat} (prime : Prime p) : InShift (evenlySpaced p) := by
  intro start gaps chain
  have pos : 0 < p := by have := prime.1; omega
  have allP : ∀ gap ∈ gaps, gap = p := by
    induction chain with
    | nil => simp
    | cons first rest ih =>
      intro gap member
      rcases List.mem_cons.mp member with rfl | inTail
      · exact evenly_spaced_gap pos first
      · exact ih gap inTail
  constructor
  · intro gap member
    rw [allP gap member]
    exact pos
  · intro block contained
    exact Or.inr (Or.inl ⟨p, prime, fun gap member => allP gap (contained.mem member)⟩)

theorem zero_point_mem_shift : InShift (fun _ => false) := by
  intro start gaps chain
  cases chain with
  | nil => exact admissible_nil
  | cons first rest => have := first.2.1; contradiction

private theorem first_one_within {point : BinaryPoint} {start : Int} {bound : Nat}
    (startOn : point start = true) (positive : 0 < bound)
    (boundOn : point (start + (bound : Int)) = true) :
    ∃ distance, distance ≤ bound ∧ Gap point start distance := by
  induction bound using Nat.strongRecOn with
  | ind bound ih =>
    by_cases earlier : ∃ i : Nat, 0 < i ∧ i < bound ∧ point (start + (i : Int)) = true
    · obtain ⟨i, iPositive, iBefore, iOn⟩ := earlier
      obtain ⟨distance, distanceBound, gap⟩ := ih i iBefore iPositive iOn
      exact ⟨distance, by omega, gap⟩
    · refine ⟨bound, Nat.le_refl _, positive, startOn, boundOn, ?_⟩
      intro i iPositive iBefore
      cases atI : point (start + (i : Int))
      · rfl
      · exact False.elim (earlier ⟨i, iPositive, iBefore, atI⟩)

private theorem arbitrary_gap_block {point : BinaryPoint} {period : Nat}
    (positive : 0 < period) (periodic : HasPeriod point period)
    (start : Int) (on : point start = true) (length : Nat) :
    ∃ gaps, gaps.length = length ∧ GapBlock point start gaps := by
  induction length generalizing start with
  | zero => exact ⟨[], rfl, GapBlock.nil _⟩
  | succ length ih =>
    have endOn : point (start + (period : Int)) = true := (periodic start).trans on
    obtain ⟨distance, _, first⟩ := first_one_within on positive endOn
    obtain ⟨tail, tailLength, rest⟩ := ih _ first.2.2.1
    exact ⟨distance :: tail, by simp [tailLength], GapBlock.cons first rest⟩

private theorem gap_block_bounded {point : BinaryPoint} {period : Nat}
    (positive : 0 < period) (periodic : HasPeriod point period)
    {start : Int} {gaps : List Nat} (chain : GapBlock point start gaps) :
    ∀ gap ∈ gaps, gap ≤ period := by
  induction chain with
  | nil => simp
  | cons first _ ih =>
    intro gap member
    rcases List.mem_cons.mp member with rfl | inTail
    · exact gap_le_period first positive periodic
    · exact ih gap inTail

private theorem values_on_constant_block {point : BinaryPoint} {step count offset : Nat}
    {start : Int} (chain : GapBlock point start (List.replicate count step))
    (startOn : point start = true) (within : offset ≤ count * step) :
    point (start + (offset : Int)) = evenlySpaced step offset := by
  induction count generalizing start offset with
  | zero =>
    have offsetZero : offset = 0 := by simp at within; exact within
    simpa [offsetZero, evenlySpaced] using startOn
  | succ count ih =>
    rw [List.replicate_succ] at chain
    cases chain with
    | cons first rest =>
      by_cases offsetZero : offset = 0
      · simpa [offsetZero, evenlySpaced] using startOn
      by_cases before : offset < step
      · rw [first.2.2.2 offset (by omega) before]
        have modOffset := Int.emod_eq_of_lt (by omega : (0 : Int) ≤ offset)
          (by omega : (offset : Int) < step)
        have castNonzero : (offset : Int) ≠ 0 := by omega
        simp [evenlySpaced, modOffset, castNonzero]
      · let after := offset - step
        have afterWithin : after ≤ count * step := by
          rw [Nat.succ_mul] at within
          omega
        have tailValue := ih rest first.2.2.1 afterWithin
        have reindex : (offset : Int) = (step : Int) + (after : Int) := by omega
        rw [reindex, ← Int.add_assoc, tailValue]
        simp only [evenlySpaced, Int.add_emod_self_left]

private theorem period_nat_multiples {point : BinaryPoint} {period : Nat}
    (periodic : HasPeriod point period) (i : Int) (multiple : Nat) :
    point (i + (multiple : Int) * (period : Int)) = point i := by
  induction multiple with
  | zero => simp
  | succ multiple ih =>
    rw [Int.natCast_add, Int.natCast_one, Int.add_mul, Int.one_mul,
      ← Int.add_assoc, periodic, ih]

private theorem period_int_multiples {point : BinaryPoint} {period : Nat}
    (periodic : HasPeriod point period) (i multiple : Int) :
    point (i + multiple * (period : Int)) = point i := by
  cases multiple with
  | ofNat k => exact period_nat_multiples periodic i k
  | negSucc k =>
    rw [Int.negSucc_eq, ← Int.natCast_succ, Int.neg_mul]
    let delta := ((k + 1 : Nat) : Int) * (period : Int)
    have cancel := period_nat_multiples periodic (i + -delta) (k + 1)
    change point (i + -delta + delta) = point (i + -delta) at cancel
    rw [show i + -delta + delta = i by omega] at cancel
    exact cancel.symm

private theorem period_from_constant_block {point : BinaryPoint} {period step : Nat}
    (positive : 0 < period) (periodic : HasPeriod point period) (stepPositive : 0 < step)
    {start : Int} (startOn : point start = true)
    (chain : GapBlock point start (List.replicate (period + 1) step)) :
    HasPeriod point step := by
  intro i
  let remainder := ((i - start) % (period : Int)).toNat
  let quotient := (i - start) / (period : Int)
  have remNonnegative := Int.emod_nonneg (i - start) (by omega : (period : Int) ≠ 0)
  have remLess := Int.emod_lt_of_pos (i - start) (by omega : (0 : Int) < period)
  have decompose : i = start + (remainder : Int) + quotient * (period : Int) := by
    have division := Int.emod_add_ediv' (i - start) (period : Int)
    have castRemainder : (remainder : Int) = (i - start) % (period : Int) := by omega
    rw [castRemainder]
    dsimp only [quotient]
    omega
  have leftShift : point i = point (start + (remainder : Int)) := by
    rw [decompose]
    exact period_int_multiples periodic _ quotient
  have rightShift : point (i + (step : Int)) = point (start + ((remainder + step : Nat) : Int)) := by
    rw [decompose, Int.natCast_add]
    rw [show start + (remainder : Int) + quotient * (period : Int) + (step : Int) =
      start + ((remainder : Int) + (step : Int)) + quotient * (period : Int) by omega]
    exact period_int_multiples periodic _ quotient
  have fullLength : remainder + step ≤ (period + 1) * step := by
    have spanLowerBound := Nat.le_mul_of_pos_right period stepPositive
    rw [Nat.add_mul, Nat.one_mul]
    omega
  rw [rightShift, leftShift, values_on_constant_block chain startOn fullLength,
    values_on_constant_block chain startOn (by omega)]
  simp only [evenlySpaced, Int.natCast_add, Int.add_emod_self]

private theorem all_gap_lengths_equal {point : BinaryPoint} {period : Nat}
    (inShift : InShift point) (positive : 0 < period) (periodic : HasPeriod point period)
    (start : Int) (on : point start = true) :
    ∃ prime, Prime prime ∧ GapBlock point start (List.replicate (period + 1) prime) := by
  obtain ⟨gaps, length, chain⟩ := arbitrary_gap_block positive periodic start on (period + 1)
  rcases (inShift start gaps chain).2 gaps List.infix_rfl with empty | ⟨prime, isPrime, allPrime⟩ |
      ⟨gap, member, longGap⟩
  · simp [empty] at length
  · have repeated := List.eq_replicate_of_mem allPrime
    rw [length] at repeated
    exact ⟨prime, isPrime, repeated ▸ chain⟩
  · have shortGap := gap_block_bounded positive periodic chain gap member
    omega

theorem binary_point_least_period_is_one_or_prime {point : BinaryPoint} {period : Nat}
    (inShift : InShift point) (least : HasLeastPeriod point period) :
    period = 1 ∨ Prime period := by
  by_cases someOne : ∃ start, point start = true
  · obtain ⟨start, on⟩ := someOne
    obtain ⟨prime, isPrime, chain⟩ := all_gap_lengths_equal inShift least.1 least.2.1 start on
    have primePositive : 0 < prime := by have := isPrime.1; omega
    have primePeriod := period_from_constant_block least.1 least.2.1 primePositive on chain
    have upper := least.2.2 prime primePositive primePeriod
    rw [List.replicate_succ] at chain
    cases chain with
    | cons first _ =>
      have lower := gap_le_period first least.1 least.2.1
      exact Or.inr (show prime = period by omega ▸ isPrime)
  · have constant (i : Int) : point i = false := by
      cases atI : point i
      · rfl
      · exact False.elim (someOne ⟨i, atI⟩)
    have onePeriod : HasPeriod point 1 := fun i => (constant _).trans (constant i).symm
    have upper := least.2.2 1 (by decide) onePeriod
    exact Or.inl (by have := least.1; omega)

theorem binary_subshift_least_period_spectrum (period : Nat) :
    (∃ point : BinaryPoint, InShift point ∧ HasLeastPeriod point period) ↔
    period = 1 ∨ Prime period := by
  constructor
  · intro occurrence
    obtain ⟨_, inShift, least⟩ := occurrence
    exact binary_point_least_period_is_one_or_prime inShift least
  · intro h
    rcases h with rfl | prime
    · exact ⟨fun _ => false, zero_point_mem_shift, by
        refine ⟨by decide, fun _ => rfl, ?_⟩
        intro q qPositive _
        omega⟩
    · have positive : 0 < period := by have := prime.1; omega
      exact ⟨evenlySpaced period, evenly_spaced_mem_shift prime, evenly_spaced_least_period positive⟩

end Conjecture101

#print axioms Conjecture101.transitive_language
#print axioms Conjecture101.exact_least_period_spectrum
#print axioms Conjecture101.binary_subshift_least_period_spectrum
