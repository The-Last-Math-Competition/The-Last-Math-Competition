import RecordSemantics
namespace Records9361
set_option autoImplicit false

def patternCount (n : Nat) (flags : List Bool) : Nat :=
  (perms n).countP (fun p => recs p == flags)
def patternWeight : List Bool → Nat
  | [] => 1
  | b::bs => (if b then 1 else bs.length) * patternWeight bs

theorem insertion_count (n r : Nat) (b : Bool) (bs : List Bool) (hr : r ≤ n) :
  ((perms n).map (fun p => r :: p.map (rise r))).countP (fun p => recs p == b::bs) =
    if (r == n) == b then patternCount n bs else 0 := by
  rw [List.countP_map]
  have h : (perms n).countP ((fun p => recs p == b::bs) ∘ (fun p => r::p.map (rise r))) =
      (perms n).countP (fun p => ((r==n)==b) && (recs p == bs)) := by
    apply List.countP_congr
    intro p hp
    simp only [Function.comp_apply,recs_extend n r p hr ((perms_complete n p).mp hp)]
    simp
  rw [h]
  cases he : ((r==n)==b) <;> simp [patternCount]

theorem sum_constant (l : List Nat) (c : Nat) : (l.map (fun _ => c)).sum = l.length*c := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, Nat.add_mul, Nat.add_comm]

theorem patternCount_step (n : Nat) (b : Bool) (bs : List Bool) :
  patternCount (n+1) (b::bs) = (if b then 1 else n) * patternCount n bs := by
  change (perms (n+1)).countP (fun p => recs p == b::bs) = _
  rw [perms,List.countP_flatMap]
  have h : ((List.range (n+1)).map ((List.countP (fun p => recs p == b::bs)) ∘
      (fun r => (perms n).map (fun p => r::p.map (rise r))))) =
    (List.range (n+1)).map (fun r => if (r==n)==b then patternCount n bs else 0) := by
    apply List.map_congr_left
    intro r hr
    exact insertion_count n r b bs (by have := List.mem_range.mp hr; omega)
  rw [h,List.range_succ,List.map_append,List.sum_append]
  have hrange : (List.range n).map (fun r => if (r==n)==b then patternCount n bs else 0) =
      (List.range n).map (fun _ => if b then 0 else patternCount n bs) := by
    apply List.map_congr_left
    intro r hr
    have hn : r ≠ n := by have := List.mem_range.mp hr; omega
    cases b <;> simp [hn]
  rw [hrange]
  cases b <;> simp [sum_constant]

theorem patternCount_exact (n : Nat) (flags : List Bool) (hlen : flags.length=n) :
    patternCount n flags = patternWeight flags := by
  induction flags generalizing n with
  | nil => have hn : n=0 := by simpa using hlen.symm
           subst n
           simp [patternCount,perms,recs,patternWeight]
  | cons b bs ih =>
    have hn : n=bs.length+1 := by simpa using hlen.symm
    subst n
    simp only [List.length_cons]
    rw [patternCount_step,ih bs.length rfl]
    rfl

def chronologicalPatternCount (n : Nat) (flags : List Bool) : Nat :=
  (chronologicalPerms n).countP (fun p => chronologicalRecords p == flags)

theorem chronologicalPatternCount_reverse (n : Nat) (flags : List Bool) :
    chronologicalPatternCount n flags = patternCount n flags.reverse := by
  unfold chronologicalPatternCount chronologicalPerms patternCount
  rw [List.countP_map]
  apply List.countP_congr
  intro p hp
  simp only [Function.comp_apply,chronologicalRecords_reverse,beq_iff_eq]
  exact ⟨fun h => by have := congrArg List.reverse h; simpa using this,
         fun h => by rw [h,List.reverse_reverse]⟩

theorem chronologicalPatternCount_exact (n : Nat) (flags : List Bool) (hlen : flags.length=n) :
    chronologicalPatternCount n flags = patternWeight flags.reverse := by
  rw [chronologicalPatternCount_reverse]
  exact patternCount_exact n flags.reverse (by simpa using hlen)

-- Factors are indexed by chronological position j=tail.length+1.
-- True has probability 1/j, false has probability 1-1/j.
def bernoulliProduct : List Bool → Rat
  | [] => 1
  | b::bs => (if b then (1:Rat)/((bs.length+1 : Nat):Rat) else (bs.length : Rat)/((bs.length+1 : Nat):Rat)) * bernoulliProduct bs

theorem factorial_positive (n : Nat) : 0 < factorial n := by
  induction n with
  | zero => decide
  | succ n ih => simp only [factorial]; exact Nat.mul_pos (by omega) ih

theorem weight_probability (flags : List Bool) :
    (patternWeight flags : Rat)/(factorial flags.length : Rat) = bernoulliProduct flags := by
  induction flags with
  | nil => change (1:Rat)/1=1; grind
  | cons b bs ih =>
    have hf : (factorial bs.length : Rat) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (factorial_positive bs.length))
    have hn : ((bs.length+1 : Nat) : Rat) ≠ 0 := by grind
    simp only [patternWeight,List.length_cons,factorial,bernoulliProduct]
    cases b <;> grind

def uniformPatternProbability (n : Nat) (flags : List Bool) : Rat :=
  (chronologicalPatternCount n flags : Rat)/(chronologicalPerms n).length

theorem independent_bernoulli_joint_law (n : Nat) (flags : List Bool) (hlen : flags.length=n) :
    uniformPatternProbability n flags = bernoulliProduct flags.reverse := by
  unfold uniformPatternProbability
  rw [chronologicalPatternCount_exact n flags hlen,chronologicalPerms_length]
  have hl : flags.reverse.length=n := by simpa using hlen
  rw [← hl]
  exact weight_probability flags.reverse

theorem bernoulli_false_factor (n : Nat) :
    (n : Rat)/((n+1 : Nat):Rat) = 1-(1:Rat)/((n+1 : Nat):Rat) := by grind

end Records9361
