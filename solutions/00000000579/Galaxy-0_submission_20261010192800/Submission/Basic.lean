import Std
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace TLMC579
abbrev Mask := Fin 16
abbrev Edge := Fin 4
def has (s : Mask) (e : Edge) : Bool := s.val / 2^e.val % 2 == 1
def sub (s t : Mask) : Bool := (List.finRange 4).all fun e => !has s e || has t e
def card (s : Mask) : Nat := ((List.finRange 4).filter (has s)).length
def rank (s : Mask) : Nat := min 3 (card s)
def dualRank (s : Mask) : Nat := card s + rank ⟨15-s.val, by omega⟩ - rank 15
abbrev Rank := Mask → Nat
def flat (r : Rank) (a b : Mask) : Bool := sub a b && (List.finRange 16).all (fun s => ! (sub a s && sub s b && (card s == card a + 1)) || r a < r s)
def chi (r : Rank) (a b : Mask) (i : Nat) : Int := ((List.finRange 16).map fun s => if sub a s && sub s b && (r b-r s == i) then (-1 : Int)^(card s-card a) else 0).sum
abbrev Family := Mask → Mask → Nat → Int
def coeff (r : Rank) (p : Family) (a b : Mask) (i : Nat) : Int := if i == 0 then p a b 0 else if i == 1 && (r b-r a == 3) then p a b 1 else 0
def rhs (r : Rank) (p : Family) (a b : Mask) (i : Nat) : Int := ((List.finRange 16).map fun f => if sub a f && flat r f b then ((List.range (i+1)).map fun j => chi r a f j * coeff r p f b (i-j)).sum else 0).sum
structure IsKL (r : Rank) (p : Family) : Prop where
 zero : ∀ a b, sub a b = true → r b-r a = 0 → p a b 0 = 1
 recurrence : ∀ a b, flat r a b = true → ∀ i, (if i ≤ r b-r a then coeff r p a b (r b-r a-i) else 0) = rhs r p a b i

theorem top (p : Family) : rhs rank p 0 15 3 = p 15 15 0 := by
  simp +decide [rhs, chi, coeff, flat, sub, has, card, rank, List.finRange, List.range_succ, List.sum_cons, List.sum_nil]

def adjacent (s : Mask) (v w : Edge) : Bool := (List.finRange 4).any fun e => has s e && ((v.val == e.val && w.val == (e.val+1)%4) || (w.val == e.val && v.val == (e.val+1)%4))
def reachable (s : Mask) : Nat → Edge → Edge → Bool
 | 0, v, w => v == w
 | k+1, v, w => reachable s k v w || (List.finRange 4).any (fun u => reachable s k v u && adjacent s u w)
def components (s : Mask) : Nat := ((List.finRange 4).filter fun v => (List.finRange 4).all (fun w => !(w.val < v.val) || !reachable s 4 v w)).length
def graphicRank (s : Mask) : Nat := 4 - components s

theorem graphic_rank_certificate : ∀ s, graphicRank s = rank s := by decide

theorem dual_rank_certificate : ∀ s, dualRank s = min 1 (card s) := by decide

theorem c0_full (p : Family) (h : IsKL rank p) : p 15 15 0 = 1 := h.zero 15 15 (by decide) (by decide)
theorem c0_origin (p : Family) (h : IsKL rank p) : p 0 15 0 = 1 := by
 have z := h.recurrence 0 15 (by decide) 3
 change p 0 15 0 = rhs rank p 0 15 3 at z
 rw [top, c0_full p h] at z
 exact z

theorem top_3 (p : Family) : rhs rank p 3 15 1 = p 15 15 0 := by
  simp +decide [rhs, chi, coeff, flat, sub, has, card, rank, List.finRange, List.range_succ, List.sum_cons, List.sum_nil]
theorem c0_3 (p : Family) (h : IsKL rank p) : p 3 15 0 = 1 := by
 have z := h.recurrence 3 15 (by decide) 1
 change p 3 15 0 = rhs rank p 3 15 1 at z
 rw [top_3, c0_full p h] at z
 exact z

theorem top_5 (p : Family) : rhs rank p 5 15 1 = p 15 15 0 := by
  simp +decide [rhs, chi, coeff, flat, sub, has, card, rank, List.finRange, List.range_succ, List.sum_cons, List.sum_nil]
theorem c0_5 (p : Family) (h : IsKL rank p) : p 5 15 0 = 1 := by
 have z := h.recurrence 5 15 (by decide) 1
 change p 5 15 0 = rhs rank p 5 15 1 at z
 rw [top_5, c0_full p h] at z
 exact z

theorem top_6 (p : Family) : rhs rank p 6 15 1 = p 15 15 0 := by
  simp +decide [rhs, chi, coeff, flat, sub, has, card, rank, List.finRange, List.range_succ, List.sum_cons, List.sum_nil]
theorem c0_6 (p : Family) (h : IsKL rank p) : p 6 15 0 = 1 := by
 have z := h.recurrence 6 15 (by decide) 1
 change p 6 15 0 = rhs rank p 6 15 1 at z
 rw [top_6, c0_full p h] at z
 exact z

theorem top_9 (p : Family) : rhs rank p 9 15 1 = p 15 15 0 := by
  simp +decide [rhs, chi, coeff, flat, sub, has, card, rank, List.finRange, List.range_succ, List.sum_cons, List.sum_nil]
theorem c0_9 (p : Family) (h : IsKL rank p) : p 9 15 0 = 1 := by
 have z := h.recurrence 9 15 (by decide) 1
 change p 9 15 0 = rhs rank p 9 15 1 at z
 rw [top_9, c0_full p h] at z
 exact z

theorem top_10 (p : Family) : rhs rank p 10 15 1 = p 15 15 0 := by
  simp +decide [rhs, chi, coeff, flat, sub, has, card, rank, List.finRange, List.range_succ, List.sum_cons, List.sum_nil]
theorem c0_10 (p : Family) (h : IsKL rank p) : p 10 15 0 = 1 := by
 have z := h.recurrence 10 15 (by decide) 1
 change p 10 15 0 = rhs rank p 10 15 1 at z
 rw [top_10, c0_full p h] at z
 exact z

theorem top_12 (p : Family) : rhs rank p 12 15 1 = p 15 15 0 := by
  simp +decide [rhs, chi, coeff, flat, sub, has, card, rank, List.finRange, List.range_succ, List.sum_cons, List.sum_nil]
theorem c0_12 (p : Family) (h : IsKL rank p) : p 12 15 0 = 1 := by
 have z := h.recurrence 12 15 (by decide) 1
 change p 12 15 0 = rhs rank p 12 15 1 at z
 rw [top_12, c0_full p h] at z
 exact z

theorem next (p : Family) : rhs rank p 0 15 2 = p 3 15 0 + p 5 15 0 + p 6 15 0 + p 9 15 0 + p 10 15 0 + p 12 15 0 - 4*p 15 15 0 := by
 simp +decide [rhs, chi, coeff, flat, sub, has, card, rank, List.finRange, List.range_succ, List.sum_cons, List.sum_nil]
 omega

theorem c1_origin (p : Family) (h : IsKL rank p) : p 0 15 1 = 2 := by
 have z := h.recurrence 0 15 (by decide) 2
 change p 0 15 1 = rhs rank p 0 15 2 at z
 rw [next, c0_3 p h, c0_5 p h, c0_6 p h, c0_9 p h, c0_10 p h, c0_12 p h, c0_full p h] at z
 exact z

theorem dual_top (p : Family) : rhs dualRank p 0 15 1 = p 15 15 0 := by
 simp +decide [rhs, chi, coeff, flat, sub, has, card, dualRank, rank, List.finRange, List.range_succ, List.sum_cons, List.sum_nil]

theorem dual_c0 (p : Family) (h : IsKL dualRank p) : p 0 15 0 = 1 := by
 have z := h.recurrence 0 15 (by decide) 1
 change p 0 15 0 = rhs dualRank p 0 15 1 at z
 rw [dual_top, h.zero 15 15 (by decide) (by decide)] at z
 exact z

def RankMonotone (r : Rank) : Prop := ∀ a b, sub a b = true → r a ≤ r b

theorem rank_mono : RankMonotone rank := by unfold RankMonotone; decide
theorem dual_mono : RankMonotone dualRank := by unfold RankMonotone; decide
theorem rank_bound : ∀ s, rank s ≤ 3 := by decide
theorem dual_bound : ∀ s, dualRank s ≤ 3 := by decide

theorem sum_zero (l : List α) (f : α → Int) (h : ∀ x, x ∈ l → f x = 0) : (l.map f).sum = 0 := by
 induction l with
 | nil => rfl
 | cons a l ih =>
   simp only [List.map_cons, List.sum_cons]
   rw [h a (by simp), ih (fun x hx => h x (by simp [hx]))]
   rfl

theorem chi_degree (r : Rank) (hm : RankMonotone r) (a b : Mask) (j : Nat) (hj : r b-r a < j) : chi r a b j = 0 := by
 apply sum_zero
 intro s hs
 split
 next h =>
  have hab : sub a s = true := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).1
  have he : r b-r s = j := by simpa using (Bool.and_eq_true_iff.mp h).2
  have hm' := hm a s hab
  omega
 next => rfl

theorem rhs_tail (r : Rank) (hm : RankMonotone r) (hb : ∀ s, r s ≤ 3) (p : Family) (a b : Mask) (i : Nat) (hi : 4 ≤ i) : rhs r p a b i = 0 := by
 apply sum_zero
 intro f hf
 split
 next h =>
  apply sum_zero
  intro j hj
  by_cases hc : r f-r a < j
  · rw [chi_degree r hm a f j hc]; simp
  · have haf : r a ≤ r f := hm a f (Bool.and_eq_true_iff.mp h).1
    have hfb : r f ≤ r b := hm f b (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).2).1
    have hb' := hb b
    have hn : i-j ≠ 0 := by omega
    have hn' : ¬ (i-j = 1 ∧ r b-r f = 3) := by omega
    have hz : coeff r p f b (i-j) = 0 := by simp [coeff, hn, hn']
    rw [hz]; simp
 next => rfl

def proposed (a b : Mask) (i : Nat) : Int := if i=0 then 1 else if i=1 && rank b-rank a == 3 && b == 15 then 2 else 0
def dualProposed (_a _b : Mask) (i : Nat) : Int := if i=0 then 1 else 0

theorem proposed_small : ∀ a b, flat rank a b = true → ∀ i : Fin 4,
 (if i.val ≤ rank b-rank a then coeff rank proposed a b (rank b-rank a-i.val) else 0) = rhs rank proposed a b i.val := by decide

theorem dual_proposed_small : ∀ a b, flat dualRank a b = true → ∀ i : Fin 4,
 (if i.val ≤ dualRank b-dualRank a then coeff dualRank dualProposed a b (dualRank b-dualRank a-i.val) else 0) = rhs dualRank dualProposed a b i.val := by decide

theorem proposed_isKL : IsKL rank proposed where
 zero := by intro a b h hr; simp [proposed]
 recurrence := by
  intro a b hf i
  by_cases hi : i < 4
  · exact proposed_small a b hf ⟨i,hi⟩
  · have htail := rhs_tail rank rank_mono rank_bound proposed a b i (by omega)
    have hb := rank_bound b
    rw [htail]; simp [show ¬ i ≤ rank b-rank a by omega]

theorem dual_proposed_isKL : IsKL dualRank dualProposed where
 zero := by intro a b h hr; simp [dualProposed]
 recurrence := by
  intro a b hf i
  by_cases hi : i < 4
  · exact dual_proposed_small a b hf ⟨i,hi⟩
  · have htail := rhs_tail dualRank dual_mono dual_bound dualProposed a b i (by omega)
    have hb := dual_bound b
    rw [htail]; simp [show ¬ i ≤ dualRank b-dualRank a by omega]

/-- Inclusion-exclusion coefficient formula for the chromatic polynomial of C4. -/
def chromaticCoeff (i : Nat) : Int := ((List.finRange 16).map fun s => if components s == i then (-1 : Int)^card s else 0).sum
/-- P(-1), computed directly from the chromatic subset expansion. -/
def chromaticMinusOne : Int := ((List.finRange 16).map fun s => (-1 : Int)^card s * (-1 : Int)^components s).sum

theorem chromatic_coefficients : (List.range 5).map chromaticCoeff = [0,-3,6,-4,1] := by decide
theorem chromatic_value : chromaticMinusOne = 14 := by decide
theorem characteristic_coefficients : (List.range 4).map (chi rank 0 15) = [-3,6,-4,1] := by decide

def atOne (r : Rank) (p : Family) : Int := coeff r p 0 15 0 + coeff r p 0 15 1

theorem graphic_KL_atOne (p : Family) (h : IsKL rank p) : atOne rank p = 3 := by
 change p 0 15 0 + p 0 15 1 = 3
 rw [c0_origin p h, c1_origin p h]
 decide

theorem dual_KL_atOne (p : Family) (h : IsKL dualRank p) : atOne dualRank p = 1 := by
 change p 0 15 0 + 0 = 1
 rw [dual_c0 p h]
 decide

theorem conjecture_00000000579_false (p q : Family) (hp : IsKL rank p) (hq : IsKL dualRank q) :
 ¬ ∃ z : Int, atOne rank p - atOne dualRank q = chromaticMinusOne * z := by
 rw [graphic_KL_atOne p hp, dual_KL_atOne q hq, chromatic_value]
 omega

theorem counterexample_exists : ∃ p q : Family, IsKL rank p ∧ IsKL dualRank q ∧
 ¬ ∃ z : Int, atOne rank p - atOne dualRank q = chromaticMinusOne * z :=
 ⟨proposed, dualProposed, proposed_isKL, dual_proposed_isKL,
 conjecture_00000000579_false proposed dualProposed proposed_isKL dual_proposed_isKL⟩

#print axioms conjecture_00000000579_false
#print axioms counterexample_exists
#print axioms graphic_rank_certificate

/-- Four rounds already give the entire connectivity relation on four vertices. -/
theorem reach_stabilizes : ∀ s v w, reachable s 5 v w = reachable s 4 v w := by decide

theorem reach_later (s : Mask) (k : Nat) : ∀ v w, reachable s (4+k) v w = reachable s 4 v w := by
 induction k with
 | zero => intro v w; rfl
 | succ k ih =>
   intro v w
   change (reachable s (4+k) v w || (List.finRange 4).any (fun u => reachable s (4+k) v u && adjacent s u w)) = reachable s 4 v w
   simp only [ih]
   exact reach_stabilizes s v w

theorem reach_earlier : ∀ s (k : Fin 5) v w, reachable s k.val v w = true → reachable s 4 v w = true := by decide

def Connected (s : Mask) (v w : Edge) : Prop := ∃ k, reachable s k v w = true

theorem connectivity_exact (s : Mask) (v w : Edge) : Connected s v w ↔ reachable s 4 v w = true := by
 constructor
 · intro ⟨k,h⟩
   by_cases hk : k < 5
   · exact reach_earlier s ⟨k,hk⟩ v w h
   · have he : k = 4+(k-4) := by omega
     rw [he, reach_later] at h
     exact h
 · intro h; exact ⟨4,h⟩

def unionMask (a b : Mask) : Mask := ⟨(a.val ||| b.val)%16, Nat.mod_lt _ (by decide)⟩
def interMask (a b : Mask) : Mask := ⟨(a.val &&& b.val)%16, Nat.mod_lt _ (by decide)⟩

theorem rank_axioms : rank 0 = 0 ∧ (∀ s, rank s ≤ card s) ∧ RankMonotone rank ∧
 (∀ a b, rank (unionMask a b) + rank (interMask a b) ≤ rank a + rank b) := by
 refine ⟨by decide, by decide, rank_mono, ?_⟩
 decide

theorem dual_rank_axioms : dualRank 0 = 0 ∧ (∀ s, dualRank s ≤ card s) ∧ RankMonotone dualRank ∧
 (∀ a b, dualRank (unionMask a b) + dualRank (interMask a b) ≤ dualRank a + dualRank b) := by
 refine ⟨by decide, by decide, dual_mono, ?_⟩
 decide

#print axioms connectivity_exact

def graphicDualRank (s : Mask) : Nat := card s + graphicRank ⟨15-s.val, by omega⟩ - graphicRank 15

theorem graphic_rank_eq : graphicRank = rank := funext graphic_rank_certificate

theorem graphic_dual_eq : graphicDualRank = dualRank := by
 funext s
 simp only [graphicDualRank, dualRank, graphic_rank_eq]

theorem graphic_counterexample (p q : Family) (hp : IsKL graphicRank p) (hq : IsKL graphicDualRank q) :
 ¬ ∃ z : Int, atOne graphicRank p - atOne graphicDualRank q = chromaticMinusOne * z := by
 rw [graphic_rank_eq] at hp ⊢
 rw [graphic_dual_eq] at hq ⊢
 exact conjecture_00000000579_false p q hp hq

#print axioms graphic_counterexample
end TLMC579
