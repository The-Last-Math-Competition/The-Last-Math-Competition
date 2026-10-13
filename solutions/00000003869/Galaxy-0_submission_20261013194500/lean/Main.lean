import Std
namespace Pfaffian
abbrev Edge := Nat × Nat

def bit (p : Prop) [Decidable p] : Nat := if p then 1 else 0

def invPair (a b : Edge) : Nat :=
  bit (b.1 < a.1) + bit (b.2 < a.1) + bit (b.1 < a.2) + bit (b.2 < a.2)
def crossPair (a b : Edge) : Nat := bit (a.1 < b.1 ∧ b.1 < a.2 ∧ a.2 < b.2)
def nestPair (a b : Edge) : Nat := bit (a.1 < b.1 ∧ b.2 < a.2)

theorem pair_identity (a b : Edge) (ha : a.1 < a.2) (hb : b.1 < b.2)
    (hab : a.1 < b.1) (_hne : a.2 ≠ b.1) (hne' : a.2 ≠ b.2) :
    invPair a b = crossPair a b + 2 * nestPair a b := by
  unfold invPair crossPair nestPair bit
  split <;> split <;> split <;> split <;> split <;> split <;> omega

def canonical : List Edge → Prop
  | [] => True
  | a :: as => a.1 < a.2 ∧ (∀ b ∈ as, a.1 < b.1 ∧ a.2 ≠ b.1 ∧ a.2 ≠ b.2) ∧ canonical as

def pairSum (f : Edge → Edge → Nat) : List Edge → Nat
  | [] => 0
  | a :: as => (as.map (f a)).sum + pairSum f as

def endpoints : List Edge → List Nat
  | [] => []
  | a :: as => a.1 :: a.2 :: endpoints as

def inversions : List Nat → Nat
  | [] => 0
  | a :: as => (as.map (fun b => bit (b < a))).sum + inversions as

theorem map_sum_add (as : List Edge) (f g : Edge → Nat) :
    (as.map (fun a => f a + g a)).sum = (as.map f).sum + (as.map g).sum := by
  induction as with
  | nil => rfl
  | cons a as ih => simp only [List.map_cons, List.sum_cons, ih]; omega

theorem map_sum_double (as : List Edge) (f : Edge → Nat) :
    (as.map (fun a => 2 * f a)).sum = 2 * (as.map f).sum := by
  induction as with
  | nil => rfl
  | cons a as ih => simp only [List.map_cons, List.sum_cons, ih, Nat.mul_add]

theorem count_endpoints (as : List Edge) (x : Nat) :
    ((endpoints as).map (fun y => bit (y < x))).sum =
      (as.map (fun b => bit (b.1 < x) + bit (b.2 < x))).sum := by
  induction as with
  | nil => rfl
  | cons a as ih => simp only [endpoints, List.map_cons, List.sum_cons, ih]; omega

theorem inv_eq_pairSum (as : List Edge) (h : canonical as) :
    inversions (endpoints as) = pairSum invPair as := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    rcases h with ⟨ha, hab, hs⟩
    simp only [endpoints, inversions, List.map_cons, List.sum_cons]
    rw [ih hs, count_endpoints, count_endpoints]
    have hz : bit (a.2 < a.1) = 0 := by unfold bit; split <;> omega
    rw [hz]
    change _ = (as.map (invPair a)).sum + pairSum invPair as
    have hm := map_sum_add as (fun b => bit (b.1 < a.1) + bit (b.2 < a.1)) (fun b => bit (b.1 < a.2) + bit (b.2 < a.2))
    have hf : (fun b => bit (b.1 < a.1) + bit (b.2 < a.1) + (bit (b.1 < a.2) + bit (b.2 < a.2))) = invPair a := by
      funext b; unfold invPair; omega
    rw [hf] at hm
    omega

theorem canonical_mem (as : List Edge) (h : canonical as) (b : Edge) (hb : b ∈ as) : b.1 < b.2 := by
  induction as with
  | nil => simp at hb
  | cons a as ih =>
    rcases h with ⟨ha, _, hs⟩
    simp only [List.mem_cons] at hb
    rcases hb with rfl | hb
    · exact ha
    · exact ih hs hb

theorem inversion_crossing_identity (as : List Edge) (h : canonical as) :
    inversions (endpoints as) = pairSum crossPair as + 2 * pairSum nestPair as := by
  rw [inv_eq_pairSum as h]
  induction as with
  | nil => rfl
  | cons a as ih =>
    rcases h with ⟨ha, hab, hs⟩
    simp only [pairSum, ih hs]
    have hm : as.map (invPair a) = as.map (fun b => crossPair a b + 2 * nestPair a b) := by
      apply List.map_congr_left
      intro b hb
      exact pair_identity a b ha (canonical_mem as hs b hb) (hab b hb).1 (hab b hb).2.1 (hab b hb).2.2
    rw [hm, map_sum_add, map_sum_double]
    omega

def sign (n : Nat) : Int := if n % 2 = 0 then 1 else -1

theorem crossing_sign (as : List Edge) (h : canonical as) :
    sign (inversions (endpoints as)) = sign (pairSum crossPair as) := by
  rw [inversion_crossing_identity as h]
  unfold sign
  have he : (pairSum crossPair as + 2 * pairSum nestPair as) % 2 = pairSum crossPair as % 2 := by omega
  rw [he]

instance canonicalDecidable : (as : List Edge) → Decidable (canonical as)
  | [] => isTrue trivial
  | a :: as =>
    letI := canonicalDecidable as
    show Decidable (a.1 < a.2 ∧ (∀ b ∈ as, a.1 < b.1 ∧ a.2 ≠ b.1 ∧ a.2 ≠ b.2) ∧ canonical as) from inferInstance

def edgeUniverse (n : Nat) : List Edge :=
  (List.range (2*n)).flatMap fun a => (List.range (2*n)).map fun b => (a,b)
def words (alphabet : List Edge) : Nat → List (List Edge)
  | 0 => [[]]
  | n+1 => alphabet.flatMap fun a => (words alphabet n).map fun as => a :: as

def PerfectMatching (n : Nat) (as : List Edge) : Prop :=
  canonical as ∧ (endpoints as).Perm (List.range (2*n))
instance (n : Nat) (as : List Edge) : Decidable (PerfectMatching n as) := by
  unfold PerfectMatching
  infer_instance

def unique {α : Type} [DecidableEq α] : List α → List α
  | [] => []
  | a :: as => if a ∈ as then unique as else a :: unique as

theorem mem_unique {α : Type} [DecidableEq α] (as : List α) (x : α) :
    x ∈ unique as ↔ x ∈ as := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    simp only [unique]
    split
    · rename_i ha
      rw [ih, List.mem_cons]
      constructor
      · exact Or.inr
      · intro h; rcases h with rfl | h
        · exact ha
        · exact h
    · simp only [List.mem_cons, ih]

theorem unique_nodup {α : Type} [DecidableEq α] (as : List α) : (unique as).Nodup := by
  induction as with
  | nil => exact List.nodup_nil
  | cons a as ih =>
    simp only [unique]
    split
    · exact ih
    · rename_i ha
      apply List.nodup_cons.mpr
      exact ⟨fun h => ha ((mem_unique as a).mp h), ih⟩

def matchings (n : Nat) : List (List Edge) :=
  unique ((words (edgeUniverse n) n).filter fun as => decide (PerfectMatching n as))

theorem endpoints_length (as : List Edge) : (endpoints as).length = 2 * as.length := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [endpoints, ih, Nat.mul_add]

theorem mem_endpoints (as : List Edge) (a : Edge) (h : a ∈ as) :
    a.1 ∈ endpoints as ∧ a.2 ∈ endpoints as := by
  induction as with
  | nil => simp at h
  | cons b bs ih =>
    simp only [List.mem_cons] at h
    rcases h with rfl | h
    · simp [endpoints]
    · have hh := ih h; simp only [endpoints, List.mem_cons]; exact ⟨Or.inr (Or.inr hh.1), Or.inr (Or.inr hh.2)⟩

theorem mem_edgeUniverse (n : Nat) (a : Edge) :
    a ∈ edgeUniverse n ↔ a.1 < 2*n ∧ a.2 < 2*n := by
  rcases a with ⟨a,b⟩
  simp [edgeUniverse, List.mem_flatMap, List.mem_map, List.mem_range]

theorem mem_words (alphabet : List Edge) (n : Nat) (as : List Edge) :
    as ∈ words alphabet n ↔ as.length = n ∧ ∀ a ∈ as, a ∈ alphabet := by
  induction n generalizing as with
  | zero => simp [words]; intro h; subst as; simp
  | succ n ih =>
    cases as with
    | nil => simp [words]
    | cons a as =>
      simp [words, List.mem_flatMap, List.mem_map, ih, List.mem_cons]
      constructor
      · intro h; exact ⟨h.2.1, h.1, h.2.2⟩
      · intro h; exact ⟨h.2.1, h.1, h.2.2⟩

theorem mem_matchings (n : Nat) (as : List Edge) :
    as ∈ matchings n ↔ PerfectMatching n as := by
  simp only [matchings, mem_unique, List.mem_filter, decide_eq_true_eq]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨(mem_words _ _ _).mpr ⟨?_, ?_⟩, h⟩
    · have hl := h.2.length_eq
      rw [endpoints_length, List.length_range] at hl
      omega
    · intro a ha
      have hm := mem_endpoints as a ha
      exact (mem_edgeUniverse n a).mpr ⟨List.mem_range.mp (h.2.mem_iff.mp hm.1), List.mem_range.mp (h.2.mem_iff.mp hm.2)⟩

theorem matchings_nodup (n : Nat) : (matchings n).Nodup := unique_nodup _

theorem matching_endpoint_permutation (n : Nat) (as : List Edge) (h : as ∈ matchings n) :
    (endpoints as).Perm (List.range (2*n)) := ((mem_matchings n as).mp h).2

theorem matching_endpoints_distinct (n : Nat) (as : List Edge) (h : as ∈ matchings n) :
    (endpoints as).Nodup :=
  (matching_endpoint_permutation n as h).nodup_iff.mpr List.nodup_range

-- The formal signed monomial includes its edge list, so equality is before
-- specialization of kernel entries and remains valid over any coefficient type.
def permutationMonomial (as : List Edge) : Int × List Edge :=
  (sign (inversions (endpoints as)), as)
def crossingMonomial (as : List Edge) : Int × List Edge :=
  (sign (pairSum crossPair as), as)

theorem formal_pfaffian_expansion (n : Nat) :
    (matchings n).map permutationMonomial = (matchings n).map crossingMonomial := by
  apply List.map_congr_left
  intro as h
  unfold permutationMonomial crossingMonomial
  rw [crossing_sign as ((mem_matchings n as).mp h).1]

theorem evaluated_pfaffian_expansion {α : Type} [Add α] [Zero α]
    (n : Nat) (evaluate : Int × List Edge → α) :
    (((matchings n).map permutationMonomial).map evaluate).sum =
      (((matchings n).map crossingMonomial).map evaluate).sum := by
  rw [formal_pfaffian_expansion]

-- Entries may be arbitrary integers: the combinatorial identity does not
-- require skew-symmetry, an integration domain, or convergence assumptions.
def edgeProduct (K : Nat → Nat → Int) (as : List Edge) : Int :=
  (as.map (fun a => K a.1 a.2)).prod

def permutationTerm (K : Nat → Nat → Int) (as : List Edge) : Int :=
  sign (inversions (endpoints as)) * edgeProduct K as

def crossingTerm (K : Nat → Nat → Int) (as : List Edge) : Int :=
  sign (pairSum crossPair as) * edgeProduct K as

def pfaffian (n : Nat) (K : Nat → Nat → Int) : Int :=
  ((matchings n).map (permutationTerm K)).sum

theorem term_sign_formula (n : Nat) (K : Nat → Nat → Int) (as : List Edge)
    (h : PerfectMatching n as) : permutationTerm K as = crossingTerm K as := by
  unfold permutationTerm crossingTerm
  rw [crossing_sign as h.1]

theorem pfaffian_crossing_expansion (n : Nat) (K : Nat → Nat → Int) :
    pfaffian n K = ((matchings n).map (crossingTerm K)).sum := by
  unfold pfaffian
  congr 1
  apply List.map_congr_left
  intro as h
  exact term_sign_formula n K as ((mem_matchings n as).mp h)

-- One crossing test for each pair of edges; no search over matchings is
-- involved in calculating the sign of an individual expansion term.
def crossingTests : List Edge → Nat
  | [] => 0
  | _ :: as => as.length + crossingTests as

theorem crossingTests_exact (as : List Edge) :
    2 * crossingTests as + as.length = as.length * as.length := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    simp only [crossingTests, List.length_cons, Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul]
    omega

theorem crossingTests_quadratic (n : Nat) (as : List Edge) (h : PerfectMatching n as) :
    crossingTests as ≤ n * n := by
  have hl := h.2.length_eq
  rw [endpoints_length, List.length_range] at hl
  have he : as.length = n := by omega
  have hc := crossingTests_exact as
  rw [he] at hc
  omega

def countAgainst (a : Edge) : List Edge → Nat × Nat
  | [] => (0,0)
  | b :: bs => let r := countAgainst a bs; (crossPair a b + r.1, 1 + r.2)

def crossingCountWithCost : List Edge → Nat × Nat
  | [] => (0,0)
  | a :: as =>
    let r := countAgainst a as
    let s := crossingCountWithCost as
    (r.1 + s.1, r.2 + s.2)

theorem countAgainst_correct (a : Edge) (as : List Edge) :
    countAgainst a as = ((as.map (crossPair a)).sum, as.length) := by
  induction as with
  | nil => rfl
  | cons b bs ih => simp [countAgainst, ih, Nat.add_comm]

theorem crossingCountWithCost_correct (as : List Edge) :
    crossingCountWithCost as = (pairSum crossPair as, crossingTests as) := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [crossingCountWithCost, countAgainst_correct, ih, pairSum, crossingTests]

theorem sign_eq_neg_one_pow (n : Nat) : sign n = (-1 : Int)^n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Int.pow_succ, ← ih]
    unfold sign
    split <;> split <;> simp_all <;> omega

#print axioms crossingCountWithCost_correct
#print axioms formal_pfaffian_expansion
#print axioms evaluated_pfaffian_expansion
#print axioms matchings_nodup
#print axioms sign_eq_neg_one_pow
#print axioms inversion_crossing_identity
#print axioms mem_matchings
#print axioms pfaffian_crossing_expansion
#print axioms crossingTests_quadratic
end Pfaffian
