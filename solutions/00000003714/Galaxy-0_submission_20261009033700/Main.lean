import Std
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace TLMC3714

abbrev Graph (n : Nat) := Fin (2 ^ (n * (n - 1) / 2))
def adj (g : Graph n) (i j : Fin n) : Bool :=
  if i.val < j.val then g.val.testBit (j.val * (j.val - 1) / 2 + i.val)
  else if j.val < i.val then g.val.testBit (i.val * (i.val - 1) / 2 + j.val)
  else false

-- Coefficients are stored in increasing degree order. These are the
-- ordinary recursive sum and convolution product in Z[X].
def pAdd : List Int → List Int → List Int
  | [], q => q
  | p, [] => p
  | a::p, b::q => (a+b)::pAdd p q

def pMul : List Int → List Int → List Int
  | [], _ => []
  | a::p, q => pAdd (q.map (a * ·)) (0 :: pMul p q)

def permutations : List Nat → List (List Nat)
  | [] => [[]]
  | a::xs => (permutations xs).flatMap (fun p =>
      (List.range (p.length+1)).map (fun k => p.take k ++ [a] ++ p.drop k))

def inversions (p : List Nat) : Nat :=
  ((List.range p.length).flatMap (fun i =>
    (List.range p.length).filter (fun j => i < j && p[i]! > p[j]!))).length

def charPoly (g : Graph n) : List Int :=
  ((permutations (List.range n)).map (fun p =>
    let term := ((List.finRange n).map (fun i =>
      let j := (⟨p[i.val]! % n, Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩ : Fin n)
      [if adj g i j then -1 else 0, if i == j then 1 else 0])).foldl pMul [1]
    term.map ((if inversions p % 2 == 0 then 1 else -1) * ·))).foldl pAdd []

theorem permutation_enumeration_checked : ∀ n : Fin 6,
    let ps := permutations (List.range n.val)
    ps.Nodup ∧ ps.length = [1,1,2,6,24,120][n.val]! ∧
    ∀ p ∈ ps, p.Nodup ∧ p.length = n.val ∧ ∀ x ∈ p, x < n.val := by decide

def IsIso (g h : Graph n) (f : Fin n → Fin n) : Prop :=
  (∀ i j, f i = f j → i = j) ∧
  (∀ j, ∃ i, f i = j) ∧
  ∀ i j, adj g i j = adj h (f i) (f j)
instance (g h : Graph n) (f : Fin n → Fin n) : Decidable (IsIso g h f) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def Isomorphic (g h : Graph n) : Prop := ∃ f, IsIso g h f

def permMap (n : Nat) (p : List Nat) (i : Fin n) : Fin n :=
  (⟨p[i.val]! % n, Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩ : Fin n)

def isoCandidate (g h : Graph n) : Fin n → Fin n :=
  permMap n (((permutations (List.range n)).find?
    (fun p => decide (IsIso g h (permMap n p)))).getD [])

-- Every isomorphism claimed in this table is checked as a genuine
-- bijection preserving all adjacency entries, not just a matching invariant.
theorem small0 : ∀ g h : Graph 0, charPoly g = charPoly h → IsIso g h (isoCandidate g h) := by decide
theorem small1 : ∀ g h : Graph 1, charPoly g = charPoly h → IsIso g h (isoCandidate g h) := by decide
theorem small2 : ∀ g h : Graph 2, charPoly g = charPoly h → IsIso g h (isoCandidate g h) := by decide
theorem small3 : ∀ g h : Graph 3, charPoly g = charPoly h → IsIso g h (isoCandidate g h) := by decide
theorem small4 : ∀ g h : Graph 4, charPoly g = charPoly h → IsIso g h (isoCandidate g h) := by decide

theorem no_smaller_pair (n : Nat) (hn : n < 5) (g h : Graph n)
    (heq : charPoly g = charPoly h) : Isomorphic g h := by
  have : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, small0 g h heq⟩
  · exact ⟨_, small1 g h heq⟩
  · exact ⟨_, small2 g h heq⟩
  · exact ⟨_, small3 g h heq⟩
  · exact ⟨_, small4 g h heq⟩

-- Edge positions 0,1,3,6 are the four edges incident to vertex 0.
def star : Graph 5 := 75
-- 0-1-2-3-0 is a four-cycle; vertex 4 is isolated.
def cycleIsolate : Graph 5 := 45

theorem explicit_polynomials :
    charPoly star = [0,0,0,-4,0,1] ∧
    charPoly cycleIsolate = [0,0,0,-4,0,1] := by decide

theorem star_is_K14 : ∀ i j : Fin 5,
    adj star i j = decide (i ≠ j ∧ (i = 0 ∨ j = 0)) := by decide

theorem cycle_is_C4_plus_K1 : ∀ i j : Fin 5,
    adj cycleIsolate i j = decide (
      (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨
      (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) ∨
      (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) ∨
      (i = 3 ∧ j = 0) ∨ (i = 0 ∧ j = 3)) := by decide

theorem explicit_factorization :
    pMul [0,0,0,1] (pMul [-2,1] [2,1]) = [0,0,0,-4,0,1] := by decide

theorem star_has_neighbor : ∀ i : Fin 5, ∃ j : Fin 5, adj star i j = true := by decide
theorem cycle_has_isolate : ∀ j : Fin 5, adj cycleIsolate 4 j = false := by decide

theorem not_isomorphic : ¬ Isomorphic star cycleIsolate := by
  rintro ⟨f, _, hsurj, hpres⟩
  obtain ⟨i, hi⟩ := hsurj 4
  obtain ⟨j, hj⟩ := star_has_neighbor i
  have he := hpres i j
  rw [hj, hi, cycle_has_isolate] at he
  cases he

theorem conjecture3714 :
    (charPoly star = charPoly cycleIsolate ∧ ¬ Isomorphic star cycleIsolate) ∧
    (∀ n, n < 5 → ∀ g h : Graph n, charPoly g = charPoly h → Isomorphic g h) :=
  ⟨⟨explicit_polynomials.1.trans explicit_polynomials.2.symm, not_isomorphic⟩,
    no_smaller_pair⟩
#print axioms conjecture3714
end TLMC3714
