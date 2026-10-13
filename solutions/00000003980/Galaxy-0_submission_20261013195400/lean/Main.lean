import Std

namespace TLMC3980

inductive Formula where
  | atom : Nat → Formula
  | bottom : Formula
  | imp : Formula → Formula → Formula
  deriving DecidableEq, Repr

def Formula.vars : Formula → Nat
  | .atom k => k + 1
  | .bottom => 0
  | .imp a b => max a.vars b.vars

-- Unary variable indices give a transparent, finite syntax encoding.
def Formula.size : Formula → Nat
  | .atom k => k + 2
  | .bottom => 1
  | .imp a b => 1 + a.size + b.size

def Formula.eval (v : List Bool) : Formula → Bool
  | .atom k => v[k]?.getD false
  | .bottom => false
  | .imp a b => !(a.eval v) || b.eval v

def Tautology (f : Formula) : Prop :=
  ∀ v : List Bool, v.length = f.vars → f.eval v = true

def assignments : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (assignments n).flatMap (fun v => [false :: v, true :: v])

theorem mem_assignments (n : Nat) (v : List Bool) :
    v ∈ assignments n ↔ v.length = n := by
  induction n generalizing v with
  | zero => simp [assignments, List.length_eq_zero_iff]
  | succ n ih =>
    cases v with
    | nil => simp [assignments]
    | cons b v =>
      cases b <;> simp [assignments, List.mem_flatMap, ih]

theorem sum_map_two (xs : List α) : (xs.map (fun _ => 2)).sum = 2 * xs.length := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [ih, Nat.mul_add, Nat.add_comm]

theorem assignments_length (n : Nat) : (assignments n).length = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [assignments, List.length_flatMap, sum_map_two, ih, Nat.pow_succ,
      Nat.mul_comm]

structure Certificate where
  formula : Formula
  table : List (List Bool)
  deriving DecidableEq, Repr

-- Check the size guard before constructing the exhaustive assignment table.
def check (p : Certificate) : Bool :=
  if p.table.length == 2 ^ p.formula.vars then
    (p.table == assignments p.formula.vars) &&
      p.table.all (fun v => p.formula.eval v)
  else false

def certificate (f : Formula) : Certificate := ⟨f, assignments f.vars⟩

theorem check_sound (p : Certificate) (h : check p = true) : Tautology p.formula := by
  simp only [check] at h
  split at h
  next =>
    have hs : (p.table == assignments p.formula.vars) = true ∧
        p.table.all (fun v => p.formula.eval v) = true := by simpa using h
    have ht : p.table = assignments p.formula.vars := by simpa using hs.1
    intro v hv
    exact List.all_eq_true.mp hs.2 v (ht ▸ (mem_assignments _ _).mpr hv)
  next => contradiction

theorem check_complete (f : Formula) (h : Tautology f) : check (certificate f) = true := by
  simp only [check, certificate, assignments_length, beq_self_eq_true, ↓reduceIte,
    Bool.true_and]
  exact List.all_eq_true.mpr (fun v hv => h v ((mem_assignments _ _).mp hv))

structure Proof where
  tag : Bool
  cert : Certificate
  deriving DecidableEq, Repr

-- Size counts the tag, syntax, row delimiters, and all valuation bits.
def proofLength (p : Proof) : Nat :=
  2 + p.cert.formula.size +
    (p.cert.table.map (fun row => row.length + 1)).sum

-- An eleven-symbol prefix alphabet, realizable by four-bit tokens.
def Formula.encode : Formula → List Nat
  | .atom k => 0 :: (List.replicate k 3 ++ [4])
  | .bottom => [1]
  | .imp a b => 2 :: (a.encode ++ b.encode)

def encodeProof (p : Proof) : List Nat :=
  [if p.tag then 6 else 5] ++ p.cert.formula.encode ++
  p.cert.table.flatMap (fun row => 7 :: row.map (fun b => if b then 9 else 8)) ++ [10]

theorem Formula.encode_length (f : Formula) : f.encode.length = f.size := by
  induction f with
  | atom k => simp [encode, size]
  | bottom => rfl
  | imp a b ha hb => simp [encode, size, ha, hb]; omega

theorem encodeProof_length (p : Proof) : (encodeProof p).length = proofLength p := by
  simp [encodeProof, proofLength, Formula.encode_length, List.length_flatMap]
  omega

def truth : Formula := .imp .bottom .bottom

theorem truth_tautology : Tautology truth := by
  intro v _
  rfl

-- Total decoding: malformed or wrong-tag certificates output a fixed tautology.
def decode (tag : Bool) (p : Proof) : Formula :=
  if p.tag == tag && check p.cert then p.cert.formula else truth

structure ProofSystem where
  verifies : Proof → Formula → Prop
  sound : ∀ p f, verifies p f → Tautology f
  complete : ∀ f, Tautology f → ∃ p, verifies p f

def taggedSystem (tag : Bool) : ProofSystem where
  verifies p f := decode tag p = f
  sound := by
    intro p f h
    change decode tag p = f at h
    subst f
    unfold decode
    split
    next ht =>
      have hc : check p.cert = true := by simpa using (Bool.and_eq_true_iff.mp ht).2
      exact check_sound p.cert hc
    next => exact truth_tautology
  complete := by
    intro f hf
    refine ⟨⟨tag, certificate f⟩, ?_⟩
    simp only [decode, beq_self_eq_true, check_complete f hf, Bool.true_and, ↓reduceIte]
    rfl

-- Retag each proof according to whether its old tag was accepted.
def translate (a b : Bool) (p : Proof) : Proof :=
  ⟨if p.tag == a then b else !b, p.cert⟩

theorem translate_decode (a b : Bool) (p : Proof) :
    decode b (translate a b p) = decode a p := by
  cases p with
  | mk t c => cases a <;> cases b <;> cases t <;> simp [translate, decode]

theorem translate_verifies (a b : Bool) (p : Proof) (f : Formula)
    (h : (taggedSystem a).verifies p f) :
    (taggedSystem b).verifies (translate a b p) f := by
  change decode b (translate a b p) = f
  rw [translate_decode]
  exact h

theorem translate_length (a b : Bool) (p : Proof) :
    proofLength (translate a b p) = proofLength p := rfl

-- Minimum is over all finite proofs, without a search bound.
def Shortest (P : ProofSystem) (f : Formula) (n : Nat) : Prop :=
  (∃ p, P.verifies p f ∧ proofLength p = n) ∧
  ∀ p, P.verifies p f → n ≤ proofLength p

theorem shortest_exists (P : ProofSystem) (f : Formula) (h : Tautology f) :
    ∃ n, Shortest P f n := by
  obtain ⟨p, hp⟩ := P.complete f h
  have aux : ∀ k, (∃ p, P.verifies p f ∧ proofLength p = k) → ∃ n, Shortest P f n := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro hk
      classical
      by_cases hs : ∃ j, j < k ∧ ∃ p, P.verifies p f ∧ proofLength p = j
      · obtain ⟨j, hj, hw⟩ := hs
        exact ih j hj hw
      · refine ⟨k, hk, ?_⟩
        intro q hq
        by_cases hn : k ≤ proofLength q
        · exact hn
        · exact False.elim (hs ⟨proofLength q, by omega, q, hq, rfl⟩)
  exact aux (proofLength p) ⟨p, hp, rfl⟩

theorem shortest_unique (P : ProofSystem) (f : Formula) (m n : Nat)
    (hm : Shortest P f m) (hn : Shortest P f n) : m = n := by
  obtain ⟨p, hp, lp⟩ := hm.1
  obtain ⟨q, hq, lq⟩ := hn.1
  have := hm.2 q hq
  have := hn.2 p hp
  omega

theorem tagged_shortest_equal (a b : Bool) (f : Formula) (m n : Nat)
    (hm : Shortest (taggedSystem a) f m)
    (hn : Shortest (taggedSystem b) f n) : m = n := by
  obtain ⟨p, hp, lp⟩ := hm.1
  obtain ⟨q, hq, lq⟩ := hn.1
  have hmn := hm.2 (translate b a q) (translate_verifies b a q f hq)
  have hnm := hn.2 (translate a b p) (translate_verifies a b p f hp)
  rw [translate_length, lq] at hmn
  rw [translate_length, lp] at hnm
  omega

-- This is weaker than eventual superpolynomial growth: it only requires
-- one violation of each polynomial bound somewhere in the family.
def SuperpolynomialSeparation (P Q : ProofSystem) (family : Nat → Formula) : Prop :=
  ∀ C d : Nat, 0 < C → ∃ i m n,
    Shortest P (family i) m ∧ Shortest Q (family i) n ∧
      C * (m + 1) ^ d < n

theorem no_self_separation (P : ProofSystem) (family : Nat → Formula) :
    ¬ SuperpolynomialSeparation P P family := by
  intro h
  obtain ⟨i, m, n, hm, hn, hlt⟩ := h 1 1 (by decide)
  have heq := shortest_unique P (family i) m n hm hn
  simp only [Nat.pow_one, Nat.one_mul] at hlt
  omega

theorem no_tagged_separation (a b : Bool) (family : Nat → Formula) :
    ¬ SuperpolynomialSeparation (taggedSystem a) (taggedSystem b) family := by
  intro h
  obtain ⟨i, m, n, hm, hn, hlt⟩ := h 1 1 (by decide)
  have heq := tagged_shortest_equal a b (family i) m n hm hn
  simp only [Nat.pow_one, Nat.one_mul] at hlt
  omega

def otherTruth : Formula := .imp truth truth

theorem otherTruth_tautology : Tautology otherTruth := by
  intro v _
  rfl

theorem systems_distinct : taggedSystem false ≠ taggedSystem true := by
  intro heq
  let p : Proof := ⟨false, certificate otherTruth⟩
  have h : (taggedSystem false).verifies p otherTruth := by
    change decode false p = otherTruth
    simp only [p, decode, beq_self_eq_true, check_complete otherTruth otherTruth_tautology, Bool.true_and, ↓reduceIte]
    rfl
  rw [heq] at h
  change decode true p = otherTruth at h
  have hf : truth = otherTruth := by simpa [decode, p] using h
  cases hf

-- Semantic analogue of the universal assertion. Polynomial-time membership
-- of the two explicit systems is justified separately by their algorithms.
def SemanticUniversalSeparation : Prop :=
  ∀ P Q : ProofSystem, ∃ family : Nat → Formula,
    SuperpolynomialSeparation P Q family

theorem conjecture3980_false : ¬ SemanticUniversalSeparation := by
  intro h
  obtain ⟨family, hf⟩ := h (taggedSystem false) (taggedSystem true)
  exact no_tagged_separation false true family hf

theorem distinct_pair_version_false :
    ¬ (∀ P Q : ProofSystem, P ≠ Q → ∃ family : Nat → Formula,
      SuperpolynomialSeparation P Q family ∨
      SuperpolynomialSeparation Q P family) := by
  intro h
  obtain ⟨family, hf⟩ := h (taggedSystem false) (taggedSystem true) systems_distinct
  cases hf with
  | inl h => exact no_tagged_separation false true family h
  | inr h => exact no_tagged_separation true false family h

#print axioms conjecture3980_false
#print axioms distinct_pair_version_false
#print axioms shortest_exists
end TLMC3980
