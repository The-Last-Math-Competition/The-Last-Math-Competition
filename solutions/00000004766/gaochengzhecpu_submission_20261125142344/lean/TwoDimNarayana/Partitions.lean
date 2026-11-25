/-
  Conjecture 00000004766 — Two-Dimensional Noncrossing and Narayana Polynomials
  Partitions.lean: Canonical set partitions via Restricted Growth Strings (RGS),
  proved completeness and duplicate-freeness for all N, noncrossing predicates,
  partition joins, refinement order, and bivariate block-enumerators.
-/
import TwoDimNarayana.Basic

namespace TwoDimNarayana

/-! ### Canonical Set Partitions via Restricted Growth Strings -/

/-- Prefix invariant for Restricted Growth Strings: each entry x ≤ m, updating m to max(m, x+1). -/
def isRGSPrefix : List Nat → Nat → Bool
  | [], _ => true
  | x :: xs, m => (x ≤ m) && isRGSPrefix xs (if x == m then m + 1 else m)

/-- A Restricted Growth String (RGS) on {0, ..., N-1} canonically represents a set partition. -/
def isRGS (l : List Nat) : Bool :=
  isRGSPrefix l 0

/-- Generate all RGS suffixes of length `len` with current maximum allowed label `m`. -/
def genRGS : Nat → Nat → List (List Nat)
  | 0, _ => [[]]
  | n + 1, m =>
    (List.range (m + 1)).flatMap (fun x =>
      (genRGS n (if x == m then m + 1 else m)).map (fun xs => x :: xs))

/-- All set partitions of {0, ..., N-1}, represented bijectively by RGS lists of length N. -/
def allRGS (N : Nat) : List (List Nat) :=
  genRGS N 0

/-- Number of blocks in an RGS partition of {0, ..., N-1} (for N ≥ 1, 1 + max label). -/
def numBlocks : List Nat → Nat
  | [] => 0
  | x :: xs => 1 + xs.foldl Nat.max x

/-! ### Soundness, Completeness, and Nodup of `allRGS` -/

theorem mem_genRGS_iff (len : Nat) :
    ∀ (m : Nat) (l : List Nat),
      l ∈ genRGS len m ↔ l.length = len ∧ isRGSPrefix l m = true := by
  induction len with
  | zero =>
    intro m l
    cases l with
    | nil => simp [genRGS, isRGSPrefix]
    | cons _ _ => simp [genRGS]
  | succ n ih =>
    intro m l
    cases l with
    | nil => simp [genRGS, List.mem_flatMap]
    | cons x xs =>
      simp only [genRGS, List.mem_flatMap, List.mem_range, List.mem_map, List.length_cons,
        isRGSPrefix, Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · rintro ⟨a, ha, hmem⟩
        rcases hmem with ⟨ys, hys, hcons⟩
        injection hcons with hx hxs
        subst hx; subst hxs
        have ⟨hlen, hpref⟩ := (ih _ ys).mp hys
        exact ⟨by omega, ⟨by omega, hpref⟩⟩
      · rintro ⟨hlen, ⟨hxle, hpref⟩⟩
        refine ⟨x, by omega, xs, (ih _ xs).mpr ⟨by omega, hpref⟩, rfl⟩

/-- Complete characterization: `l ∈ allRGS N` iff `l` has length `N` and is a valid RGS. -/
theorem mem_allRGS_iff (N : Nat) (l : List Nat) :
    l ∈ allRGS N ↔ l.length = N ∧ isRGS l = true :=
  mem_genRGS_iff N 0 l

theorem nodup_append_disjoint {α : Type} {l1 l2 : List α}
    (h1 : l1.Nodup) (h2 : l2.Nodup)
    (hdisj : ∀ x, x ∈ l1 → x ∈ l2 → False) : (l1 ++ l2).Nodup := by
  induction l1 with
  | nil => exact h2
  | cons a as ih =>
    cases h1 with
    | cons ha has =>
      simp only [List.cons_append]
      apply List.Pairwise.cons
      · intro y hy hay
        cases List.mem_append.mp hy with
        | inl hy1 => exact ha y hy1 hay
        | inr hy2 => exact hdisj a List.mem_cons_self (hay ▸ hy2)
      · exact ih has (fun x hx hx2 => hdisj x (List.mem_cons_of_mem a hx) hx2)

private theorem nodup_map_cons {α : Type} (x : α) {ls : List (List α)} (h : ls.Nodup) :
    (ls.map (fun xs => x :: xs)).Nodup := by
  induction ls with
  | nil => exact List.Pairwise.nil
  | cons a as ihl =>
    cases h with
    | cons hnotmem htail =>
      simp only [List.map]
      apply List.Pairwise.cons
      · intro y hy hxy
        rw [List.mem_map] at hy
        rcases hy with ⟨b, hb, rfl⟩
        injection hxy with _ hab
        exact hnotmem b hb hab
      · exact ihl htail

private theorem nodup_flatMap_disjoint {α β : Type} {l : List α} (f : α → List β)
    (hl : l.Nodup)
    (hf : ∀ a ∈ l, (f a).Nodup)
    (hdisj : ∀ a ∈ l, ∀ b ∈ l, a ≠ b → ∀ y, y ∈ f a → y ∈ f b → False) :
    (l.flatMap f).Nodup := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons a as ih =>
    cases hl with
    | cons ha_not_mem has_nodup =>
      simp only [List.flatMap_cons]
      apply nodup_append_disjoint (hf a List.mem_cons_self)
      · exact ih has_nodup (fun b hb => hf b (List.mem_cons_of_mem a hb))
          (fun b hb c hc hbc => hdisj b (List.mem_cons_of_mem a hb) c (List.mem_cons_of_mem a hc) hbc)
      · intro y hya hyas
        rw [List.mem_flatMap] at hyas
        rcases hyas with ⟨b, hb, hyb⟩
        have hab : a ≠ b := fun h => ha_not_mem b hb h
        exact hdisj a List.mem_cons_self b (List.mem_cons_of_mem a hb) hab y hya hyb

theorem nodup_genRGS (len : Nat) : ∀ m : Nat, (genRGS len m).Nodup := by
  induction len with
  | zero =>
    intro _
    simp [genRGS]
  | succ n ih =>
    intro m
    unfold genRGS
    apply nodup_flatMap_disjoint _ List.nodup_range
    · intro x _
      exact nodup_map_cons x (ih _)
    · intro a _ b _ hab y hya hyb
      rw [List.mem_map] at hya hyb
      rcases hya with ⟨_, _, rfl⟩
      rcases hyb with ⟨_, _, heq⟩
      injection heq with h_eq _
      exact hab h_eq.symm

/-- `allRGS N` enumerates each set partition of `{0, ..., N-1}` without duplicates. -/
theorem nodup_allRGS (N : Nat) : (allRGS N).Nodup :=
  nodup_genRGS N 0

/-! ### Noncrossing Conditions wrt Arbitrary Linear Orders -/

def hasCrossingAux3 (bb : Nat) : List Nat → Bool
  | [] => false
  | x :: xs => (x == bb) || hasCrossingAux3 bb xs

def hasCrossingAux2 (ba bb : Nat) : List Nat → Bool
  | [] => false
  | x :: xs => ((x == ba) && hasCrossingAux3 bb xs) || hasCrossingAux2 ba bb xs

def hasCrossingAux1 (ba : Nat) : List Nat → Bool
  | [] => false
  | x :: xs => ((x != ba) && hasCrossingAux2 ba x xs) || hasCrossingAux1 ba xs

/-- Check if sequence `seq` of block labels has an alternating quadruple `a < b < c < d`
    with `seq[a] = seq[c] ≠ seq[b] = seq[d]`. -/
def hasCrossingInSeq : List Nat → Bool
  | [] => false
  | x :: xs => hasCrossingAux1 x xs || hasCrossingInSeq xs

/-- Noncrossing predicate for partition `part` wrt linear order `ord`. -/
def isNCOrder (part : List Nat) (ord : List Nat) : Bool :=
  !hasCrossingInSeq (ord.map (fun x => part.getD x 0))

/-- Univariate block-enumerator polynomial ∑_{π ∈ L} t^{|π|} for a list of partitions of size N. -/
def blockPoly1 (N : Nat) (parts : List (List Nat)) : Poly1 :=
  (List.range (N + 1)).map (fun k =>
    Int.ofNat ((parts.filter (fun p => numBlocks p == k)).length))

/-- Classical 1D noncrossing partitions NC(n). -/
def ncPartitions (n : Nat) : List (List Nat) :=
  (allRGS n).filter (fun p => isNCOrder p (List.range n))

/-! ### Lattice Operations & Bivariate Coupled-Pair Predicates -/

/-- Refinement order `p1 ≤ p2` on set partitions of `{0, ..., n-1}`:
    every pair in the same block of `p1` is also in the same block of `p2`. -/
def refines (n : Nat) (p1 p2 : List Nat) : Bool :=
  (List.range n).all (fun i =>
    (List.range n).all (fun j =>
      !(p1.getD i 0 == p1.getD j 0) || (p2.getD i 0 == p2.getD j 0)))

/-- Equivalence-relation join `p1 ∨ p2` on `{0, ..., n-1}`, computed by transitive closure
    of same-block adjacency and normalized to canonical labels. -/
def joinPartition (n : Nat) (p1 p2 : List Nat) : List Nat :=
  let sameStep (i j : Nat) : Bool :=
    (p1.getD i 0 == p1.getD j 0) || (p2.getD i 0 == p2.getD j 0)
  let adj0 : List (List Bool) :=
    (List.range n).map (fun i => (List.range n).map (fun j => sameStep i j))
  let warshallStep (mat : List (List Bool)) (k : Nat) : List (List Bool) :=
    (List.range n).map (fun i =>
      let ik := (mat.getD i []).getD k false
      (List.range n).map (fun j =>
        (mat.getD i []).getD j false || (ik && (mat.getD k []).getD j false)))
  let closed := (List.range n).foldl warshallStep adj0
  -- Assign each element i to the smallest element j in its equivalence class
  (List.range n).map (fun i =>
    ((List.range n).find? (fun j => (closed.getD i []).getD j false)).getD i)

def altDirAux3 (Y : Nat → Bool) : List Nat → Bool
  | [] => false
  | d :: ds => Y d || altDirAux3 Y ds

def altDirAux2 (X Y : Nat → Bool) : List Nat → Bool
  | [] => false
  | c :: cs => (X c && altDirAux3 Y cs) || altDirAux2 X Y cs

def altDirAux1 (X Y : Nat → Bool) : List Nat → Bool
  | [] => false
  | b :: bs => (Y b && altDirAux2 X Y bs) || altDirAux1 X Y bs

def altDir (X Y : Nat → Bool) : List Nat → Bool
  | [] => false
  | a :: as => (X a && altDirAux1 X Y as) || altDir X Y as

/-- Check if block `b1` of `p1` and block `b2` of `p2` strictly alternate `a < b < c < d` in `0..n-1`. -/
def twoBlocksCross (n : Nat) (inB1 inB2 : Nat → Bool) : Bool :=
  let pts := List.range n
  altDir inB1 inB2 pts || altDir inB2 inB1 pts

/-- Mutual block noncrossing between two partitions `p1, p2` on `{0, ..., n-1}`:
    no block of `p1` strictly crosses any block of `p2`. -/
def mutuallyBlockNC (n : Nat) (p1 p2 : List Nat) : Bool :=
  let k1 := numBlocks p1
  let k2 := numBlocks p2
  !(List.range k1).any (fun b1 =>
    (List.range k2).any (fun b2 =>
      twoBlocksCross n (fun x => p1.getD x 0 == b1) (fun x => p2.getD x 0 == b2)))

/-- Construct bivariate polynomial ∑_{(p1, p2) ∈ pairs} u^{f1(p1)} v^{f2(p2)} up to degree `maxDeg`. -/
def makePoly2 {α : Type} (maxDeg : Nat) (items : List α) (degU degV : α → Nat) : Poly2 :=
  (List.range (maxDeg + 1)).map (fun i =>
    (List.range (maxDeg + 1)).map (fun j =>
      Int.ofNat ((items.filter (fun x => degU x == i && degV x == j)).length)))

/-- Sum of all coefficients in a bivariate polynomial. -/
def totalCount2 (P : Poly2) : Int :=
  P.foldl (fun acc row => acc + row.foldl (· + ·) 0) 0

end TwoDimNarayana
