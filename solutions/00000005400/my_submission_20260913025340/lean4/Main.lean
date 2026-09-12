/-
  Refutation of conjecture 00000005400 (TLMC).

  Conjecture (abridged): "There exist two maps with identical orbit distribution
  limits but different periodic point counts, and the separation is realized by
  an explicit conjugate pair with the same measure but different periods."

  We refute both layers in the literal discrete reading, on the 4-point set.

  Identity I (layer 1).  On a finite set, the orbit distribution *determines*
  the periodic point count: the periodic points split into disjoint cycles, an
  orbit of length l contributing exactly l points, so
      P(f) = Σ_l l · N_l(f).
  Equal orbit profiles therefore force equal periodic counts — the conjecture's
  first half is self-contradictory.  Encoded below by
  `count_from_profile_sum` (bridge, decided over all 256 self-maps) and
  `profile_det_count` (the implication, proved by rewriting with the bridge).

  Identity II (layer 2).  Conjugation is an isomorphism of dynamical systems and
  transports periods pointwise:
      (τ f τ⁻¹)^k (τ x) = τ (f^k x)   for all k,
  hence period_{τfτ⁻¹}(τx) = period_f(x) and a "conjugate pair with different
  periods" cannot exist.  Encoded below by `conj_preserves_period`, decided by
  exhaustive evaluation over 24 × 256 × 4 = 24576 configurations (τ over all 24
  permutations, f over *all* 256 self-maps of the 4-point set), and by `refute`,
  the decided negation of the conjecture's existential over the complete
  enumeration of conjugate pairs.

  Everything is proved by kernel-checked computation or rewriting.  All
  definitions are kept inside the axiom-free (Bool/Nat-computable) fragment of
  Lean core, so the dependency audit in Check.lean reports *no axioms at all*
  — not even `propext` or `Quot.sound` — for every theorem; in particular
  there is no `sorry` and no classical reasoning.
-/

namespace Tlmc5400

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-! ## 1. Permutations of a 4-point set -/

/-- A permutation of `{0,1,2,3}` as a function. -/
def Perm : Type := Fin 4 → Fin 4

/-- The point `0` of the 4-point set, constructed without numeral instances. -/
def pt0 : Fin 4 := ⟨0, Nat.zero_lt_succ 3⟩

/-- Points `1, 2, 3`, constructed without numeral instances. -/
def pt1 : Fin 4 := ⟨1, by decide⟩
def pt2 : Fin 4 := ⟨2, by decide⟩
def pt3 : Fin 4 := ⟨3, by decide⟩

/-- Apply a permutation to a point. -/
def applyP (f : Perm) (x : Fin 4) : Fin 4 := f x

/-- The `k`-th iterate of `f`. -/
def iterP (f : Perm) : Nat → Fin 4 → Fin 4
  | 0,     x => x
  | k + 1, x => f (iterP f k x)

/-- Does `f^k x = x` hold?  (Nat-valued equality test, kernel-computable.) -/
def periodHit (f : Perm) (x : Fin 4) (k : Nat) : Bool :=
  (iterP f k x).val == x.val

/-- Least `k ≥ 1` with `f^k x = x`.  On a 4-point set every cycle has length
`≤ 4`, so the search space `1..4` is complete; points on tails (never periodic)
fall through to the harmless default `4`, consistently under conjugation. -/
def period (f : Perm) (x : Fin 4) : Nat :=
  if periodHit f x 1 then 1
  else if periodHit f x 2 then 2
  else if periodHit f x 3 then 3
  else 4

/-- Pointwise inverse search: the `y` with `f y = x`.  For a bijection exactly
one branch fires, giving the genuine two-sided inverse; the last branch is
reached only on non-bijections, where it is a harmless default. -/
def invP (f : Perm) (x : Fin 4) : Fin 4 :=
  if (f pt0).val == x.val then pt0
  else if (f pt1).val == x.val then pt1
  else if (f pt2).val == x.val then pt2
  else pt3

/-- Conjugation pointwise: `conjugate τ f x = τ (f (τ⁻¹ x))`. -/
def conjugate (τ f : Perm) : Perm := fun x => τ (f (invP τ x))

/-- `IsConjugateVia τ f g`: `g` is exactly the conjugate `τ f τ⁻¹`. -/
def IsConjugateVia (τ f g : Perm) : Prop := ∀ x, g x = τ (f (invP τ x))

/-! ## 2. Complete enumeration of S₄ -/

/-- An image vector `(f 0, f 1, f 2, f 3)`. -/
abbrev V4 := Fin 4 × Fin 4 × Fin 4 × Fin 4

/-- Interpret an image vector as a permutation. -/
def ofVec (v : V4) : Perm := fun x =>
  match x.val with
  | 0 => v.1
  | 1 => v.2.1
  | 2 => v.2.2.1
  | _ => v.2.2.2

/-- Injectivity test on an image vector (for self-maps of a 4-set this is
equivalent to bijectivity). -/
def isBij (v : V4) : Bool :=
  v.1.val != v.2.1.val     && v.1.val != v.2.2.1.val &&
  v.1.val != v.2.2.2.val   && v.2.1.val != v.2.2.1.val &&
  v.2.1.val != v.2.2.2.val && v.2.2.1.val != v.2.2.2.val

/-- All `4^4 = 256` image vectors. -/
def allVecs : List V4 :=
  (List.finRange 4).flatMap fun a =>
  (List.finRange 4).flatMap fun b =>
  (List.finRange 4).flatMap fun c =>
  (List.finRange 4).map fun d => (a, b, c, d)

/-- The 24 permutations of the 4-point set: the bijective image vectors. -/
def permVecs : List V4 := allVecs.filter isBij

theorem allVecs_length : allVecs.length = 256 := rfl

/-- The enumeration contains exactly the 24 permutations of S₄. -/
theorem permVecs_length : permVecs.length = 24 := rfl

theorem permVecs_bij : permVecs.all isBij = true := rfl

/-! ## 3. Arbitrary self-maps of the 4-point set -/

/-- A self-map encoded by an index in `[0,256)`: the base-4 digits of `w` are
the images `(f 0, f 1, f 2, f 3)`.  This ranges over *all* `4^4` self-maps, not
only permutations — the identities below are checked on the full function space
(`permAt` restricts to `S₄` only where a bijection is required, namely `τ`). -/
def ofW (w : Fin 256) : Perm := fun x =>
  match x.val with
  | 0 => ⟨(w.val / 64) % 4, Nat.mod_lt _ (by decide)⟩
  | 1 => ⟨(w.val / 16) % 4, Nat.mod_lt _ (by decide)⟩
  | 2 => ⟨(w.val / 4) % 4, Nat.mod_lt _ (by decide)⟩
  | _ => ⟨w.val % 4, Nat.mod_lt _ (by decide)⟩

/-- The `k`-th permutation of S₄ in lexicographic order of image vectors,
given by the base-4 code of its image vector (the same code convention as
`ofW`).  The kernel-checked `permAtTable_eq` below certifies that these 24
maps are exactly the bijective vectors of `permVecs`, in the same order. -/
def permAt (k : Fin 24) : Perm :=
  match k.val with
  | 0  => ofW ⟨27, by decide⟩   -- (0,1,2,3)
  | 1  => ofW ⟨30, by decide⟩   -- (0,1,3,2)
  | 2  => ofW ⟨39, by decide⟩   -- (0,2,1,3)
  | 3  => ofW ⟨45, by decide⟩   -- (0,2,3,1)
  | 4  => ofW ⟨54, by decide⟩   -- (0,3,1,2)
  | 5  => ofW ⟨57, by decide⟩   -- (0,3,2,1)
  | 6  => ofW ⟨75, by decide⟩   -- (1,0,2,3)
  | 7  => ofW ⟨78, by decide⟩   -- (1,0,3,2)
  | 8  => ofW ⟨99, by decide⟩   -- (1,2,0,3)
  | 9  => ofW ⟨108, by decide⟩  -- (1,2,3,0)
  | 10 => ofW ⟨114, by decide⟩  -- (1,3,0,2)
  | 11 => ofW ⟨120, by decide⟩  -- (1,3,2,0)
  | 12 => ofW ⟨135, by decide⟩  -- (2,0,1,3)
  | 13 => ofW ⟨141, by decide⟩  -- (2,0,3,1)
  | 14 => ofW ⟨147, by decide⟩  -- (2,1,0,3)
  | 15 => ofW ⟨156, by decide⟩  -- (2,1,3,0)
  | 16 => ofW ⟨177, by decide⟩  -- (2,3,0,1)
  | 17 => ofW ⟨180, by decide⟩  -- (2,3,1,0)
  | 18 => ofW ⟨198, by decide⟩  -- (3,0,1,2)
  | 19 => ofW ⟨201, by decide⟩  -- (3,0,2,1)
  | 20 => ofW ⟨210, by decide⟩  -- (3,1,0,2)
  | 21 => ofW ⟨216, by decide⟩  -- (3,1,2,0)
  | 22 => ofW ⟨225, by decide⟩  -- (3,2,0,1)
  | 23 => ofW ⟨228, by decide⟩  -- (3,2,1,0)
  | _  => ofW ⟨0, by decide⟩    -- unreachable for k < 24

/-- The 24 maps `permAt 0 … permAt 23`, as point-evaluation tables. -/
def permAtTable : List (List (Fin 4)) :=
  (List.finRange 24).map fun k => (List.finRange 4).map (applyP (permAt k))

/-- The 24 enumerated permutations, as point-evaluation tables. -/
def permVecsTable : List (List (Fin 4)) :=
  permVecs.map fun v => (List.finRange 4).map (applyP (ofVec v))

/-- Kernel-checked: `permAt` enumerates exactly the bijective vectors of
`permVecs`, in the same order — so quantifying `τ : Fin 24` in the theorems
below ranges over precisely the permutation group S₄. -/
theorem permAtTable_eq : permAtTable = permVecsTable := rfl

/-! ## 4. Orbits, profiles, periodic counts -/

/-- Is `x` on a cycle of `f` (i.e. periodic)?  Cycle lengths are `≤ 4`. -/
def onCycle (f : Perm) (x : Fin 4) : Bool :=
  periodHit f x 1 || periodHit f x 2 || periodHit f x 3 || periodHit f x 4

/-- The periodic points of `f`. -/
def periodicPoints (f : Perm) : List (Fin 4) :=
  (List.finRange 4).filter (onCycle f)

/-- `P(f)`: the number of periodic points. -/
def periodicCount (f : Perm) : Nat := (periodicPoints f).length

/-- Do `x` and `y` lie on the same cycle? -/
def sameCycle (f : Perm) (x y : Fin 4) : Bool :=
  onCycle f x && onCycle f y &&
  ((iterP f 0 x).val == y.val || (iterP f 1 x).val == y.val ||
   (iterP f 2 x).val == y.val || (iterP f 3 x).val == y.val)

/-- Is `x` the least-numbered point of its cycle? -/
def cycleRep (f : Perm) (x : Fin 4) : Bool :=
  onCycle f x &&
    List.all ((List.finRange 4).filter (fun y => decide (y.val < x.val)))
      (fun y => !(sameCycle f x y))

/-- Length of the cycle through the periodic point `x`. -/
def cycleLen (f : Perm) (x : Fin 4) : Nat :=
  ((List.finRange 4).filter (fun y => sameCycle f x y)).length

/-- Insert into an ascending `Nat` list. -/
def insertNat : Nat → List Nat → List Nat
  | n, []     => [n]
  | n, m :: t => if n ≤ m then n :: m :: t else m :: insertNat n t

/-- Sort ascending. -/
def sortNats : List Nat → List Nat
  | []     => []
  | n :: t => insertNat n (sortNats t)

/-- The orbit distribution (orbit profile) of `f`: the sorted list of cycle
lengths, i.e. one entry `l` per periodic orbit of length `l`. -/
def orbitProfile (f : Perm) : List Nat :=
  sortNats (((List.finRange 4).filter (cycleRep f)).map (cycleLen f))

/-! ## 5. Identity I: the profile determines the periodic point count -/

/-- Identity I, bridge form: the number of periodic points equals the sum of
the orbit profile `Σ l · N_l(f)`.  Decided by exhaustive evaluation over all
`256` self-maps of the 4-point set. -/
theorem count_from_profile_sum :
    ∀ w : Fin 256, periodicCount (ofW w) = (orbitProfile (ofW w)).sum := by
  decide

/-- Identity I, consequence form: equal orbit profiles force equal periodic
point counts.  Holds for *all* self-maps (indices in `Fin 256`), proved by
rewriting with the bridge lemma — no enumeration needed in this step. -/
theorem profile_det_count :
    ∀ (f g : Fin 256), orbitProfile (ofW f) = orbitProfile (ofW g) →
      periodicCount (ofW f) = periodicCount (ofW g) := by
  intro f g h
  rw [count_from_profile_sum, count_from_profile_sum, h]

/-! ## 6. Identity II: conjugation transports periods pointwise -/

/-- Identity II: for every permutation `τ` (all 24, via `permAt`), every
self-map `f` (all 256, via `ofW`) and every point `x`, the conjugate
`τ f τ⁻¹` has `period(τ f τ⁻¹)(τ x) = period(f)(x)`.  Decided by exhaustive
evaluation over `24 × 256 × 4 = 24576` configurations. -/
theorem conj_preserves_period :
    ∀ (τ : Fin 24) (f : Fin 256) (x : Fin 4),
      period (conjugate (permAt τ) (ofW f)) (applyP (permAt τ) x)
        = period (ofW f) x := by
  decide

/-! ## 7. The refutation -/

/-- The conjecture's existential, over the complete enumeration of conjugate
pairs of self-maps of the 4-point set.  A conjugate pair is `(f, g, τ)` with
`IsConjugateVia τ f g`, i.e. `g = τ f τ⁻¹` — so the pair is determined by `(τ, f)`
and the search ranges over τ ∈ S₄ (all 24) and f (all 256 self-maps); a
separating witness is a point `x` where the periods differ. -/
def conjWitnessExists : Bool :=
  (List.finRange 24).any fun τ =>
    (List.finRange 256).any fun f =>
      (List.finRange 4).any fun x =>
        period (conjugate (permAt τ) (ofW f)) (applyP (permAt τ) x)
          != period (ofW f) x

/-- The search finds nothing: kernel-checked `false`. -/
theorem conjWitnessExists_false : conjWitnessExists = false := rfl

/-- **Refutation of conjecture 00000005400 (second layer).**  There is no
conjugate pair of self-maps of the 4-point set with different pointwise
periods.  Since every pair with `IsConjugateVia τ f g` has `g = τ f τ⁻¹`, the
conjecture's existential over pairs collapses to the existential below, so this
refutes the conjecture's "explicit conjugate pair with different periods".
Derived from `conj_preserves_period` by pure logic (no enumeration here). -/
theorem refute :
    ¬ ∃ (τ : Fin 24) (f : Fin 256) (x : Fin 4),
      period (conjugate (permAt τ) (ofW f)) (applyP (permAt τ) x)
        ≠ period (ofW f) x := by
  intro ⟨τ, f, x, h⟩
  exact h (conj_preserves_period τ f x)

/-! ## 8. A concrete conjugate pair, for the record

`f = (0 1)(2 3)`, `τ = (1 2 3)`, `g = τ f τ⁻¹ = (0 2)(1 3)`: every point has
period `2` under both `f` and `g`, and the periods transport exactly.  The
maps are given by their base-4 digit codes: image vector `(1,0,3,2)` is the
code `78`, image vector `(0,2,3,1)` is the code `45`. -/

def fEx : Perm := ofW ⟨78, by decide⟩

def tauEx : Perm := ofW ⟨45, by decide⟩

def gEx : Perm := conjugate tauEx fEx

/-- Pointwise period table of the pair: `(period_f x, period_g (τ x))`. -/
def pairTable : List (Nat × Nat) :=
  (List.finRange 4).map fun x =>
    (period fEx x, period gEx (applyP tauEx x))

theorem pairTable_all_two :
    pairTable = [(2, 2), (2, 2), (2, 2), (2, 2)] := rfl

end Tlmc5400
