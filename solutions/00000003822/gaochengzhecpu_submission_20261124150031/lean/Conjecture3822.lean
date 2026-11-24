import Std

namespace Conjecture3822

universe u

variable {Vertex : Type u}

/-- A walk follows arrows, can revisit vertices, and records its length. -/
inductive Walk (arrow : Vertex → Vertex → Prop) : Vertex → Vertex → Nat → Prop where
  | nil (vertex : Vertex) : Walk arrow vertex vertex 0
  | cons {a b c : Vertex} {length : Nat} (edge : arrow a b)
      (tail : Walk arrow b c length) : Walk arrow a c (length + 1)

namespace Walk

theorem append {arrow : Vertex → Vertex → Prop} {a b c : Vertex} {m n : Nat}
    (first : Walk arrow a b m) (second : Walk arrow b c n) :
    Walk arrow a c (m + n) := by
  induction first with
  | nil => simpa only [Nat.zero_add] using second
  | @cons x y z length edge walk ih =>
    simpa only [Nat.add_assoc, Nat.add_comm 1 n] using Walk.cons edge (ih second)

theorem map {arrow newArrow : Vertex → Vertex → Prop} {a b : Vertex} {n : Nat}
    (walk : Walk arrow a b n) (transform : ∀ ⦃x y⦄, arrow x y → newArrow x y) :
    Walk newArrow a b n := by
  induction walk with
  | nil => exact Walk.nil _
  | cons edge _ ih => exact Walk.cons (transform edge) ih

theorem reverseMap {arrow newArrow : Vertex → Vertex → Prop} {a b : Vertex} {n : Nat}
    (walk : Walk arrow a b n) (reflect : Vertex → Vertex)
    (transform : ∀ ⦃x y⦄, arrow x y → newArrow (reflect y) (reflect x)) :
    Walk newArrow (reflect b) (reflect a) n := by
  induction walk with
  | nil => exact Walk.nil _
  | cons edge _ ih => exact ih.append (Walk.cons (transform edge) (Walk.nil _))

end Walk

/-- Forget the orientation of the arrows. -/
def undirected (arrow : Vertex → Vertex → Prop) (a b : Vertex) : Prop :=
  arrow a b ∨ arrow b a

/-- Every distance is at most d, and some distance is at least d.
    For a nonempty connected finite graph this characterizes its diameter. -/
def HasDiameter (edge : Vertex → Vertex → Prop) (d : Nat) : Prop :=
  (∀ a b, ∃ n ≤ d, Walk edge a b n) ∧
    ∃ a b, ∀ n, Walk edge a b n → d ≤ n

theorem directed_drop {arrow : Vertex → Vertex → Prop} (height : Vertex → Int)
    (edgeDrop : ∀ ⦃a b⦄, arrow a b → height a = height b + 2)
    {a b : Vertex} {n : Nat} (walk : Walk arrow a b n) :
    height a = height b + 2 * (n : Int) := by
  induction walk with
  | nil => simp
  | cons edge _ ih =>
    have drop := edgeDrop edge
    omega

theorem undirected_drop_bound {arrow : Vertex → Vertex → Prop} (height : Vertex → Int)
    (edgeDrop : ∀ ⦃a b⦄, arrow a b → height a = height b + 2)
    {a b : Vertex} {n : Nat} (walk : Walk (undirected arrow) a b n) :
    height a ≤ height b + 2 * (n : Int) := by
  induction walk with
  | nil => simp
  | cons edge _ ih =>
    rcases edge with forward | backward
    · have drop := edgeDrop forward
      omega
    · have drop := edgeDrop backward
      omega

/-- A graph generated from a highest vertex, with a height-negating,
    arrow-reversing involution, has diameter the height of that vertex
    when each arrow drops the height by two. In a finite-type crystal
    the height is the weight paired with 2ρ∨. -/
theorem highest_weight_diameter (arrow : Vertex → Vertex → Prop)
    (height : Vertex → Int) (highest : Vertex) (opposite : Vertex → Vertex)
    (edgeDrop : ∀ ⦃a b⦄, arrow a b → height a = height b + 2)
    (generated : ∀ b, ∃ n, Walk arrow highest b n)
    (involutive : ∀ b, opposite (opposite b) = b)
    (reverses : ∀ ⦃a b⦄, arrow a b → arrow (opposite b) (opposite a))
    (negatesHeight : ∀ b, height (opposite b) = - height b) :
    HasDiameter (undirected arrow) (height highest).toNat := by
  let lowest := opposite highest
  have lowestHeight : height lowest = - height highest := negatesHeight highest
  have walksToLowest (a : Vertex) : ∃ n, Walk arrow a lowest n := by
    obtain ⟨n, walk⟩ := generated (opposite a)
    exact ⟨n, by simpa only [involutive] using walk.reverseMap opposite reverses⟩
  obtain ⟨span, ends⟩ := generated lowest
  have endsDrop := directed_drop height edgeDrop ends
  have diameter_eq_span : (height highest).toNat = span := by omega
  rw [diameter_eq_span]
  constructor
  · intro a b
    obtain ⟨ha, fromHighA⟩ := generated a
    obtain ⟨hb, fromHighB⟩ := generated b
    obtain ⟨la, toLowA⟩ := walksToLowest a
    obtain ⟨lb, toLowB⟩ := walksToLowest b
    have haDrop := directed_drop height edgeDrop fromHighA
    have hbDrop := directed_drop height edgeDrop fromHighB
    have laDrop := directed_drop height edgeDrop toLowA
    have lbDrop := directed_drop height edgeDrop toLowB
    by_cases highRoute : ha + hb ≤ span
    · have aToHighest := fromHighA.reverseMap id (newArrow := undirected arrow)
          (fun _ _ edge => Or.inr edge)
      have highestToB := fromHighB.map (newArrow := undirected arrow)
        (fun _ _ edge => Or.inl edge)
      exact ⟨ha + hb, highRoute, aToHighest.append highestToB⟩
    · have aToLowest := toLowA.map (newArrow := undirected arrow)
        (fun _ _ edge => Or.inl edge)
      have lowestToB := toLowB.reverseMap id (newArrow := undirected arrow)
          (fun _ _ edge => Or.inr edge)
      exact ⟨la + lb, by omega, aToLowest.append lowestToB⟩
  · refine ⟨highest, lowest, ?_⟩
    intro n walk
    have drop := undirected_drop_bound height edgeDrop walk
    omega

/-- Specialize the graph result to arrows that subtract simple roots. The
    supplied pairing is with the sum of positive coroots, 2ρ∨. -/
theorem crystal_diameter_from_weights {Weight Index : Type u} [Sub Weight]
    (arrow : Vertex → Vertex → Prop) (highest : Vertex) (opposite : Vertex → Vertex)
    (weight : Vertex → Weight) (simpleRoot : Index → Weight)
    (longest : Weight → Weight) (pairWithCorootSum : Weight → Int)
    (subPair : ∀ x y, pairWithCorootSum (x - y) = pairWithCorootSum x - pairWithCorootSum y)
    (simplePair : ∀ i, pairWithCorootSum (simpleRoot i) = 2)
    (loweringWeight : ∀ ⦃a b⦄, arrow a b → ∃ i, weight b = weight a - simpleRoot i)
    (reflectedWeight : ∀ b, weight (opposite b) = longest (weight b))
    (longestPair : ∀ w, pairWithCorootSum (longest w) = - pairWithCorootSum w)
    (generated : ∀ b, ∃ n, Walk arrow highest b n)
    (involutive : ∀ b, opposite (opposite b) = b)
    (reverses : ∀ ⦃a b⦄, arrow a b → arrow (opposite b) (opposite a)) :
    HasDiameter (undirected arrow) (pairWithCorootSum (weight highest)).toNat := by
  refine highest_weight_diameter arrow (fun b => pairWithCorootSum (weight b))
    highest opposite ?_ generated involutive reverses ?_
  · intro a b edge
    obtain ⟨i, weightDrop⟩ := loweringWeight edge
    have pairDrop : pairWithCorootSum (weight b) = pairWithCorootSum (weight a) - 2 := by
      rw [weightDrop, subPair, simplePair]
    change pairWithCorootSum (weight a) = pairWithCorootSum (weight b) + 2
    omega
  · intro b
    change pairWithCorootSum (weight (opposite b)) = -pairWithCorootSum (weight b)
    rw [reflectedWeight, longestPair]

end Conjecture3822

#print axioms Conjecture3822.crystal_diameter_from_weights
