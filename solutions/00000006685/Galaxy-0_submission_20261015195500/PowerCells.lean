import Std

namespace PowerCells6685

structure Vec3 where
  x : Rat
  y : Rat
  z : Rat
  deriving DecidableEq, Repr

def add (a b : Vec3) : Vec3 := ⟨a.x+b.x,a.y+b.y,a.z+b.z⟩
def sub (a b : Vec3) : Vec3 := ⟨a.x-b.x,a.y-b.y,a.z-b.z⟩
def scale (t : Rat) (a : Vec3) : Vec3 := ⟨t*a.x,t*a.y,t*a.z⟩
def dot (a b : Vec3) : Rat := a.x*b.x+a.y*b.y+a.z*b.z
def cross (a b : Vec3) : Vec3 :=
  ⟨a.y*b.z-a.z*b.y,a.z*b.x-a.x*b.z,a.x*b.y-a.y*b.x⟩
def zero : Vec3 := ⟨0,0,0⟩
def normSq (a : Vec3) : Rat := dot a a

def site (i : Fin 5) : Vec3 := match i.val with
  | 0 => ⟨0,0,0⟩
  | 1 => ⟨1,1,1⟩
  | 2 => ⟨1,-1,-1⟩
  | 3 => ⟨-1,1,-1⟩
  | _ => ⟨-1,-1,1⟩

def weight (i : Fin 5) : Rat := (i.val : Rat)/100

def power (i : Fin 5) (x : Vec3) : Rat := normSq (sub x (site i)) - weight i

def InPowerCell (i : Fin 5) (x : Vec3) : Prop :=
  ∀ k : Fin 5, power i x ≤ power k x
instance (i : Fin 5) (x : Vec3) : Decidable (InPowerCell i x) :=
  inferInstanceAs (Decidable (∀ k : Fin 5, power i x ≤ power k x))

/-- Strict minimizer on a bisector: all other sites have larger power. -/
def StrictBisector (i j : Fin 5) (x : Vec3) : Prop :=
  power i x = power j x ∧
  ∀ k : Fin 5, k ≠ i → k ≠ j → power i x < power k x
instance (i j : Fin 5) (x : Vec3) : Decidable (StrictBisector i j x) :=
  inferInstanceAs (Decidable (power i x = power j x ∧
    ∀ k : Fin 5, k ≠ i → k ≠ j → power i x < power k x))

/-- Strict bisector witnesses are genuinely in both defined power cells. -/
theorem strictBisector_mem_cells (i j : Fin 5) (x : Vec3)
    (h : StrictBisector i j x) : InPowerCell i x ∧ InPowerCell j x := by
  have hi : InPowerCell i x := by
    intro k
    by_cases hki : k = i
    · subst k; exact Rat.le_refl
    by_cases hkj : k = j
    · subst k; rw [h.1]; exact Rat.le_refl
    exact Rat.le_of_lt (h.2 k hki hkj)
  refine ⟨hi, ?_⟩
  intro k
  rw [← h.1]
  exact hi k

/-- Three noncollinear strict bisector points certify a two-dimensional facet.
The paper supplies the elementary convexity bridge from this finite certificate
in rational coordinates to shared facets of the corresponding real power cells. -/
structure FacetCertificate (i j : Fin 5) where
  a : Vec3
  b : Vec3
  c : Vec3
  ha : StrictBisector i j a
  hb : StrictBisector i j b
  hc : StrictBisector i j c
  noncollinear : cross (sub b a) (sub c a) ≠ zero

/-- Adjacency is witnessed geometrically, not assigned by a graph table. -/
def FacetAdjacent (i j : Fin 5) : Prop := i ≠ j ∧ Nonempty (FacetCertificate i j)

def center (i j : Fin 5) : Vec3 :=
  if i.val = 0 then scale ((3-weight j)/6) (site j)
  else if j.val = 0 then scale ((3-weight i)/6) (site i)
  else add (add (site i) (site j))
    (scale ((weight j-weight i)/16) (sub (site i) (site j)))

def tangentU (n : Vec3) : Vec3 :=
  if n.x ≠ 0 then ⟨-n.y,n.x,0⟩
  else if n.y ≠ 0 then ⟨n.y,-n.x,0⟩
  else ⟨1,0,0⟩
def tangentV (n : Vec3) : Vec3 :=
  if n.x ≠ 0 then ⟨-n.z,0,n.x⟩
  else if n.y ≠ 0 then ⟨0,-n.z,n.y⟩
  else ⟨0,1,0⟩

def pointA (i j : Fin 5) := center i j
def pointB (i j : Fin 5) := add (center i j)
  (scale (1/1000) (tangentU (sub (site i) (site j))))
def pointC (i j : Fin 5) := add (center i j)
  (scale (1/1000) (tangentV (sub (site i) (site j))))

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- All certificates check by exact rational arithmetic in the kernel. -/
theorem facet_checks : ∀ i j : Fin 5, i ≠ j →
    StrictBisector i j (pointA i j) ∧
    StrictBisector i j (pointB i j) ∧
    StrictBisector i j (pointC i j) ∧
    cross (sub (pointB i j) (pointA i j))
      (sub (pointC i j) (pointA i j)) ≠ zero := by decide +kernel

def facetCertificate (i j : Fin 5) (h : i ≠ j) : FacetCertificate i j where
  a := pointA i j
  b := pointB i j
  c := pointC i j
  ha := (facet_checks i j h).1
  hb := (facet_checks i j h).2.1
  hc := (facet_checks i j h).2.2.1
  noncollinear := (facet_checks i j h).2.2.2

theorem adjacency_complete (i j : Fin 5) : FacetAdjacent i j ↔ i ≠ j := by
  constructor
  · exact fun h => h.1
  · exact fun h => ⟨h, ⟨facetCertificate i j h⟩⟩

/-- In particular, no site is hidden or has an empty power cell. -/
theorem own_site_strict : ∀ i k : Fin 5, i ≠ k →
    power i (site i) < power k (site i) := by decide +kernel

theorem weights_distinct : ∀ i j : Fin 5, i ≠ j → weight i ≠ weight j := by decide +kernel

def orientedVolume (i j k l : Fin 5) : Rat :=
  dot (sub (site j) (site i))
    (cross (sub (site k) (site i)) (sub (site l) (site i)))

/-- Affine general position: every four sites span three dimensions. -/
theorem every_four_independent : ∀ i j k l : Fin 5,
    i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l →
    orientedVolume i j k l ≠ 0 := by decide +kernel

/-- The sum of the four outer sites is the zero vector. -/
theorem outer_site_sum : add (add (site 1) (site 2)) (add (site 3) (site 4)) = zero := by decide +kernel

/-- The sum of their lifted squared norms is nonzero; together with the
previous vector identity this obstructs one common power sphere. -/
theorem power_sphere_obstruction :
    (normSq (site 1)-weight 1) + (normSq (site 2)-weight 2) +
    (normSq (site 3)-weight 3) + (normSq (site 4)-weight 4) = 119/10 := by decide +kernel

end PowerCells6685
