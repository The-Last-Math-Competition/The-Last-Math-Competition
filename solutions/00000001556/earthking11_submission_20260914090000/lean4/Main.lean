/-
  Refutation certificate for conjecture 00000001556.

  Conjecture (as filed): the chromatic number of the planar distance graph
  G(Z^2, D) with D = {1, 2, 4} is 7.

  Disproof.  The file writes three scalars, so D is a set of distances, and
  lattice-colouring work also states distance sets as SQUARED norms.  We cover
  both standard readings at once:

    * squared reading:  displacements with squared norm in {1,2,4};
    * Euclidean reading: axis displacements of Euclidean length 1, 2 or 4.

  `D` below is the UNION of the two displacement sets, so it contains the edge
  set of BOTH readings.  The map

      color(x,y) = (x + 2y) mod 5

  is shown to change along every displacement of `D`, at every lattice point,
  hence it is a proper 5-colouring of the union graph, and a fortiori of each
  reading.  Therefore chi <= 5 < 7, contradicting the claimed value 7.

  Lower bounds are certified by explicit finite cliques (over the union graph,
  which contains both readings): a 5-clique for the squared reading and a
  3-clique for the Euclidean reading.  Combined with the colourings this pins
  chi = 5 (squared reading) and chi = 3 (Euclidean reading) exactly.

  Core Lean only (`import Std`), no Mathlib, no `sorry`.
-/
import Std

namespace Tlmc1556

/-- Union of the two plausible displacement sets for "D = {1,2,4}":
    * the 12 vectors of squared norm 1, 2 or 4;
    * the axis vectors of Euclidean length 1, 2 or 4 (adds (±4,0), (0,±4)). -/
def D : List (Int × Int) :=
  [(1,0),(-1,0),(0,1),(0,-1),
   (1,1),(1,-1),(-1,1),(-1,-1),
   (2,0),(-2,0),(0,2),(0,-2),
   (4,0),(-4,0),(0,4),(0,-4)]

/-- Squared reading: displacements with dx*dx + dy*dy in {1,2,4}.  (12 vectors.) -/
def Dsq : List (Int × Int) :=
  [(1,0),(-1,0),(0,1),(0,-1),
   (1,1),(1,-1),(-1,1),(-1,-1),
   (2,0),(-2,0),(0,2),(0,-2)]

/-- Euclidean reading: axis displacements of length 1, 2 or 4.  (12 vectors.) -/
def Deuc : List (Int × Int) :=
  [(1,0),(-1,0),(0,1),(0,-1),
   (2,0),(-2,0),(0,2),(0,-2),
   (4,0),(-4,0),(0,4),(0,-4)]

/-- The 5-colouring `c(x,y) = (x + 2y) mod 5`. -/
def color (p : Int × Int) : Int := (p.1 + 2 * p.2) % 5

/-- The 3-colouring `c3(x,y) = (x + y) mod 3` for the Euclidean reading. -/
def color3 (p : Int × Int) : Int := (p.1 + p.2) % 3

/-- Finite verification: no displacement of the union `D` satisfies
`dx + 2 dy ≡ 0 (mod 5)`. -/
theorem D_ok : D.all (fun e => decide ((e.1 + 2 * e.2) % 5 ≠ 0)) = true := by
  decide

/-- **Properness for the union graph.**  For every lattice point `(x,y)` and
every displacement `d ∈ D`, the colours of the two endpoints differ.  This is
the whole refutation: a proper 5-colouring of the union graph is proper for
each reading, so each has chromatic number at most 5. -/
theorem color_shift_ne (x y : Int) (d : Int × Int) (hd : d ∈ D) :
    color (x + d.1, y + d.2) ≠ color (x, y) := by
  have hne : (d.1 + 2 * d.2) % 5 ≠ 0 := by
    have h := (List.all_eq_true.mp D_ok) d hd
    simpa using h
  simp only [color]
  omega

/-- Adjacency form: two lattice points differing by a displacement in `D`
receive different colours. -/
theorem adjacent_colors_ne (u v : Int × Int) (d : Int × Int) (hd : d ∈ D)
    (h : u = (v.1 + d.1, v.2 + d.2)) : color u ≠ color v := by
  subst h
  exact color_shift_ne v.1 v.2 d hd

/-- Finite verification for the 3-colouring: no Euclidean displacement has
`dx + dy ≡ 0 (mod 3)`. -/
theorem Deuc_ok : Deuc.all (fun e => decide ((e.1 + e.2) % 3 ≠ 0)) = true := by
  decide

/-- Properness of the 3-colouring on the Euclidean reading. -/
theorem color3_shift_ne (x y : Int) (d : Int × Int) (hd : d ∈ Deuc) :
    color3 (x + d.1, y + d.2) ≠ color3 (x, y) := by
  have hne : (d.1 + d.2) % 3 ≠ 0 := by
    have h := (List.all_eq_true.mp Deuc_ok) d hd
    simpa using h
  simp only [color3]
  omega

/-- Boolean adjacency test on the union graph: `p = q`, or else the
displacement `q - p` belongs to `D`. -/
def pairAdj (p q : Int × Int) : Bool :=
  p == q || D.contains (q.1 - p.1, q.2 - p.2)

/-- The 5-clique `{(0,0), (±1,0), (0,±1)}` of the squared reading: all ten
pairwise differences have squared norm in {1,2,4}.  Hence chi >= 5 for the
squared reading (and for the union graph, which contains it). -/
def C5 : List (Int × Int) := [(0,0),(1,0),(-1,0),(0,1),(0,-1)]

/-- Clique certificate: every pair of points of `C5` is adjacent in the union
graph.  Verified by `decide`. -/
theorem C5_clique : C5.all (fun p => C5.all (fun q => pairAdj p q)) = true := by
  decide

/-- The 3-clique `{(0,0), (1,0), (2,0)}` of the Euclidean reading: the
pairwise differences have Euclidean lengths 1 and 2.  Hence chi >= 3 for the
Euclidean reading. -/
def C3 : List (Int × Int) := [(0,0),(1,0),(2,0)]

/-- Clique certificate for `C3`, verified by `decide`. -/
theorem C3_clique : C3.all (fun p => C3.all (fun q => pairAdj p q)) = true := by
  decide

end Tlmc1556
