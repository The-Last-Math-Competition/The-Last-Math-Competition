import Std

/-!
# Disproof of conjecture 00000001096
(VC dimension of degree-≤ `d` polynomials over `F_q`)

We work over `F_5` with `n = 2`, `d = 2` (so `d < q`).  The six monomials
`1, x, y, x², xy, y²` span a 6-dimensional space of functions on `F_5²`.
We exhibit six points whose 6×6 evaluation matrix is invertible mod 5
(determinant ≡ 1), hence the six points are shattered in the natural
generalised (`F_q`-valued) VC sense: every labelling by `F_5` is realised.
The conjecture predicts `n·d = 4`, strictly less than 6.

Everything is done with core Lean + `Std` only (no Mathlib).  Since `ZMod`
is part of Mathlib, all arithmetic is carried out on `Nat` residues mod 5.
-/

namespace Tlmc1096

/-- x-coordinates of the six points `p₀,…,p₅`. -/
def px : Fin 6 → Nat
  | 0 => 0 | 1 => 0 | 2 => 0 | 3 => 1 | 4 => 1 | 5 => 2

/-- y-coordinates of the six points `p₀,…,p₅`. -/
def py : Fin 6 → Nat
  | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 1 | 5 => 0

/-- Exponents `(x-exp, y-exp)` of the six monomials `1,x,y,x²,xy,y²`. -/
def monoExp : Fin 6 → Nat × Nat
  | 0 => (0, 0)   -- 1
  | 1 => (1, 0)   -- x
  | 2 => (0, 1)   -- y
  | 3 => (2, 0)   -- x²
  | 4 => (1, 1)   -- xy
  | 5 => (0, 2)   -- y²

/-- Monomial `j` evaluated at `(x,y)`, reduced mod 5. -/
def monoMod (j : Fin 6) (x y : Nat) : Nat :=
  (x ^ (monoExp j).1 * y ^ (monoExp j).2) % 5

/-- The 6×6 evaluation matrix mod 5: entry `(i,j)` = monomial `j` at point `i`. -/
def evalM (i j : Fin 6) : Nat := monoMod j (px i) (py i)

/-- Evaluation of the coefficient vector `c` at point `i` (a linear form), mod 5. -/
def evalAt (c : Fin 6 → Nat) (i : Fin 6) : Nat :=
  (evalM i 0 * c 0 + evalM i 1 * c 1 + evalM i 2 * c 2
   + evalM i 3 * c 3 + evalM i 4 * c 4 + evalM i 5 * c 5) % 5

/-! ### The determinant via the Leibniz formula (enumerated as lists) -/

/-- Insert `x` at every position of `l`. -/
def insertEverywhere {α : Type} (x : α) : List α → List (List α)
  | [] => [[x]]
  | y :: ys => (x :: y :: ys) :: ((insertEverywhere x ys).map (fun l => y :: l))

/-- All permutations of a list (as lists). -/
def perms {α : Type} : List α → List (List α)
  | [] => [[]]
  | x :: xs => (perms xs).flatMap (insertEverywhere x)

/-- The 720 permutations of `Fin 6`, each as a list of length 6. -/
def permLists : List (List (Fin 6)) := perms (List.finRange 6)

/-- Number of inversions of a permutation list. -/
def inversionsL (l : List (Fin 6)) : Nat :=
  ((List.finRange 6).zip l).foldl
    (fun acc (p : Fin 6 × Fin 6) =>
      acc + (((List.finRange 6).zip l).foldl
        (fun acc2 (q : Fin 6 × Fin 6) =>
          if p.1 < q.1 && q.2 < p.2 then acc2 + 1 else acc2) 0)) 0

/-- Sign of a permutation list, encoded mod 5: `1` if even, `4` (= `-1`) if odd. -/
def permSignL (l : List (Fin 6)) : Nat :=
  if inversionsL l % 2 = 0 then 1 else 4

/-- Product of the matrix entries selected by the permutation list, mod 5. -/
def prodOf (l : List (Fin 6)) : Nat :=
  ((List.finRange 6).zip l).foldl
    (fun acc (p : Fin 6 × Fin 6) => (acc * evalM p.1 p.2) % 5) 1

/-- Determinant of the evaluation matrix mod 5 (Leibniz formula over all
permutations of `Fin 6`), reduced mod 5. -/
def detMod5 : Nat :=
  (permLists.foldl
     (fun acc l => (acc + (permSignL l * prodOf l) % 5) % 5) 0) % 5

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000 in
/-- The determinant is congruent to `1` mod 5, so the matrix is invertible. -/
theorem det_is_one : detMod5 = 1 := by decide

/-! ### Explicit coefficient realiser (the inverse matrix mod 5) -/

/-- Reduce a natural number into `Fin 5`. -/
def f5 (n : Nat) : Fin 5 := ⟨n % 5, Nat.mod_lt _ (by decide)⟩

/-- Build a function `Fin 6 → Fin 5` from its six values. -/
def mkFun5 (a0 a1 a2 a3 a4 a5 : Fin 5) : Fin 6 → Fin 5 :=
  fun j => if j = 0 then a0 else if j = 1 then a1 else if j = 2 then a2
           else if j = 3 then a3 else if j = 4 then a4 else a5

/-- `mkFun5` recovers a function from its six components. -/
theorem mkFun5_eta (y : Fin 6 → Fin 5) :
    mkFun5 (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) = y := by
  funext j
  simp only [mkFun5]
  split <;> rename_i h0
  · subst h0; rfl
  split <;> rename_i h1
  · subst h1; rfl
  split <;> rename_i h2
  · subst h2; rfl
  split <;> rename_i h3
  · subst h3; rfl
  split <;> rename_i h4
  · subst h4; rfl
  · have hv : j.val = 5 := by omega
    have hj : j = (5 : Fin 6) := Fin.ext hv
    subst hj; rfl

/-- Coefficient vector realising an arbitrary labelling `y`, obtained from the
inverse of the evaluation matrix mod 5:
`c = (y₀, y₀+2y₃+2y₅, y₀+2y₁+2y₂, 3y₀+4y₃+3y₅, y₀+4y₁+4y₃+y₄, 3y₀+4y₁+3y₂)`. -/
def solveFun (y : Fin 6 → Fin 5) : Fin 6 → Fin 5 :=
  fun j =>
    let y0 := (y 0).val; let y1 := (y 1).val; let y2 := (y 2).val
    let y3 := (y 3).val; let y4 := (y 4).val; let y5 := (y 5).val
    if j = 0 then f5 y0
    else if j = 1 then f5 (y0 + 2*y3 + 2*y5)
    else if j = 2 then f5 (y0 + 2*y1 + 2*y2)
    else if j = 3 then f5 (3*y0 + 4*y3 + 3*y5)
    else if j = 4 then f5 (y0 + 4*y1 + 4*y3 + y4)
    else f5 (3*y0 + 4*y1 + 3*y2)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 8000000 in
/-- Finite check of shattering (all `5^6 = 15625` labellings, component-wise):
for every labelling `(a₀,…,a₅)` and every point `i`, the explicit coefficient
vector `solveFun` realises the label at `i`. -/
theorem shatters_components :
    ∀ a0 a1 a2 a3 a4 a5 : Fin 5, ∀ i : Fin 6,
      evalAt (fun j => (solveFun (mkFun5 a0 a1 a2 a3 a4 a5) j).val) i
        = (mkFun5 a0 a1 a2 a3 a4 a5 i).val := by decide

/-- Every labelling `y : Fin 6 → Fin 5` is realised by `solveFun y`. -/
theorem shatters_six (y : Fin 6 → Fin 5) (i : Fin 6) :
    evalAt (fun j => (solveFun y j).val) i = (y i).val := by
  rw [← mkFun5_eta y]
  exact shatters_components _ _ _ _ _ _ i

/-- Generalised (`F_5`-valued) shattering: the evaluation map on the six chosen
points is surjective onto `F_5^6` — all `5^6` labellings are realisable. -/
theorem eval_map_bijective :
    ∀ y : Fin 6 → Fin 5, ∃ c : Fin 6 → Fin 5,
      ∀ i : Fin 6, evalAt (fun j => (c j).val) i = (y i).val :=
  fun y => ⟨solveFun y, shatters_six y⟩

/-- `n·d = 2·2 = 4` is strictly less than the six shattered points. -/
theorem vc_at_least_six : 4 < 6 := by decide

/-- Assembled disproof of conjecture 00000001096: the determinant of the
evaluation matrix is a unit mod 5, six points are shattered (all `5^6`
labellings realisable), and `n·d = 4 < 6` shattered points. -/
theorem conjecture_00000001096_false :
    detMod5 = 1 ∧
    (∀ y : Fin 6 → Fin 5, ∃ c : Fin 6 → Fin 5,
      ∀ i : Fin 6, evalAt (fun j => (c j).val) i = (y i).val) ∧
    4 < 6 :=
  ⟨det_is_one, eval_map_bijective, vc_at_least_six⟩

end Tlmc1096
