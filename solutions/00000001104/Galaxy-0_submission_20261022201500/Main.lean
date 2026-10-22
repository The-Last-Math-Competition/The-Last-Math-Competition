import Std
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace KL1104
abbrev PermId := Fin 120
abbrev Poly := List Int
-- All permutations of 0,...,4, in lexicographic order.
def permTable : Array (List Nat) := #[
[0,1,2,3,4],
[0,1,2,4,3],
[0,1,3,2,4],
[0,1,3,4,2],
[0,1,4,2,3],
[0,1,4,3,2],
[0,2,1,3,4],
[0,2,1,4,3],
[0,2,3,1,4],
[0,2,3,4,1],
[0,2,4,1,3],
[0,2,4,3,1],
[0,3,1,2,4],
[0,3,1,4,2],
[0,3,2,1,4],
[0,3,2,4,1],
[0,3,4,1,2],
[0,3,4,2,1],
[0,4,1,2,3],
[0,4,1,3,2],
[0,4,2,1,3],
[0,4,2,3,1],
[0,4,3,1,2],
[0,4,3,2,1],
[1,0,2,3,4],
[1,0,2,4,3],
[1,0,3,2,4],
[1,0,3,4,2],
[1,0,4,2,3],
[1,0,4,3,2],
[1,2,0,3,4],
[1,2,0,4,3],
[1,2,3,0,4],
[1,2,3,4,0],
[1,2,4,0,3],
[1,2,4,3,0],
[1,3,0,2,4],
[1,3,0,4,2],
[1,3,2,0,4],
[1,3,2,4,0],
[1,3,4,0,2],
[1,3,4,2,0],
[1,4,0,2,3],
[1,4,0,3,2],
[1,4,2,0,3],
[1,4,2,3,0],
[1,4,3,0,2],
[1,4,3,2,0],
[2,0,1,3,4],
[2,0,1,4,3],
[2,0,3,1,4],
[2,0,3,4,1],
[2,0,4,1,3],
[2,0,4,3,1],
[2,1,0,3,4],
[2,1,0,4,3],
[2,1,3,0,4],
[2,1,3,4,0],
[2,1,4,0,3],
[2,1,4,3,0],
[2,3,0,1,4],
[2,3,0,4,1],
[2,3,1,0,4],
[2,3,1,4,0],
[2,3,4,0,1],
[2,3,4,1,0],
[2,4,0,1,3],
[2,4,0,3,1],
[2,4,1,0,3],
[2,4,1,3,0],
[2,4,3,0,1],
[2,4,3,1,0],
[3,0,1,2,4],
[3,0,1,4,2],
[3,0,2,1,4],
[3,0,2,4,1],
[3,0,4,1,2],
[3,0,4,2,1],
[3,1,0,2,4],
[3,1,0,4,2],
[3,1,2,0,4],
[3,1,2,4,0],
[3,1,4,0,2],
[3,1,4,2,0],
[3,2,0,1,4],
[3,2,0,4,1],
[3,2,1,0,4],
[3,2,1,4,0],
[3,2,4,0,1],
[3,2,4,1,0],
[3,4,0,1,2],
[3,4,0,2,1],
[3,4,1,0,2],
[3,4,1,2,0],
[3,4,2,0,1],
[3,4,2,1,0],
[4,0,1,2,3],
[4,0,1,3,2],
[4,0,2,1,3],
[4,0,2,3,1],
[4,0,3,1,2],
[4,0,3,2,1],
[4,1,0,2,3],
[4,1,0,3,2],
[4,1,2,0,3],
[4,1,2,3,0],
[4,1,3,0,2],
[4,1,3,2,0],
[4,2,0,1,3],
[4,2,0,3,1],
[4,2,1,0,3],
[4,2,1,3,0],
[4,2,3,0,1],
[4,2,3,1,0],
[4,3,0,1,2],
[4,3,0,2,1],
[4,3,1,0,2],
[4,3,1,2,0],
[4,3,2,0,1],
[4,3,2,1,0]]
def perm (w : PermId) : List Nat := permTable[w.val]!
def entry (w : PermId) (i : Nat) : Nat := (perm w).getD i 0
def len (w : PermId) : Nat := ((List.range 5).map fun i =>
  ((List.range 5).filter fun j => i < j && entry w j < entry w i).length).sum
def bruhat (x w : PermId) : Bool := (List.range 6).all fun i =>
  (List.range 5).all fun j =>
    ((perm x).take i |>.filter fun a => j ≤ a).length ≤
    ((perm w).take i |>.filter fun a => j ≤ a).length
-- Right multiplication by the simple reflection (i,i+1).
def swapList (p : List Nat) (i : Nat) : List Nat :=
  (List.range 5).map fun j => p.getD (if j=i then i+1 else if j=i+1 then i else j) 0
def swap (w : PermId) (i : Nat) : PermId :=
  ⟨(permTable.toList.findIdx fun p => p == swapList (perm w) i) % 120, Nat.mod_lt _ (by decide)⟩
def descent (w : PermId) : Nat := (List.range 4).findIdx fun i => entry w (i+1) < entry w i

theorem table_permutations : ∀ w : PermId, (perm w).length = 5 ∧ (perm w).Nodup ∧ (perm w).all (· < 5) = true := by decide
theorem table_size : permTable.size = 120 := by decide
theorem table_no_duplicates : permTable.toList.Nodup := by decide
theorem swap_correct : ∀ w : PermId, ∀ i : Fin 4,
  perm (swap w i.val) = swapList (perm w) i.val := by decide
theorem descend_lt : ∀ w : PermId, 0 < len w → len (swap w (descent w)) < len w := by decide

theorem descent_in_range : ∀ w : PermId, 0 < len w → descent w < 4 := by decide
def padd : Poly → Poly → Poly
  | [], b => b
  | a, [] => a
  | a::as, b::bs => (a+b)::padd as bs
def pneg (p : Poly) : Poly := p.map (- ·)
def pscale (a : Int) (p : Poly) : Poly := p.map (a*·)
def shift (n : Nat) (p : Poly) : Poly := List.replicate n 0 ++ p
def coeff (p : Poly) (n : Nat) : Int := p.getD n 0
-- One step of the standard right-descent KL recursion.
def step (F : PermId → PermId → Poly) (x w : PermId) : Poly :=
  if len w = 0 then (if x=w then [1] else [])
  else if !(bruhat x w) then []
  else if x=w then [1]
  else
    let s := descent w
    let v := swap w s
    let c := if len (swap x s) < len x then 1 else 0
    let first := padd (shift (1-c) (F (swap x s) v)) (shift c (F x v))
    let correction := ((List.finRange 120).map fun z =>
      if len z < len w then
        if len z < len v && bruhat x z && bruhat z v &&
          len (swap z s) < len z && (len v-len z)%2=1 then
          pscale (coeff (F z v) ((len v-len z-1)/2))
            (shift ((len w-len z)/2) (F x z))
        else []
      else []).foldl padd []
    padd first (pneg correction)
theorem congr2 {α β γ : Type} (f : α → β → γ) {a a' : α} {b b' : β}
    (h : a = a') (k : b = b') : f a b = f a' b' := by rw [h, k]
theorem step_congr (F G : PermId → PermId → Poly) (x w : PermId)
    (hFG : ∀ a b, len b < len w → F a b = G a b) :
    step F x w = step G x w := by
  unfold step
  split
  · rfl
  · rename_i h0
    split
    · rfl
    · split
      · rfl
      · have hv := descend_lt w (Nat.pos_of_ne_zero h0)
        apply congr2 padd
        · apply congr2 padd
          · exact congrArg (shift _) (hFG _ _ hv)
          · exact congrArg (shift _) (hFG _ _ hv)
        · apply congrArg pneg
          apply congrArg (fun xs : List Poly => xs.foldl padd [])
          apply List.map_congr_left
          intro z _
          split
          · rename_i hz
            split
            · apply congr2 pscale
              · exact congrArg (fun p => coeff p _) (hFG _ _ hv)
              · exact congrArg (shift _) (hFG _ _ hz)
            · rfl
          · rfl

def fuel : Nat → PermId → PermId → Poly
  | 0, x, w => if x=w then [1] else []
  | n+1, x, w => step (fuel n) x w
theorem fuel_next (n : Nat) : ∀ x w, len w ≤ n → fuel (n+1) x w = fuel n x w := by
  induction n with
  | zero =>
    intro x w hw
    have h0 : len w = 0 := Nat.eq_zero_of_le_zero hw
    simp [fuel, step, h0]
  | succ n ih =>
    intro x w hw
    apply step_congr
    intro a b hb
    apply ih
    omega
-- The height equals the actual Coxeter length, not an empirical cutoff.
def kl (x w : PermId) : Poly := fuel (len w) x w

theorem fuel_add (n m : Nat) (x w : PermId) (h : len w ≤ n) :
    fuel (n+m) x w = fuel n x w := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Nat.add_succ, fuel_next (n+m) x w (by omega), ih]
theorem fuel_above (n : Nat) (x w : PermId) (h : len w ≤ n) :
    fuel n x w = kl x w := by
  have hn : n = len w + (n-len w) := by omega
  rw [hn, fuel_add]
  · rfl
  · exact Nat.le_refl _
theorem kl_recurrence (x w : PermId) : kl x w = step kl x w := by
  by_cases h0 : len w = 0
  · simp [kl, fuel, step, h0]
  · let n := len w - 1
    have hn : len w = n+1 := by dsimp [n]; omega
    calc
      kl x w = step (fuel n) x w := by unfold kl; rw [hn, fuel]
      _ = step kl x w := by
        apply step_congr
        intro a b hb
        exact fuel_above n a b (by omega)

theorem recurrence_unique (F : PermId → PermId → Poly)
    (hF : ∀ x w, F x w = step F x w) : ∀ x w, F x w = kl x w := by
  intro x w
  generalize hn : len w = n
  induction n using Nat.strongRecOn generalizing x w with
  | ind n ih =>
    rw [hF, kl_recurrence]
    apply step_congr
    intro a b hb
    exact ih (len b) (by omega) a b rfl

def e : PermId := ⟨0,by decide⟩
def w : PermId := ⟨64,by decide⟩
theorem witness_permutation : perm w = [2,3,4,0,1] := by decide
theorem witness_length : len w = 6 := by decide
theorem computed_polynomial : kl e w = [1,2,0] := by decide
def monic (p : Poly) : Prop := ((p.reverse.dropWhile (· == 0)).headD 0) = 1
theorem not_monic : ¬ monic (kl e w) := by
  rw [computed_polynomial]
  unfold monic
  decide
theorem ordinary_counterexample : ¬ (∀ x w, monic (kl x w)) := by
  intro h
  exact not_monic (h e w)
theorem recurrence_counterexample (F : PermId → PermId → Poly)
    (hF : ∀ x w, F x w = step F x w) : ¬ (∀ x w, monic (F x w)) := by
  intro h
  have hw := h e w
  rw [recurrence_unique F hF e w] at hw
  exact not_monic hw
#print axioms recurrence_counterexample
#print axioms recurrence_unique
#print axioms kl_recurrence
#print axioms computed_polynomial
#print axioms ordinary_counterexample
end KL1104
