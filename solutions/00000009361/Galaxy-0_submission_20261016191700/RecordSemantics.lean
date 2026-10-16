import Permutations
namespace Records9361
set_option autoImplicit false

-- Tail entries precede the head in time: this is reverse chronological storage.
def recs : List Nat → List Bool
  | [] => []
  | r::p => (p.all (fun x => x < r)) :: recs p

-- Independent left-to-right definition. The earlier contains all earlier entries.
def scanRecords (earlier : List Nat) : List Nat → List Bool
  | [] => []
  | r::p => (earlier.all (fun x => x < r)) :: scanRecords (earlier ++ [r]) p

def chronologicalRecords (p : List Nat) : List Bool := scanRecords [] p

theorem scanRecords_append (earlier p q : List Nat) :
    scanRecords earlier (p ++ q) = scanRecords earlier p ++ scanRecords (earlier ++ p) q := by
  induction p generalizing earlier with
  | nil => simp [scanRecords]
  | cons a p ih => simp [scanRecords, ih, List.append_assoc]

theorem recs_chronological (p : List Nat) :
    recs p = (chronologicalRecords p.reverse).reverse := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    simp [recs, chronologicalRecords, List.reverse_cons, scanRecords_append,
      scanRecords, List.all_reverse, ih, chronologicalRecords]

theorem recs_length (p : List Nat) : (recs p).length = p.length := by
  induction p with
  | nil => rfl
  | cons a p ih => simp [recs, ih]

theorem recs_map_strict (f : Nat → Nat) (hf : ∀ x y, f x < f y ↔ x < y)
    (p : List Nat) : recs (p.map f) = recs p := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    simp only [List.map_cons, recs, ih, List.cons.injEq, and_true]
    simp only [List.all_map]
    apply congrArg (fun g => p.all g)
    funext x
    simp [hf]

theorem rise_record (n r : Nat) (p : List Nat) (hr : r ≤ n) (hp : p.Perm (List.range n)) :
    (p.map (rise r)).all (fun x => x < r) = (r == n) := by
  have hv := (valid_iff_perm n p).mpr hp
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true, List.mem_map, beq_iff_eq]
  constructor
  · intro h
    by_cases he : r = n
    · exact he
    have hrn : r < n := by omega
    have hmem : r ∈ p := (hv.2 r).mpr hrn
    have := h (rise r r) ⟨r,hmem,rfl⟩
    simp [rise] at this
    omega
  · intro he
    subst r
    intro x hx
    obtain ⟨y,hy,rfl⟩ := hx
    have hy' := (hv.2 y).mp hy
    simp [rise, hy']

theorem recs_extend (n r : Nat) (p : List Nat) (hr : r ≤ n) (hp : p.Perm (List.range n)) :
    recs (r :: p.map (rise r)) = (r == n) :: recs p := by
  simp only [recs, rise_record n r p hr hp, recs_map_strict (rise r) (rise_strict r)]


def chronologicalPerms (n : Nat) : List (List Nat) := (perms n).map List.reverse

theorem chronologicalPerms_complete (n : Nat) (p : List Nat) :
    p ∈ chronologicalPerms n ↔ p.Perm (List.range n) := by
  constructor
  · intro h
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp h
    exact (List.reverse_perm q).trans ((perms_complete n q).mp hq)
  · intro hp
    apply List.mem_map.mpr
    refine ⟨p.reverse, (perms_complete n p.reverse).mpr ((List.reverse_perm p).trans hp), ?_⟩
    exact List.reverse_reverse p

theorem chronologicalPerms_nodup (n : Nat) : (chronologicalPerms n).Nodup :=
  nodup_map_injective List.reverse (fun _ _ => List.reverse_inj.mp) (perms n) (perms_nodup n)

theorem chronologicalPerms_length (n : Nat) : (chronologicalPerms n).length = factorial n := by
  simp only [chronologicalPerms, List.length_map, perms_length]

theorem chronologicalRecords_reverse (p : List Nat) :
    chronologicalRecords p.reverse = (recs p).reverse := by
  have h := congrArg List.reverse (recs_chronological p)
  simpa only [List.reverse_reverse] using h.symm

end Records9361
