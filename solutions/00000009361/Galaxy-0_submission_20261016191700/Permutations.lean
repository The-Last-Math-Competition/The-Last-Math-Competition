import Std
namespace Records9361
set_option autoImplicit false

def rise (r x : Nat) : Nat := if x < r then x else x + 1
def drop (r x : Nat) : Nat := if x < r then x else x - 1

theorem drop_rise (r x : Nat) : drop r (rise r x) = x := by
  simp only [rise, drop]
  split <;> (try split) <;> omega

theorem rise_drop (r x : Nat) (h : x ≠ r) : rise r (drop r x) = x := by
  simp only [rise, drop]
  split <;> (try split) <;> omega

theorem rise_strict (r x y : Nat) : rise r x < rise r y ↔ x < y := by
  simp only [rise]
  split <;> (try split) <;> omega

theorem rise_inj (r x y : Nat) : rise r x = rise r y ↔ x = y := by
  constructor
  · intro h
    have := congrArg (drop r) h
    simpa only [drop_rise] using this
  · intro h; subst y; rfl

theorem rise_ne (r x : Nat) : rise r x ≠ r := by
  simp only [rise]; split <;> omega

theorem rise_bound (n r x : Nat) (hx : x < n) (_hr : r ≤ n) : rise r x < n+1 := by
  simp only [rise]; split <;> omega

theorem drop_bound (n r x : Nat) (hx : x < n+1) (hr : r ≤ n) (hne : x ≠ r) : drop r x < n := by
  simp only [drop]; split <;> omega

theorem map_drop_rise (r : Nat) (p : List Nat) : (p.map (rise r)).map (drop r) = p := by
  simp [List.map_map, Function.comp_def, drop_rise]

theorem map_rise_drop (r : Nat) (p : List Nat) (h : r ∉ p) :
    (p.map (drop r)).map (rise r) = p := by
  calc
    (p.map (drop r)).map (rise r) = p.map id := by
      rw [List.map_map]
      exact List.map_congr_left (fun x hx => rise_drop r x (fun e => h (e ▸ hx)))
    _ = p := List.map_id' p

-- An exact finite-set characterization of ordinary permutations.
def Valid (n : Nat) (p : List Nat) : Prop :=
  p.Nodup ∧ ∀ x, x ∈ p ↔ x < n

theorem valid_iff_perm (n : Nat) (p : List Nat) : Valid n p ↔ p.Perm (List.range n) := by
  constructor
  · intro h
    apply List.perm_iff_count.mpr
    intro x
    rw [h.1.count, List.nodup_range.count]
    simp [h.2 x]
  · intro h
    refine ⟨h.nodup_iff.mpr List.nodup_range, ?_⟩
    intro x
    simpa using h.mem_iff

theorem nodup_map_injective {α β : Type} (f : α → β) (inj : ∀ x y, f x = f y → x = y)
    (p : List α) (h : p.Nodup) : (p.map f).Nodup := by
  exact List.pairwise_map.mpr (h.imp (fun hne heq => hne (inj _ _ heq)))

theorem valid_extend (n r : Nat) (p : List Nat) (hr : r ≤ n) (hp : Valid n p) :
    Valid (n+1) (r :: p.map (rise r)) := by
  constructor
  · rw [List.nodup_cons]
    constructor
    · intro h
      obtain ⟨x, _, hx⟩ := List.mem_map.mp h
      exact rise_ne r x hx
    · exact nodup_map_injective (rise r) (fun x y => (rise_inj r x y).mp) p hp.1
  · intro x
    constructor
    · intro hx
      rcases List.mem_cons.mp hx with hx | hx
      · omega
      · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
        exact rise_bound n r y ((hp.2 y).mp hy) hr
    · intro hx
      by_cases he : x = r
      · simp [he]
      · apply List.mem_cons_of_mem
        apply List.mem_map.mpr
        exact ⟨drop r x, (hp.2 _).mpr (drop_bound n r x hx hr he), rise_drop r x he⟩

theorem valid_remove (n r : Nat) (p : List Nat) (hp : Valid (n+1) (r::p)) :
    r ≤ n ∧ Valid n (p.map (drop r)) := by
  have hn : r ∉ p := (List.nodup_cons.mp hp.1).1
  have hr : r ≤ n := by have := (hp.2 r).mp (by simp); omega
  refine ⟨hr, ?_, ?_⟩
  · apply List.pairwise_map.mpr
    apply ((List.nodup_cons.mp hp.1).2).imp_of_mem
    intro x y hx hy hxy he
    have hx' : x ≠ r := fun e => hn (e ▸ hx)
    have hy' : y ≠ r := fun e => hn (e ▸ hy)
    have := congrArg (rise r) he
    rw [rise_drop r x hx', rise_drop r y hy'] at this
    exact hxy this
  · intro x
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      exact drop_bound n r y ((hp.2 y).mp (by simp [hy])) hr (fun e => hn (e ▸ hy))
    · intro hx
      apply List.mem_map.mpr
      refine ⟨rise r x, ?_, drop_rise r x⟩
      have hm := (hp.2 (rise r x)).mpr (rise_bound n r x hx hr)
      rcases List.mem_cons.mp hm with he | he
      · exact False.elim (rise_ne r x he)
      · exact he

def perms : Nat → List (List Nat)
  | 0 => [[]]
  | n+1 => (List.range (n+1)).flatMap fun r => (perms n).map fun p => r :: p.map (rise r)

theorem perms_valid (n : Nat) (p : List Nat) : p ∈ perms n ↔ Valid n p := by
  induction n generalizing p with
  | zero =>
    constructor
    · intro h; simp [perms] at h; subst p; simp [Valid]
    · intro h
      have : p = [] := List.eq_nil_iff_forall_not_mem.mpr (by intro x hx; have := (h.2 x).mp hx; omega)
      simp [perms, this]
  | succ n ih =>
    constructor
    · intro h
      obtain ⟨r, hr, h⟩ := List.mem_flatMap.mp h
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
      exact valid_extend n r p (by simp only [List.mem_range] at hr; omega) ((ih p).mp hp)
    · intro hp
      cases p with
      | nil => have := (hp.2 0).mpr (by omega); simp at this
      | cons r p =>
        obtain ⟨hr,hq⟩ := valid_remove n r p hp
        apply List.mem_flatMap.mpr
        refine ⟨r, by simp only [List.mem_range]; omega, ?_⟩
        apply List.mem_map.mpr
        refine ⟨p.map (drop r), (ih _).mpr hq, ?_⟩
        rw [map_rise_drop r p (List.nodup_cons.mp hp.1).1]

theorem perms_complete (n : Nat) (p : List Nat) : p ∈ perms n ↔ p.Perm (List.range n) :=
  (perms_valid n p).trans (valid_iff_perm n p)

theorem nodup_flatMap_disjoint {α β : Type} (f : α → List β) (l : List α)
    (hn : l.Nodup) (hf : ∀ a ∈ l, (f a).Nodup)
    (hd : ∀ a ∈ l, ∀ b ∈ l, a ≠ b → ∀ x ∈ f a, x ∉ f b) :
    (l.flatMap f).Nodup := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.flatMap_cons, List.nodup_append]
    have hnl := List.nodup_cons.mp hn
    refine ⟨hf a (by simp), ih hnl.2 (fun b hb => hf b (by simp [hb]))
      (fun b hb c hc => hd b (by simp [hb]) c (by simp [hc])), ?_⟩
    intro x hx y hy he
    subst y
    obtain ⟨b,hb,hxb⟩ := List.mem_flatMap.mp hy
    exact hd a (by simp) b (by simp [hb]) (fun e => hnl.1 (e ▸ hb)) x hx hxb

theorem perms_nodup (n : Nat) : (perms n).Nodup := by
  induction n with
  | zero => simp [perms]
  | succ n ih =>
    apply nodup_flatMap_disjoint _ _ List.nodup_range
    · intro r _
      apply nodup_map_injective _ _ _ ih
      intro p q he
      have hm := (List.cons.inj he).2
      have := congrArg (List.map (drop r)) hm
      simpa only [map_drop_rise] using this
    · intro r hr s hs hrs x hx hxs
      obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hx
      obtain ⟨q,hq,he⟩ := List.mem_map.mp hxs
      exact hrs (List.cons.inj he).1.symm

def factorial : Nat → Nat
  | 0 => 1
  | n+1 => (n+1) * factorial n

theorem sum_const {α : Type} (l : List α) (k : Nat) : (l.map (fun _ => k)).sum = l.length * k := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, Nat.add_mul, Nat.add_comm]

theorem perms_length (n : Nat) : (perms n).length = factorial n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [perms, List.length_flatMap, List.length_map]
    rw [sum_const, List.length_range, ih]
    rfl

end Records9361
