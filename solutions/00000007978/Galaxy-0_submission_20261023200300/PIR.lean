import Std
set_option autoImplicit false
set_option maxRecDepth 10000
namespace PIR

def shrink (v pivot : Nat) : Nat := if v < pivot then v else v - 1

theorem shrink_inj (x y pivot : Nat) (hx : x ≠ pivot) (hy : y ≠ pivot)
    (h : shrink x pivot = shrink y pivot) : x = y := by
  unfold shrink at h
  split at h <;> split at h <;> omega

theorem fin_injection_bound {m n : Nat} (f : Fin m → Fin n)
    (hf : ∀ a b, f a = f b → a = b) : m ≤ n := by
  induction m generalizing n with
  | zero => omega
  | succ m ih =>
    cases n with
    | zero => exact Fin.elim0 (f ⟨0, by omega⟩)
    | succ n =>
      let last : Fin (m+1) := ⟨m, by omega⟩
      let pivot := (f last).val
      have hne (a : Fin m) : (f a.castSucc).val ≠ pivot := by
        intro he
        have heq : f a.castSucc = f last := Fin.ext he
        have hab := hf a.castSucc last heq
        have hv := congrArg Fin.val hab
        have ha := a.isLt
        simp only [Fin.val_castSucc] at hv
        change a.val = m at hv
        omega
      let g : Fin m → Fin n := fun a => ⟨shrink (f a.castSucc).val pivot, by
        have ha := (f a.castSucc).isLt
        have hp : pivot < n+1 := (f last).isLt
        have hh := hne a
        unfold shrink
        split <;> omega⟩
      have hg : ∀ a b, g a = g b → a = b := by
        intro a b h
        have hval := congrArg Fin.val h
        have he : (f a.castSucc).val = (f b.castSucc).val :=
          shrink_inj _ _ _ (hne a) (hne b) hval
        have hab := hf a.castSucc b.castSucc (Fin.ext he)
        have hv := congrArg (fun z : Fin (m+1) => z.val) hab
        exact Fin.ext hv
      have hi := ih g hg
      omega

-- A database has three independent messages, each with alphabet size B.
def Database (B : Nat) := Fin B × Fin B × Fin B

def item {B : Nat} (x : Database B) (i : Fin 3) : Fin B :=
  if i.val = 0 then x.1 else if i.val = 1 then x.2.1 else x.2.2

theorem item_ext {B : Nat} (x y : Database B)
    (h : ∀ i, item x i = item y i) : x = y := by
  have h0 := h ⟨0, by decide⟩
  have h1 := h ⟨1, by decide⟩
  have h2 := h ⟨2, by decide⟩
  simp [item] at h0 h1 h2
  exact Prod.ext h0 (Prod.ext h1 h2)

-- Queries may be randomized; privacy needs only identical query supports.
structure Scheme (B D : Nat) (Seed Query : Type) where
  query : Fin 3 → Seed → Query
  answer : Query → Database B → Fin D
  decode : Fin 3 → Seed → Fin D → Fin B
  correct : ∀ i r x, decode i r (answer (query i r) x) = item x i
  privateSupport : ∀ i j r, ∃ s, query j s = query i r

theorem fixed_query_injective {B D : Nat} {Seed Query : Type}
    (p : Scheme B D Seed Query) (r : Seed) :
    ∀ x y, p.answer (p.query ⟨0, by decide⟩ r) x =
      p.answer (p.query ⟨0, by decide⟩ r) y → x = y := by
  intro x y heq
  apply item_ext
  intro i
  obtain ⟨s, hs⟩ := p.privateSupport ⟨0, by decide⟩ i r
  have hx := p.correct i s x
  have hy := p.correct i s y
  rw [hs] at hx hy
  rw [← hx, ← hy, heq]

-- An injection enumerating all triples, with no counting oracle.
def unpack (B : Nat) (hB : 0 < B) (z : Fin (B * (B * B))) : Database B :=
  (⟨z.val % B, Nat.mod_lt _ hB⟩,
   ⟨(z.val / B) % B, Nat.mod_lt _ hB⟩,
   ⟨(z.val / B) / B, by
      apply (Nat.div_lt_iff_lt_mul hB).mpr
      apply (Nat.div_lt_iff_lt_mul hB).mpr
      simp [Nat.mul_comm] at *⟩)

theorem unpack_injective (B : Nat) (hB : 0 < B) :
    ∀ x y, unpack B hB x = unpack B hB y → x = y := by
  intro x y h
  have h0 := congrArg (fun z : Database B => z.1.val) h
  have h1 := congrArg (fun z : Database B => z.2.1.val) h
  have h2 := congrArg (fun z : Database B => z.2.2.val) h
  change x.val % B = y.val % B at h0
  change x.val / B % B = y.val / B % B at h1
  change x.val / B / B = y.val / B / B at h2
  have hd : x.val / B = y.val / B := by
    calc
      x.val / B = x.val / B % B + B * (x.val / B / B) := (Nat.mod_add_div _ _).symm
      _ = y.val / B % B + B * (y.val / B / B) := by rw [h1,h2]
      _ = y.val / B := Nat.mod_add_div _ _
  apply Fin.ext
  calc
    x.val = x.val % B + B * (x.val / B) := (Nat.mod_add_div _ _).symm
    _ = y.val % B + B * (y.val / B) := by rw [h0,hd]
    _ = y.val := Nat.mod_add_div _ _

theorem answer_alphabet_bound {B D : Nat} {Seed Query : Type}
    (hB : 0 < B) (p : Scheme B D Seed Query) (r : Seed) : B * (B * B) ≤ D := by
  apply fin_injection_bound (fun x => p.answer (p.query ⟨0, by decide⟩ r) (unpack B hB x))
  intro x y h
  exact unpack_injective B hB x y (fixed_query_injective p r _ _ h)

theorem digit_bound (B x y : Nat) (hx : x < B) (hy : y < B) :
    x + B*y < B*B := by
  have h := Nat.mul_le_mul_left B (show y+1 ≤ B by omega)
  rw [Nat.mul_add, Nat.mul_one] at h
  omega

def pack {B : Nat} (x : Database B) : Fin (B*(B*B)) :=
  ⟨x.1.val+B*(x.2.1.val+B*x.2.2.val), by
    have hinner := digit_bound B x.2.1.val x.2.2.val x.2.1.isLt x.2.2.isLt
    have h := Nat.mul_le_mul_left B (show x.2.1.val+B*x.2.2.val+1 ≤ B*B by omega)
    rw [Nat.mul_add, Nat.mul_one] at h
    have h0 := x.1.isLt
    omega⟩

theorem unpack_pack {B : Nat} (hB : 0 < B) (x : Database B) :
    unpack B hB (pack x) = x := by
  apply Prod.ext
  · apply Fin.ext
    simp [unpack,pack,Nat.mod_eq_of_lt x.1.isLt]
  · apply Prod.ext
    · apply Fin.ext
      simp [unpack,pack,Nat.add_mul_div_left _ _ hB,
        Nat.div_eq_of_lt x.1.isLt,Nat.mod_eq_of_lt x.2.1.isLt]
    · apply Fin.ext
      simp [unpack,pack,Nat.add_mul_div_left _ _ hB,
        Nat.div_eq_of_lt x.1.isLt,Nat.div_eq_of_lt x.2.1.isLt]

def downloadAll (B : Nat) (hB : 0 < B) : Scheme B (B*(B*B)) Unit Unit where
  query := fun _ _ => ()
  answer := fun _ x => pack x
  decode := fun i _ a => item (unpack B hB a) i
  correct := by intro i r x; rw [unpack_pack]
  privateSupport := by intro i j r; exact ⟨(),rfl⟩

theorem exact_single_server_alphabet (B : Nat) (hB : 0 < B) :
    (Nonempty (Scheme B (B*(B*B)) Unit Unit)) ∧
    (∀ (D : Nat) (Seed Query : Type) (_p : Scheme B D Seed Query) (_r : Seed), B*(B*B) ≤ D) := by
  constructor
  · exact ⟨downloadAll B hB⟩
  · intro D Seed Query p r
    exact answer_alphabet_bound hB p r

end PIR
