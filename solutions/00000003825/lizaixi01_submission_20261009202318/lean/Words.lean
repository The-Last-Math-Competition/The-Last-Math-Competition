import Tensor

namespace FixedAlphabetA1
open A1Crystal

def letter : A1Crystal Bool where
  wt b := if b then -1 else 1
  eps b := if b then 1 else 0
  phi b := if b then 0 else 1
  e b := if b then some false else none
  f b := if b then none else some true
  balance b := by cases b <;> decide
  inverse x y := by cases x <;> cases y <;> decide
  e_none b := by cases b <;> decide
  f_none b := by cases b <;> decide
  f_eps x y h := by cases x <;> cases y <;> simp_all
  f_phi x y h := by cases x <;> cases y <;> simp_all
  f_wt x y h := by cases x <;> cases y <;> simp_all

def empty : A1Crystal Unit where
  wt _ := 0
  eps _ := 0
  phi _ := 0
  e _ := none
  f _ := none
  balance _ := rfl
  inverse _ _ := by simp
  e_none _ := by simp
  f_none _ := by simp
  f_eps _ _ h := by cases h
  f_phi _ _ h := by cases h
  f_wt _ _ h := by cases h

def Word : ℕ → Type
  | 0 => Unit
  | n+1 => Bool × Word n

def wordCrystal : (n : ℕ) → A1Crystal (Word n)
  | 0 => empty
  | n+1 => letter.tensor (wordCrystal n)

def toList : (n : ℕ) → Word n → List Bool
  | 0, _ => []
  | n+1, (b,w) => b :: toList n w

def encode : List Bool → Sigma Word
  | [] => ⟨0,()⟩
  | b::l => let p := encode l; ⟨p.1+1,(b,p.2)⟩

def decode (p : Sigma Word) : List Bool := toList p.1 p.2

theorem decode_encode (l : List Bool) : decode (encode l) = l := by
  induction l with
  | nil => rfl
  | cons b l ih => simpa [encode,decode,toList] using congrArg (b :: ·) ih

theorem encode_decode (p : Sigma Word) : encode (decode p) = p := by
  rcases p with ⟨n,w⟩
  induction n with
  | zero => cases w; rfl
  | succ n ih =>
    rcases w with ⟨b,w⟩
    have h := ih w
    change (let p := encode (toList n w); ⟨p.1+1,(b,p.2)⟩ : Sigma Word) = ⟨n+1,(b,w)⟩
    change encode (toList n w) = ⟨n,w⟩ at h
    rw [h]

def wordsEquiv : Sigma Word ≃ List Bool where
  toFun := decode
  invFun := encode
  left_inv := encode_decode
  right_inv := decode_encode

def sigmaCrystal : A1Crystal (Sigma Word) where
  wt p := (wordCrystal p.1).wt p.2
  eps p := (wordCrystal p.1).eps p.2
  phi p := (wordCrystal p.1).phi p.2
  e p := ((wordCrystal p.1).e p.2).map (Sigma.mk p.1)
  f p := ((wordCrystal p.1).f p.2).map (Sigma.mk p.1)
  balance p := (wordCrystal p.1).balance p.2
  inverse p q := by
    constructor
    · intro h
      rcases p with ⟨n,x⟩
      rcases Option.map_eq_some_iff.mp h with ⟨y,hy,rfl⟩
      exact Option.map_eq_some_iff.mpr ⟨x,((wordCrystal n).inverse x y).mp hy,rfl⟩
    · intro h
      rcases q with ⟨n,y⟩
      rcases Option.map_eq_some_iff.mp h with ⟨x,hx,rfl⟩
      exact Option.map_eq_some_iff.mpr ⟨y,((wordCrystal n).inverse x y).mpr hx,rfl⟩
  e_none p := by simp only [Option.map_eq_none_iff, (wordCrystal p.1).e_none]
  f_none p := by simp only [Option.map_eq_none_iff, (wordCrystal p.1).f_none]
  f_eps p q h := by
    rcases p with ⟨n,x⟩
    rcases Option.map_eq_some_iff.mp h with ⟨y,hy,rfl⟩
    exact (wordCrystal n).f_eps x y hy
  f_phi p q h := by
    rcases p with ⟨n,x⟩
    rcases Option.map_eq_some_iff.mp h with ⟨y,hy,rfl⟩
    exact (wordCrystal n).f_phi x y hy
  f_wt p q h := by
    rcases p with ⟨n,x⟩
    rcases Option.map_eq_some_iff.mp h with ⟨y,hy,rfl⟩
    exact (wordCrystal n).f_wt x y hy

def A1Crystal.transport {V W : Type} (A : A1Crystal V) (h : V ≃ W) : A1Crystal W where
  wt x := A.wt (h.symm x)
  eps x := A.eps (h.symm x)
  phi x := A.phi (h.symm x)
  e x := (A.e (h.symm x)).map h
  f x := (A.f (h.symm x)).map h
  balance x := A.balance (h.symm x)
  inverse x y := by
    have hm (z : Option V) (w : W) : z.map h = some w ↔ z=some (h.symm w) := by
      constructor
      · intro hz
        rcases Option.map_eq_some_iff.mp hz with ⟨v,hv,he⟩
        simpa only [←he,h.symm_apply_apply] using hv
      · intro hz
        simp [hz]
    rw [hm,hm,A.inverse]
  e_none x := by simp only [Option.map_eq_none_iff,A.e_none]
  f_none x := by simp only [Option.map_eq_none_iff,A.f_none]
  f_eps x y hf := by
    rcases Option.map_eq_some_iff.mp hf with ⟨v,hv,rfl⟩
    simpa using A.f_eps (h.symm x) v hv
  f_phi x y hf := by
    rcases Option.map_eq_some_iff.mp hf with ⟨v,hv,rfl⟩
    simpa using A.f_phi (h.symm x) v hv
  f_wt x y hf := by
    rcases Option.map_eq_some_iff.mp hf with ⟨v,hv,rfl⟩
    simpa using A.f_wt (h.symm x) v hv

/-- The actual crystal on the one fixed free alphabet monoid List Bool. -/
def monoidCrystal : A1Crystal (List Bool) := sigmaCrystal.transport wordsEquiv

theorem monoid_nil : monoidCrystal.eps [] = 0 ∧ monoidCrystal.phi [] = 0 ∧
    monoidCrystal.e [] = none ∧ monoidCrystal.f [] = none ∧ monoidCrystal.wt [] = 0 := by
  decide

theorem monoid_cons_eps (b : Bool) (l : List Bool) :
    monoidCrystal.eps (b::l) = monoidCrystal.eps l + (letter.eps b - monoidCrystal.phi l) := by
  rfl
theorem monoid_cons_phi (b : Bool) (l : List Bool) :
    monoidCrystal.phi (b::l) = letter.phi b + (monoidCrystal.phi l-letter.eps b) := by
  rfl
theorem monoid_cons_wt (b : Bool) (l : List Bool) :
    monoidCrystal.wt (b::l) = letter.wt b + monoidCrystal.wt l := by rfl

theorem monoid_cons_e (b : Bool) (l : List Bool) :
    monoidCrystal.e (b::l) =
    if monoidCrystal.phi l < letter.eps b then (letter.e b).map (·::l)
    else (monoidCrystal.e l).map (b::·) := by
  unfold monoidCrystal A1Crystal.transport sigmaCrystal
  simp only [wordsEquiv,Equiv.coe_fn_mk,Equiv.symm_mk,encode,wordCrystal,A1Crystal.tensor,
    A1Crystal.te,Prod.fst,Prod.snd]
  split
  · rename_i hc
    have hl : toList (encode l).1 (encode l).2 = l := decode_encode l
    cases h : letter.e b with
    | none => simp only [hc,if_pos]; rfl
    | some a =>
      simp only [hc,if_pos]
      change some (a :: toList (encode l).1 (encode l).2) = some (a::l)
      rw [hl]
  · rename_i hc
    cases h : (wordCrystal (encode l).1).e (encode l).2 <;>
      simp only [hc,if_false] <;> rfl

theorem monoid_cons_f (b : Bool) (l : List Bool) :
    monoidCrystal.f (b::l) =
    if monoidCrystal.phi l ≤ letter.eps b then (letter.f b).map (·::l)
    else (monoidCrystal.f l).map (b::·) := by
  unfold monoidCrystal A1Crystal.transport sigmaCrystal
  simp only [wordsEquiv,Equiv.coe_fn_mk,Equiv.symm_mk,encode,wordCrystal,A1Crystal.tensor,
    A1Crystal.tf,Prod.fst,Prod.snd]
  split
  · rename_i hc
    have hl : toList (encode l).1 (encode l).2 = l := decode_encode l
    cases h : letter.f b with
    | none => simp only [hc,if_pos]; rfl
    | some a =>
      simp only [hc,if_pos]
      change some (a :: toList (encode l).1 (encode l).2) = some (a::l)
      rw [hl]
  · rename_i hc
    cases h : (wordCrystal (encode l).1).f (encode l).2 <;>
      simp only [hc,if_false] <;> rfl

end FixedAlphabetA1
