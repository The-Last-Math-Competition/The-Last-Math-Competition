import Std
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace C5366

inductive Letter where
  | a | A | b | B
  deriving DecidableEq, Repr

open Letter
abbrev Word := List Letter

def dx : Letter → Int
  | a => 1 | A => -1 | b => 0 | B => 0

def dy : Letter → Int
  | a => 0 | A => 0 | b => 1 | B => -1

def evalX : Word → Int
  | [] => 0
  | c :: w => dx c + evalX w

def evalY : Word → Int
  | [] => 0
  | c :: w => dy c + evalY w

def eval (w : Word) : Int × Int := (evalX w, evalY w)

theorem eval_append (u v : Word) :
    eval (u ++ v) = (evalX u + evalX v, evalY u + evalY v) := by
  induction u with
  | nil => simp [eval, evalX, evalY]
  | cons c u ih =>
    have hx := congrArg Prod.fst ih
    have hy := congrArg Prod.snd ih
    simp only [eval] at hx hy
    simp [eval, evalX, evalY, hx, hy, Int.add_assoc]

/-- The chosen generators commute in the modeled group. -/
theorem generators_commute : eval [a, b] = eval [b, a] := by decide

def rank : Letter → Nat
  | a => 0 | A => 1 | b => 2 | B => 3

/-- Ordinary lexicographic comparison, for the order a < A < b < B. -/
def LexLE (u v : Word) : Prop := u = v ∨ List.Lex (fun c d => rank c < rank d) u v

/-- A shortest representative in the Cayley graph of Z² with the four standard letters. -/
def Geodesic (w : Word) : Prop := ∀ v, eval v = eval w → w.length ≤ v.length

/-- Lexicographically first among all shortest representatives of the same group element. -/
def Canonical (w : Word) : Prop :=
  Geodesic w ∧ ∀ v, eval v = eval w → v.length = w.length → LexLE w v

theorem evalX_le_length (w : Word) : evalX w ≤ (w.length : Int) := by
  induction w with
  | nil => simp [evalX]
  | cons c w ih => cases c <;> simp [evalX, dx] <;> omega

theorem evalX_eq_length_unique (w : Word) (h : evalX w = (w.length : Int)) :
    w = List.replicate w.length a := by
  induction w with
  | nil => rfl
  | cons c w ih =>
    have hb := evalX_le_length w
    cases c <;> simp only [evalX, dx, List.length_cons] at h
    · have he : evalX w = (w.length : Int) := by omega
      simpa [List.replicate_succ] using congrArg (List.cons a) (ih he)
    all_goals omega

theorem eval_replicate (n : Nat) : eval (List.replicate n a) = ((n : Int), 0) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hx := congrArg Prod.fst ih
    have hy := congrArg Prod.snd ih
    simp only [eval] at hx hy
    simp [List.replicate_succ, eval, evalX, evalY, dx, dy, hx, hy]
    omega

theorem unique_short_word (n : Nat) (v : Word)
    (he : eval v = ((n : Int), 0)) (hl : v.length ≤ n) :
    v = List.replicate n a := by
  have hx : evalX v = (n : Int) := congrArg Prod.fst he
  have hb := evalX_le_length v
  have hn : v.length = n := by omega
  have hu := evalX_eq_length_unique v (by omega)
  simpa [hn] using hu

theorem powers_are_canonical (n : Nat) : Canonical (List.replicate n a) := by
  constructor
  · intro v he
    rw [eval_replicate] at he
    have hx : evalX v = (n : Int) := congrArg Prod.fst he
    have hb := evalX_le_length v
    simp only [List.length_replicate]
    omega
  · intro v he hl
    rw [eval_replicate] at he
    simp only [List.length_replicate] at hl
    exact Or.inl (unique_short_word n v he (by omega)).symm

/-- Ordinary regular expressions: no complement or intersection operator. -/
inductive Regex where
  | empty | epsilon
  | letter (c : Letter)
  | union (r s : Regex)
  | concat (r s : Regex)
  | star (r : Regex)

/-- The usual finite concatenation closure, including the empty word. -/
inductive Kleene (L : Word → Prop) : Word → Prop where
  | nil : Kleene L []
  | append {u v} : L u → Kleene L v → Kleene L (u ++ v)

def accepts : Regex → Word → Prop
  | .empty, _ => False
  | .epsilon, w => w = []
  | .letter c, w => w = [c]
  | .union r s, w => accepts r w ∨ accepts s w
  | .concat r s, w => ∃ u v, w = u ++ v ∧ accepts r u ∧ accepts s v
  | .star r, w => Kleene (accepts r) w

def starHeight : Regex → Nat
  | .empty | .epsilon | .letter _ => 0
  | .union r s | .concat r s => max (starHeight r) (starHeight s)
  | .star r => starHeight r + 1

/-- A bound for the lengths of words accepted by any height-zero expression. -/
def lengthBound : Regex → Nat
  | .empty | .epsilon => 0
  | .letter _ => 1
  | .union r s => max (lengthBound r) (lengthBound s)
  | .concat r s => lengthBound r + lengthBound s
  | .star _ => 0

theorem zero_height_length_bound (r : Regex) (h : starHeight r = 0)
    (w : Word) (hw : accepts r w) : w.length ≤ lengthBound r := by
  induction r generalizing w with
  | empty => exact False.elim hw
  | epsilon => cases hw; simp [lengthBound]
  | letter c => cases hw; simp [lengthBound]
  | union r s ihr ihs =>
    have hr : starHeight r = 0 := by simp only [starHeight] at h; omega
    have hs : starHeight s = 0 := by simp only [starHeight] at h; omega
    cases hw with
    | inl hw => have := ihr hr w hw; simp only [lengthBound]; omega
    | inr hw => have := ihs hs w hw; simp only [lengthBound]; omega
  | concat r s ihr ihs =>
    have hr : starHeight r = 0 := by simp only [starHeight] at h; omega
    have hs : starHeight s = 0 := by simp only [starHeight] at h; omega
    obtain ⟨u, v, rfl, hu, hv⟩ := hw
    have := ihr hr u hu
    have := ihs hs v hv
    simp only [List.length_append, lengthBound]
    omega
  | star r ih => simp [starHeight] at h

/-- Height zero for a language means it is denoted by an ordinary expression of height zero. -/
def HasStarHeightZero (L : Word → Prop) : Prop :=
  ∃ r : Regex, starHeight r = 0 ∧ ∀ w, accepts r w ↔ L w

/-- The lexicographic geodesic language of this commuting four-letter group is not height zero. -/
theorem canonical_not_star_height_zero : ¬ HasStarHeightZero Canonical := by
  rintro ⟨r, hr, he⟩
  have hp := powers_are_canonical (lengthBound r + 1)
  have ha := (he _).mpr hp
  have hb := zero_height_length_bound r hr _ ha
  simp only [List.length_replicate] at hb
  omega

end C5366
