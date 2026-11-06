import Std

namespace TLMC8875
inductive Game where
| mk : List Game → List Game → Game
 deriving Repr

def leG : Game → Game → Bool
 | .mk gl gr, .mk hl hr => gl.attach.all (fun a => !leG (.mk hl hr) a.val) && hr.attach.all (fun b => !leG b.val (.mk gl gr))
termination_by g h => sizeOf g + sizeOf h
decreasing_by
 all_goals simp_wf
 all_goals first | (have := List.sizeOf_lt_of_mem a.property; omega) | (have := List.sizeOf_lt_of_mem b.property; omega)

def zero : Game := .mk [] []
def one : Game := .mk [zero] []
def half : Game := .mk [zero] [one]
def quarter : Game := .mk [zero] [half]
example : leG zero quarter = true ∧ leG quarter zero = false := by simp [zero, quarter, half, one, leG]

def isNumber : Game → Bool
 | .mk gl gr => gl.attach.all (fun a => isNumber a.val) &&
   gr.attach.all (fun b => isNumber b.val) &&
   gl.all (fun a => gr.all (fun b => leG a b && !leG b a))
termination_by g => sizeOf g
 decreasing_by
  all_goals simp_wf
  all_goals first | (have := List.sizeOf_lt_of_mem a.property; omega) | (have := List.sizeOf_lt_of_mem b.property; omega)

theorem quarter_is_number : isNumber quarter = true := by
 simp [quarter, half, one, zero, isNumber, leG]
-- Conway's simplest-number construction, enumerated by birthday.
def interpolate : List Rat → List Rat
 | [] => []
 | [a] => [a]
 | a :: b :: xs => a :: ((a+b)/2) :: interpolate (b::xs)
def numbersByDay : Nat → List Rat
 | 0 => [0]
 | n+1 => -(n+1 : Rat) :: (interpolate (numbersByDay n) ++ [(n+1 : Rat)])

def evalNumber : Nat → Game → Option Rat
 | 0, _ => none
 | n+1, .mk gl gr => do
   let ls ← gl.mapM (evalNumber n)
   let rs ← gr.mapM (evalNumber n)
   ((List.range (n+1)).flatMap numbersByDay).find? (fun q =>
     ls.all (fun l => l < q) && rs.all (fun r => q < r))

theorem eval_zero : evalNumber 1 zero = some 0 := by decide +kernel
theorem eval_one : evalNumber 2 one = some 1 := by decide +kernel
theorem eval_half : evalNumber 3 half = some (1/2) := by decide +kernel
theorem eval_quarter : evalNumber 4 quarter = some (1/4) := by decide +kernel

theorem no_earlier_number_between :
  ((List.range 3).flatMap numbersByDay).all (fun q => !(0 < q && q < 1/2)) = true := by decide +kernel

def quarterValue : Rat := 1/4
def HalfIntegral (q : Rat) : Prop := ∃ z : Int, 2*q = (z : Rat)
theorem quarter_not_halfIntegral : ¬HalfIntegral quarterValue := by
 intro ⟨z,h⟩
 have hd := congrArg Rat.den h
 have hden : (2 * quarterValue).den = 2 := by decide +kernel
 rw [hden, Rat.den_intCast] at hd
 have bad : (2 : Nat) = 1 := hd
 contradiction

-- Nimber *n has all earlier nimbers as both left and right options.
def nimber (n : Nat) : Game :=
  let opts := (List.range n).attach.map (fun i => nimber i.val)
  .mk opts opts
termination_by n
 decreasing_by
  have := List.mem_range.mp i.property
  omega

theorem nimber_zero : nimber 0 = zero := by
 rw [nimber]
 rfl

 theorem quarter_positive : leG zero quarter = true ∧ leG quarter zero = false := by
  simp [zero, quarter, half, one, leG]

theorem quarter_not_le_any_nimber (n : Nat) : leG quarter (nimber n) = false := by
  cases n with
  | zero => simp [nimber_zero, quarter, half, one, zero, leG]
  | succ n =>
    have hz : (0 : Nat) ∈ List.range (n+1) := by simp
    have hopt : zero ∈ (List.range (n+1)).attach.map (fun i => nimber i.val) := by
      apply List.mem_map.mpr
      refine ⟨⟨0,hz⟩, by simp, ?_⟩
      exact nimber_zero
    rw [nimber]
    simp only [quarter, leG]
    simp only [Bool.and_eq_false_iff]
    right
    rw [List.all_eq_false]
    refine ⟨⟨zero,hopt⟩, by simp, ?_⟩
    simp [leG,zero,half,one]
#print axioms quarter_not_le_any_nimber

def equivalent (g h : Game) : Prop := leG g h = true ∧ leG h g = true

theorem quarter_not_equivalent_nimber (n : Nat) : ¬equivalent quarter (nimber n) := by
 intro h
 have he := h.1
 rw [quarter_not_le_any_nimber] at he
 contradiction

def height : Game → Nat
 | .mk gl gr => 1 + ((gl.attach.map (fun g => height g.val) ++
   gr.attach.map (fun g => height g.val)).foldl Nat.max 0)
termination_by g => sizeOf g
 decreasing_by
  all_goals simp_wf
  all_goals have := List.sizeOf_lt_of_mem g.property
  all_goals omega

-- On number games, the ordinary (nonnegative-temperature) thermograph
-- is the constant vertical line at the value obtained by simplicity.
-- None indicates that no number has been certified by this finite evaluator.
abbrev PositiveTemperature := { t : Rat // 0 < t }

def numericRightWall (g : Game) (_t : PositiveTemperature) : Option Rat := evalNumber (height g) g

theorem quarter_numeric_wall (t : PositiveTemperature) : numericRightWall quarter t = some (1/4) := by
 have hb : height quarter = 4 := by simp [height, quarter, half, one, zero]
 unfold numericRightWall
 rw [hb]
 exact eval_quarter

def NumberMastHalfIntegral : Prop :=
 ∀ (g : Game) (q : Rat), isNumber g = true →
   (∀ t : PositiveTemperature, numericRightWall g t = some q) → HalfIntegral q

theorem disproof_number_mast_half_integrality : ¬ NumberMastHalfIntegral := by
 intro h
 apply quarter_not_halfIntegral
 exact h quarter quarterValue quarter_is_number (fun t => quarter_numeric_wall t)

def NumberMastHalfIntegralOutsideNimbers : Prop :=
 ∀ (g : Game) (q : Rat), isNumber g = true →
   (∀ n : Nat, ¬equivalent g (nimber n)) →
   (∀ t : PositiveTemperature, numericRightWall g t = some q) → HalfIntegral q

theorem disproof_even_with_nimber_exception : ¬ NumberMastHalfIntegralOutsideNimbers := by
 intro h
 apply quarter_not_halfIntegral
 exact h quarter quarterValue quarter_is_number quarter_not_equivalent_nimber
   (fun t => quarter_numeric_wall t)
#print axioms disproof_even_with_nimber_exception

#print axioms quarter_not_equivalent_nimber
#print axioms quarter_numeric_wall
#print axioms disproof_number_mast_half_integrality

end TLMC8875
