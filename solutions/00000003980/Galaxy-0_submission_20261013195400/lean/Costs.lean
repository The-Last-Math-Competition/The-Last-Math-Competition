import Main
namespace TLMC3980

theorem vars_le_size (f : Formula) : f.vars ≤ f.size := by
  induction f with
  | atom k => simp [Formula.vars, Formula.size]
  | bottom => decide
  | imp a b ha hb => simp only [Formula.vars, Formula.size]; omega

-- Instrumented list lookup: every inspected cell is charged one step.
def lookupMeter : List Bool → Nat → Bool × Nat
  | [], _ => (false, 1)
  | b :: _, 0 => (b, 1)
  | _ :: xs, n + 1 => let r := lookupMeter xs n; (r.1, r.2 + 1)

theorem lookupMeter_value (v : List Bool) (k : Nat) :
    (lookupMeter v k).1 = v[k]?.getD false := by
  induction v generalizing k with
  | nil => simp [lookupMeter]
  | cons b xs ih => cases k <;> simp [lookupMeter, ih]

theorem lookupMeter_steps (v : List Bool) (k : Nat) :
    (lookupMeter v k).2 ≤ k + 1 := by
  induction v generalizing k with
  | nil => simp [lookupMeter]
  | cons b xs ih =>
    cases k with
    | zero => simp [lookupMeter]
    | succ k => simp only [lookupMeter]; have := ih k; omega

-- Eager evaluation counts both implication subtrees, giving a safe upper
-- bound even for short-circuit execution.
def evalMeter (v : List Bool) : Formula → Bool × Nat
  | .atom k => lookupMeter v k
  | .bottom => (false, 1)
  | .imp a b =>
    let ra := evalMeter v a
    let rb := evalMeter v b
    (!(ra.1) || rb.1, ra.2 + rb.2 + 1)

theorem evalMeter_value (v : List Bool) (f : Formula) :
    (evalMeter v f).1 = f.eval v := by
  induction f with
  | atom k => exact lookupMeter_value v k
  | bottom => rfl
  | imp a b ha hb => simp [evalMeter, Formula.eval, ha, hb]

theorem evalMeter_steps (v : List Bool) (f : Formula) :
    (evalMeter v f).2 ≤ f.size := by
  induction f with
  | atom k => have := lookupMeter_steps v k; simp only [evalMeter, Formula.size]; omega
  | bottom => simp [evalMeter, Formula.size]
  | imp a b ha hb => simp only [evalMeter, Formula.size]; omega

def evalTableMeter (f : Formula) : List (List Bool) → Bool × Nat
  | [] => (true, 1)
  | v :: vs =>
    let r := evalMeter v f
    let t := evalTableMeter f vs
    (r.1 && t.1, r.2 + t.2 + 1)

theorem evalTableMeter_value (f : Formula) (vs : List (List Bool)) :
    (evalTableMeter f vs).1 = vs.all (fun v => f.eval v) := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp [evalTableMeter, evalMeter_value, ih]

theorem evalTableMeter_steps (f : Formula) (vs : List (List Bool)) :
    (evalTableMeter f vs).2 ≤ (f.size + 1) * vs.length + 1 := by
  induction vs with
  | nil => simp [evalTableMeter]
  | cons v vs ih =>
    have hv := evalMeter_steps v f
    simp only [evalTableMeter, List.length_cons, Nat.mul_add, Nat.mul_one]
    omega

-- A specified shared-output construction model charges each previous row
-- for two extensions and two output-list cells. Actual flatMap temporary
-- allocations are not counted exactly; they add a constant factor.
-- This meter is not the allocation count of compiled Lean code.
def assignmentsMeter : Nat → List (List Bool) × Nat
  | 0 => ([[]], 1)
  | n + 1 =>
    let r := assignmentsMeter n
    (r.1.flatMap (fun v => [false :: v, true :: v]), r.2 + 4 * r.1.length + 1)

theorem assignmentsMeter_value (n : Nat) : (assignmentsMeter n).1 = assignments n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [assignmentsMeter, assignments, ih]

theorem pow_two_pos (n : Nat) : 1 ≤ 2 ^ n := by
  induction n with
  | zero => decide
  | succ n ih => simp only [Nat.pow_succ]; omega

theorem assignmentsMeter_steps (n : Nat) : (assignmentsMeter n).2 ≤ 6 * 2 ^ n := by
  induction n with
  | zero => decide
  | succ n ih =>
    have hp := pow_two_pos n
    simp only [assignmentsMeter, assignmentsMeter_value, assignments_length, Nat.pow_succ]
    omega

-- Repeated binary doubling to form 2^n: at stage n the current binary
-- representation has n+1 bits. This counts the bit-copy work, not a
-- constant-cost oracle for exponentially large integers.
def doublingWork : Nat → Nat
  | 0 => 1
  | n + 1 => doublingWork n + n + 2

theorem doublingWork_bound (n : Nat) : doublingWork n ≤ (n + 1) * (n + 1) := by
  induction n with
  | zero => decide
  | succ n ih =>
    simp only [doublingWork, Nat.add_mul, Nat.mul_add, Nat.one_mul,
      Nat.mul_one] at *
    omega

def tableVolume (vs : List (List Bool)) : Nat :=
  (vs.map (fun row => row.length + 1)).sum

theorem table_length_le_volume (vs : List (List Bool)) : vs.length ≤ tableVolume vs := by
  induction vs with
  | nil => decide
  | cons v vs ih => simp only [tableVolume, List.map_cons, List.sum_cons,
      List.length_cons] at *; omega

theorem proof_component_bounds (p : Proof) :
    p.cert.formula.vars ≤ proofLength p ∧
    p.cert.formula.size ≤ proofLength p ∧
    p.cert.table.length ≤ proofLength p := by
  have hv := vars_le_size p.cert.formula
  have ht := table_length_le_volume p.cert.table
  simp only [proofLength, tableVolume] at *
  omega

-- A guard-dependent work budget assembled from the explicit algorithms
-- above. The first square allows syntax traversal and integer comparisons;
-- row comparison may traverse the generated rows and the input rows.
-- This is an algorithmic upper-bound certificate, not a formal Turing
-- machine running-time definition. The bit-model implementation bridge
-- is stated separately in the report.
def checkerWorkBudget (p : Proof) : Nat :=
  let s := p.cert.formula.size
  let n := p.cert.formula.vars
  let N := proofLength p
  (s + 1) * (s + 1) + doublingWork n + N +
    if p.cert.table.length = 2 ^ n then
      (assignmentsMeter n).2 + (n + 1) * 2 ^ n + N +
        (evalTableMeter p.cert.formula p.cert.table).2
    else 0

theorem checkerWorkBudget_polynomial (p : Proof) :
    checkerWorkBudget p ≤ 13 * (proofLength p + 1) * (proofLength p + 1) := by
  obtain ⟨hn, hs, ht⟩ := proof_component_bounds p
  let N := proofLength p
  have sqS := Nat.mul_le_mul (Nat.add_le_add_right hs 1) (Nat.add_le_add_right hs 1)
  have sqN := Nat.mul_le_mul (Nat.add_le_add_right hn 1) (Nat.add_le_add_right hn 1)
  have hd := doublingWork_bound p.cert.formula.vars
  have hbase : N ≤ (N + 1) * (N + 1) := by
    have h := Nat.le_mul_of_pos_left (N + 1) (Nat.zero_lt_succ N)
    simp only [Nat.succ_eq_add_one] at h
    omega
  unfold checkerWorkBudget
  dsimp only
  split
  next hg =>
    have ha := assignmentsMeter_steps p.cert.formula.vars
    have he := evalTableMeter_steps p.cert.formula p.cert.table
    have hp : 2 ^ p.cert.formula.vars ≤ N := by omega
    have hmul := Nat.mul_le_mul (Nat.add_le_add_right hn 1) (Nat.le_trans hp (Nat.le_add_right N 1))
    have heMul := Nat.mul_le_mul (Nat.add_le_add_right hs 1) (Nat.le_trans ht (Nat.le_add_right N 1))
    change _ ≤ 13 * (N + 1) * (N + 1)
    rw [Nat.mul_assoc]
    dsimp [N] at *
    have hpos : 1 ≤ (proofLength p + 1) * (proofLength p + 1) := Nat.mul_pos (Nat.zero_lt_succ _) (Nat.zero_lt_succ _)
    omega
  next =>
    change _ ≤ 13 * (N + 1) * (N + 1)
    rw [Nat.mul_assoc]
    dsimp [N] at *
    have hpos : 1 ≤ (proofLength p + 1) * (proofLength p + 1) := Nat.mul_pos (Nat.zero_lt_succ _) (Nat.zero_lt_succ _)
    omega

#print axioms checkerWorkBudget_polynomial
end TLMC3980
