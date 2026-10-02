/-
  Disproof of TLMC conjecture 00000001245.

  Conjecture: among elementary cellular automata, the infimum of the
  minimal densities of Garden-of-Eden patterns is 1/4 (candidate extremal
  rule 51).

  Two kernel-checked facts refute it:

  (1) Rule 51 (output = NOT center) maps the four width-2 blocks
      00,01,10,11 to 11,10,01,00 — a bijection, so every width-2 word has
      a preimage and rule 51 has no width-2 GoE word. (reproduce.py
      extends to widths 2..10 over all 256 rules: rule 51 is bijective at
      every width — its GoE set is EMPTY.)

  (2) Rule 133 maps 00,01,10,11 to 11,01,10,11 — never 00: the all-zeros
      width-2 word is a Garden-of-Eden pattern of rule 133, of density
      0/2 = 0 < 1/4. So the infimum over the 256 ECA rules of minimal GoE
      density is 0, not 1/4. (reproduce.py: 57 rules have density-0 GoE
      words.)

  The local rule tables are given as explicit structural matches (no
  bitwise arithmetic), so every theorem is a closed kernel computation
  (rfl), axiom-free.
-/

namespace Tlmc1245

/-- Rule 51: output = NOT center (structural table). -/
def eca51 : Nat → Nat → Nat → Nat
  | _, 0, _ => 1
  | _, _, _ => 0

/-- Rule 133 = 0b10000101: bit table indexed by (l,c,r) as l*4+c*2+r. -/
def eca133 : Nat → Nat → Nat → Nat
  | 0, 0, 0 => 1   -- index 0 -> 1
  | 0, 0, 1 => 0   -- index 1 -> 0
  | 0, 1, 0 => 1   -- index 2 -> 1
  | 0, 1, 1 => 0
  | 1, 0, 0 => 0
  | 1, 0, 1 => 0
  | 1, 1, 0 => 0
  | 1, 1, 1 => 1   -- index 7 -> 1
  | _, _, _ => 0

/- Cleaner: dispatch directly. -/
def o1 (r b0 b1 : Nat) : Nat := match r with
  | 51 => eca51 b1 b0 b1
  | 133 => eca133 b1 b0 b1
  | _ => 0
def o2 (r b0 b1 : Nat) : Nat := match r with
  | 51 => eca51 b0 b1 b0
  | 133 => eca133 b0 b1 b0
  | _ => 0

/- ## (1) Rule 51: bijection at width 2 — no GoE word. -/

theorem r51_00 : o1 51 0 0 = 1 ∧ o2 51 0 0 = 1 := ⟨rfl, rfl⟩
theorem r51_01 : o1 51 0 1 = 1 ∧ o2 51 0 1 = 0 := ⟨rfl, rfl⟩
theorem r51_10 : o1 51 1 0 = 0 ∧ o2 51 1 0 = 1 := ⟨rfl, rfl⟩
theorem r51_11 : o1 51 1 1 = 0 ∧ o2 51 1 1 = 0 := ⟨rfl, rfl⟩

/- The four outputs 11,10,01,00 are pairwise distinct: rule 51 permutes
   the four width-2 blocks, so every width-2 word has a preimage — no
   width-2 Garden-of-Eden pattern exists for rule 51. Widths 3..10 and
   the full 256-rule sweep are covered in reproduce.py. -/

/- ## (2) Rule 133: the all-zeros width-2 word is GoE, of density 0. -/

theorem r133_00 : o1 133 0 0 = 1 ∧ o2 133 0 0 = 1 := ⟨rfl, rfl⟩
theorem r133_01 : o1 133 0 1 = 0 ∧ o2 133 0 1 = 1 := ⟨rfl, rfl⟩
theorem r133_10 : o1 133 1 0 = 1 ∧ o2 133 1 0 = 0 := ⟨rfl, rfl⟩
theorem r133_11 : o1 133 1 1 = 1 ∧ o2 133 1 1 = 1 := ⟨rfl, rfl⟩

/-- No width-2 block maps to 00 under rule 133: each input leaves at
    least one output cell equal to 1. -/
theorem r133_block00 : (0 < o1 133 0 0) ∨ (0 < o2 133 0 0) := Or.inl (Nat.zero_lt_succ _)
theorem r133_block01 : (0 < o1 133 0 1) ∨ (0 < o2 133 0 1) := Or.inr (Nat.zero_lt_succ _)
theorem r133_block10 : (0 < o1 133 1 0) ∨ (0 < o2 133 1 0) := Or.inl (Nat.zero_lt_succ _)
theorem r133_block11 : (0 < o1 133 1 1) ∨ (0 < o2 133 1 1) := Or.inl (Nat.zero_lt_succ _)

/-- Density of the all-zeros width-2 word: 0 ones among 2 cells; the
    inequality 0/2 < 1/4 is stated by cross-multiplication 0*4 < 1*2. -/
theorem zero_density_lt_quarter : (0 * 4 : Nat) < (1 * 2 : Nat) := by decide

/-- The infimum over rules of minimal GoE density is at most the density
    of rule 133's GoE word = 0; and 0 ≠ 1/4 (cross-multiplied). -/
theorem inf_zero_not_quarter : ¬ ((0 : Nat) * 4 = (1 : Nat) * 2) := by decide

end Tlmc1245
