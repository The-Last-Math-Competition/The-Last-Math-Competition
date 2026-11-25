/-
  SpernerFD/SmallN.lean
  Exact Sperner numbers and central corrections for small generator counts
  (`n = 0, 1, 2, 3, 4`) in both `FD(n)` and `FD_0(n)`, using verified
  antichain and chain-decomposition certificates (zero `native_decide`).
-/

import SpernerFD.Antichain

namespace SpernerFD

/-! ## 1. Exact Sperner Numbers for `n = 0, 1, 2` -/

theorem spernerFD_zero : spernerFD 0 = 1 := by decide
theorem spernerFD_one : spernerFD 1 = 1 := by decide
theorem spernerFD_two : spernerFD 2 = 2 := by decide

theorem spernerFD0_zero : spernerFD0 0 = 0 := by decide

theorem spernerFD0_one : spernerFD0 1 = 1 := by
  rw [spernerFD0_eq_spernerFD (by decide), spernerFD_one]

theorem spernerFD0_two : spernerFD0 2 = 2 := by
  rw [spernerFD0_eq_spernerFD (by decide), spernerFD_two]

/-! ## 2. Bitmask Decoder and Chain-Cover Certificates for `n = 3` and `n = 4` -/

/-- Binary index `0 .. 2^n - 1` of a vertex `x : Cube n`. -/
def cubeIndex : {n : Nat} → Cube n → Nat
  | 0, _ => 0
  | _ + 1, x => (if headCube x then 1 else 0) + 2 * cubeIndex (tailCube x)

/-- Boolean truth-table function on `Cube n` decoded from a `2^n`-bit natural number `mask`. -/
def funcOfMask (n : Nat) (mask : Nat) (x : Cube n) : Bool :=
  mask.testBit (cubeIndex x)

/-- Safe lift of a bitmask to `FD n` (falling back to `botFD n` if non-monotone). -/
def fdOfMask (n : Nat) (mask : Nat) : FD n :=
  if h : IsMonotone (funcOfMask n mask) then ⟨funcOfMask n mask, h⟩ else botFD n

/-- Explicit rank-4 antichain of size `4` in `FD 3`:
    the three generators `x_1, x_2, x_3` together with the 3-variable majority function. -/
def antichainFD3 : List (FD 3) :=
  [170, 204, 232, 240].map (fdOfMask 3)

/-- Explicit 4-chain partition covering all 20 elements of `FD 3`. -/
def chainsFD3 : List (List (FD 3)) :=
  [[0, 128, 136, 168, 170, 234, 238, 255],
   [160, 224, 232, 248, 254],
   [192, 200, 204, 236, 252],
   [240, 250]].map (fun C => C.map (fdOfMask 3))

theorem spernerFD_three : spernerFD 3 = 4 := by
  have hA : IsAntichain FDLe antichainFD3 := by decide
  have hchains : ∀ C ∈ chainsFD3, IsChain FDLe C := by decide
  have hcover : ∀ f ∈ allFD 3, ∃ C ∈ chainsFD3, f ∈ C := by decide
  have hlen : antichainFD3.length = chainsFD3.length := rfl
  have heq := spernerNumber_eq_of_antichain_and_chains
    (noDup_allFD 3) mem_allFD hA hchains hcover hlen
  exact heq

theorem spernerFD0_three : spernerFD0 3 = 4 := by
  rw [spernerFD0_eq_spernerFD (by decide), spernerFD_three]

/-- Explicit rank-8 antichain of size `24` in `FD 4`. -/
def antichainFD4 : List (FD 4) :=
  [43690, 52428, 59624, 60072, 60104, 60128, 60584, 60616,
   60640, 61064, 61088, 61120, 61680, 63656, 63688, 63712,
   64136, 64160, 64192, 64648, 64672, 64704, 65152, 65280].map (fdOfMask 4)

theorem spernerFD_four_ge_twenty_four : 24 ≤ spernerFD 4 := by
  have hA : IsAntichain FDLe antichainFD4 := by decide
  have hle := antichain_le_spernerFD hA
  exact hle

theorem spernerFD0_four_ge_twenty_four : 24 ≤ spernerFD0 4 := by
  rw [spernerFD0_eq_spernerFD (by decide)]
  exact spernerFD_four_ge_twenty_four

/-! ## 3. Exact Signed Central Corrections for `n = 0, 1, 2, 3` -/

theorem spernerCorrectionFD_zero : spernerCorrectionFD 0 = 0 := by
  simp [spernerCorrectionFD, spernerFD_zero, centralBinom, binom]

theorem spernerCorrectionFD_one : spernerCorrectionFD 1 = 0 := by
  simp [spernerCorrectionFD, spernerFD_one, centralBinom, binom]

theorem spernerCorrectionFD_two : spernerCorrectionFD 2 = 0 := by
  simp [spernerCorrectionFD, spernerFD_two, centralBinom, binom]

theorem spernerCorrectionFD_three : spernerCorrectionFD 3 = 1 := by
  simp [spernerCorrectionFD, spernerFD_three, centralBinom, binom]

theorem spernerCorrectionFD0_zero : spernerCorrectionFD0 0 = -1 := by
  simp [spernerCorrectionFD0, spernerFD0_zero, centralBinom, binom]

theorem spernerCorrectionFD0_one : spernerCorrectionFD0 1 = 0 := by
  simp [spernerCorrectionFD0, spernerFD0_one, centralBinom, binom]

theorem spernerCorrectionFD0_two : spernerCorrectionFD0 2 = 0 := by
  simp [spernerCorrectionFD0, spernerFD0_two, centralBinom, binom]

theorem spernerCorrectionFD0_three : spernerCorrectionFD0 3 = 1 := by
  simp [spernerCorrectionFD0, spernerFD0_three, centralBinom, binom]

end SpernerFD
