import Sums
namespace TLMC8872

def toggle (n : Nat) : Nat := if n % 2 = 0 then n+1 else n-1

theorem toggle_even (k : Nat) : toggle (2*k) = 2*k+1 := by
  simp [toggle]

theorem toggle_odd (k : Nat) : toggle (2*k+1) = 2*k := by
  simp [toggle]

theorem toggle_involutive (n : Nat) : toggle (toggle n) = n := by
  unfold toggle
  split <;> split <;> omega

theorem toggle_lt_even (k n : Nat) : toggle n < 2*k ↔ n < 2*k := by
  unfold toggle
  split <;> omega

theorem toggle_range_any (k : Nat) (p : Nat → Bool) :
    ((List.range (2*k)).any fun n => p (toggle n)) =
    (List.range (2*k)).any p := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, List.mem_range]
  constructor
  · rintro ⟨n, hn, hp⟩
    exact ⟨toggle n, (toggle_lt_even k n).mpr hn, hp⟩
  · rintro ⟨n, hn, hp⟩
    exact ⟨toggle n, (toggle_lt_even k n).mpr hn, by simpa [toggle_involutive] using hp⟩

theorem toggle_range_any_odd (k : Nat) (p : Nat → Bool) :
    ((List.range (2*k+1)).any fun n => p (toggle n)) =
    ((List.range (2*k)).any p || p (2*k+1)) := by
  rw [List.range_succ, List.any_append]
  simp [toggle_range_any, toggle_even]

end TLMC8872
