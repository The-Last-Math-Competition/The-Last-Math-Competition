import Base
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace TLMC1043
theorem cert3_0 : ∀ b c : F, NotAffine (strip [0,b,c] witness) := by unfold NotAffine; decide
theorem cert4_0 : ∀ b c d : F, NotAffine (strip [0,b,c,d] witness) := by unfold NotAffine; decide
theorem cert3_1 : ∀ b c : F, NotAffine (strip [1,b,c] witness) := by unfold NotAffine; decide
theorem cert4_1 : ∀ b c d : F, NotAffine (strip [1,b,c,d] witness) := by unfold NotAffine; decide
theorem cert3_2 : ∀ b c : F, NotAffine (strip [2,b,c] witness) := by unfold NotAffine; decide
theorem cert4_2 : ∀ b c d : F, NotAffine (strip [2,b,c,d] witness) := by unfold NotAffine; decide
theorem cert3_3 : ∀ b c : F, NotAffine (strip [3,b,c] witness) := by unfold NotAffine; decide
theorem cert4_3 : ∀ b c d : F, NotAffine (strip [3,b,c,d] witness) := by unfold NotAffine; decide
theorem cert3_4 : ∀ b c : F, NotAffine (strip [4,b,c] witness) := by unfold NotAffine; decide
theorem cert4_4 : ∀ b c d : F, NotAffine (strip [4,b,c,d] witness) := by unfold NotAffine; decide
theorem cert3_5 : ∀ b c : F, NotAffine (strip [5,b,c] witness) := by unfold NotAffine; decide
theorem cert4_5 : ∀ b c d : F, NotAffine (strip [5,b,c,d] witness) := by unfold NotAffine; decide
theorem cert3_6 : ∀ b c : F, NotAffine (strip [6,b,c] witness) := by unfold NotAffine; decide
theorem cert4_6 : ∀ b c d : F, NotAffine (strip [6,b,c,d] witness) := by unfold NotAffine; decide
theorem cert3_7 : ∀ b c : F, NotAffine (strip [7,b,c] witness) := by unfold NotAffine; decide
theorem cert4_7 : ∀ b c d : F, NotAffine (strip [7,b,c,d] witness) := by unfold NotAffine; decide
theorem cert3_8 : ∀ b c : F, NotAffine (strip [8,b,c] witness) := by unfold NotAffine; decide
theorem cert4_8 : ∀ b c d : F, NotAffine (strip [8,b,c,d] witness) := by unfold NotAffine; decide
theorem cert3_9 : ∀ b c : F, NotAffine (strip [9,b,c] witness) := by unfold NotAffine; decide
theorem cert4_9 : ∀ b c d : F, NotAffine (strip [9,b,c,d] witness) := by unfold NotAffine; decide
theorem cert3_10 : ∀ b c : F, NotAffine (strip [10,b,c] witness) := by unfold NotAffine; decide
theorem cert4_10 : ∀ b c d : F, NotAffine (strip [10,b,c,d] witness) := by unfold NotAffine; decide

theorem certificate3 (a b c : F) : NotAffine (strip [a,b,c] witness) := by
  have enum : ∀ z : F, z = 0 ∨ z = 1 ∨ z = 2 ∨ z = 3 ∨ z = 4 ∨ z = 5 ∨ z = 6 ∨ z = 7 ∨ z = 8 ∨ z = 9 ∨ z = 10 := by decide
  have cases_a := enum a
  rcases cases_a with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact cert3_0 b c
  · exact cert3_1 b c
  · exact cert3_2 b c
  · exact cert3_3 b c
  · exact cert3_4 b c
  · exact cert3_5 b c
  · exact cert3_6 b c
  · exact cert3_7 b c
  · exact cert3_8 b c
  · exact cert3_9 b c
  · exact cert3_10 b c

theorem certificate4 (a b c d : F) : NotAffine (strip [a,b,c,d] witness) := by
  have enum : ∀ z : F, z = 0 ∨ z = 1 ∨ z = 2 ∨ z = 3 ∨ z = 4 ∨ z = 5 ∨ z = 6 ∨ z = 7 ∨ z = 8 ∨ z = 9 ∨ z = 10 := by decide
  have cases_a := enum a
  rcases cases_a with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact cert4_0 b c d
  · exact cert4_1 b c d
  · exact cert4_2 b c d
  · exact cert4_3 b c d
  · exact cert4_4 b c d
  · exact cert4_5 b c d
  · exact cert4_6 b c d
  · exact cert4_7 b c d
  · exact cert4_8 b c d
  · exact cert4_9 b c d
  · exact cert4_10 b c d
end TLMC1043
