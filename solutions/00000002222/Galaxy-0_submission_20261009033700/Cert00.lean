import Basic
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace TLMC2222
def C1 : List (List Nat) := []
def K1 : List Nat := []
theorem cert1 : check 1 C1 K1 := by decide
theorem result1 : EqualChromaticClique 1 := check_sound (by decide) cert1
def C2 : List (List Nat) := []
def K2 : List Nat := []
theorem cert2 : check 2 C2 K2 := by decide
theorem result2 : EqualChromaticClique 2 := check_sound (by decide) cert2
def C3 : List (List Nat) := []
def K3 : List Nat := []
theorem cert3 : check 3 C3 K3 := by decide
theorem result3 : EqualChromaticClique 3 := check_sound (by decide) cert3
def C4 : List (List Nat) := [[2]]
def K4 : List Nat := [2]
theorem cert4 : check 4 C4 K4 := by decide
theorem result4 : EqualChromaticClique 4 := check_sound (by decide) cert4
def C5 : List (List Nat) := []
def K5 : List Nat := []
theorem cert5 : check 5 C5 K5 := by decide
theorem result5 : EqualChromaticClique 5 := check_sound (by decide) cert5
def C6 : List (List Nat) := [[3],[2,4]]
def K6 : List Nat := [3,2]
theorem cert6 : check 6 C6 K6 := by decide
theorem result6 : EqualChromaticClique 6 := check_sound (by decide) cert6
def C7 : List (List Nat) := []
def K7 : List Nat := []
theorem cert7 : check 7 C7 K7 := by decide
theorem result7 : EqualChromaticClique 7 := check_sound (by decide) cert7
def C8 : List (List Nat) := [[4],[2,6]]
def K8 : List Nat := [4,2]
theorem cert8 : check 8 C8 K8 := by decide
theorem result8 : EqualChromaticClique 8 := check_sound (by decide) cert8
def C9 : List (List Nat) := [[3],[6]]
def K9 : List Nat := [3,6]
theorem cert9 : check 9 C9 K9 := by decide
theorem result9 : EqualChromaticClique 9 := check_sound (by decide) cert9
def C10 : List (List Nat) := [[5],[2,4,6,8]]
def K10 : List Nat := [5,2]
theorem cert10 : check 10 C10 K10 := by decide
theorem result10 : EqualChromaticClique 10 := check_sound (by decide) cert10
def C11 : List (List Nat) := []
def K11 : List Nat := []
theorem cert11 : check 11 C11 K11 := by decide
theorem result11 : EqualChromaticClique 11 := check_sound (by decide) cert11
def C12 : List (List Nat) := [[6,3,9],[2,4,8,10]]
def K12 : List Nat := [6,4]
theorem cert12 : check 12 C12 K12 := by decide
theorem result12 : EqualChromaticClique 12 := check_sound (by decide) cert12
def C13 : List (List Nat) := []
def K13 : List Nat := []
theorem cert13 : check 13 C13 K13 := by decide
theorem result13 : EqualChromaticClique 13 := check_sound (by decide) cert13
def C14 : List (List Nat) := [[7],[2,4,6,8,10,12]]
def K14 : List Nat := [7,2]
theorem cert14 : check 14 C14 K14 := by decide
theorem result14 : EqualChromaticClique 14 := check_sound (by decide) cert14
def C15 : List (List Nat) := [[5,10],[3,6,9,12]]
def K15 : List Nat := [5,3]
theorem cert15 : check 15 C15 K15 := by decide
theorem result15 : EqualChromaticClique 15 := check_sound (by decide) cert15
def C16 : List (List Nat) := [[4,2,6,10,14],[8],[12]]
def K16 : List Nat := [4,8,12]
theorem cert16 : check 16 C16 K16 := by decide
theorem result16 : EqualChromaticClique 16 := check_sound (by decide) cert16
def C17 : List (List Nat) := []
def K17 : List Nat := []
theorem cert17 : check 17 C17 K17 := by decide
theorem result17 : EqualChromaticClique 17 := check_sound (by decide) cert17
def C18 : List (List Nat) := [[6,2,4,8,10,14,16],[12],[3,9,15]]
def K18 : List Nat := [6,12,9]
theorem cert18 : check 18 C18 K18 := by decide
theorem result18 : EqualChromaticClique 18 := check_sound (by decide) cert18
def C19 : List (List Nat) := []
def K19 : List Nat := []
theorem cert19 : check 19 C19 K19 := by decide
theorem result19 : EqualChromaticClique 19 := check_sound (by decide) cert19
def C20 : List (List Nat) := [[10,5,15],[2,4,6,8,12,14,16,18]]
def K20 : List Nat := [10,4]
theorem cert20 : check 20 C20 K20 := by decide
theorem result20 : EqualChromaticClique 20 := check_sound (by decide) cert20
def C21 : List (List Nat) := [[7,14],[3,6,9,12,15,18]]
def K21 : List Nat := [7,3]
theorem cert21 : check 21 C21 K21 := by decide
theorem result21 : EqualChromaticClique 21 := check_sound (by decide) cert21
def C22 : List (List Nat) := [[11],[2,4,6,8,10,12,14,16,18,20]]
def K22 : List Nat := [11,2]
theorem cert22 : check 22 C22 K22 := by decide
theorem result22 : EqualChromaticClique 22 := check_sound (by decide) cert22
def C23 : List (List Nat) := []
def K23 : List Nat := []
theorem cert23 : check 23 C23 K23 := by decide
theorem result23 : EqualChromaticClique 23 := check_sound (by decide) cert23
def C24 : List (List Nat) := [[12],[2,3,6,9,10,14,15,18,21,22],[4,8,16,20]]
def K24 : List Nat := [12,6,8]
theorem cert24 : check 24 C24 K24 := by decide
theorem result24 : EqualChromaticClique 24 := check_sound (by decide) cert24
def C25 : List (List Nat) := [[5],[10],[15],[20]]
def K25 : List Nat := [5,10,15,20]
theorem cert25 : check 25 C25 K25 := by decide
theorem result25 : EqualChromaticClique 25 := check_sound (by decide) cert25
def C26 : List (List Nat) := [[13],[2,4,6,8,10,12,14,16,18,20,22,24]]
def K26 : List Nat := [13,2]
theorem cert26 : check 26 C26 K26 := by decide
theorem result26 : EqualChromaticClique 26 := check_sound (by decide) cert26
def C27 : List (List Nat) := [[9],[18],[3,6,12,15,21,24]]
def K27 : List Nat := [9,18,3]
theorem cert27 : check 27 C27 K27 := by decide
theorem result27 : EqualChromaticClique 27 := check_sound (by decide) cert27
def C28 : List (List Nat) := [[14,7,21],[2,4,6,8,10,12,16,18,20,22,24,26]]
def K28 : List Nat := [14,4]
theorem cert28 : check 28 C28 K28 := by decide
theorem result28 : EqualChromaticClique 28 := check_sound (by decide) cert28
def C29 : List (List Nat) := []
def K29 : List Nat := []
theorem cert29 : check 29 C29 K29 := by decide
theorem result29 : EqualChromaticClique 29 := check_sound (by decide) cert29
def C30 : List (List Nat) := [[3,5,9,15,21,25,27],[2,4,8,10,14,16,20,22,26,28],[6,12,18,24]]
def K30 : List Nat := [15,10,6]
theorem cert30 : check 30 C30 K30 := by decide
theorem result30 : EqualChromaticClique 30 := check_sound (by decide) cert30
def C31 : List (List Nat) := []
def K31 : List Nat := []
theorem cert31 : check 31 C31 K31 := by decide
theorem result31 : EqualChromaticClique 31 := check_sound (by decide) cert31
def C32 : List (List Nat) := [[8],[16],[24],[2,4,6,10,12,14,18,20,22,26,28,30]]
def K32 : List Nat := [8,16,24,4]
theorem cert32 : check 32 C32 K32 := by decide
theorem result32 : EqualChromaticClique 32 := check_sound (by decide) cert32
def C33 : List (List Nat) := [[11,22],[3,6,9,12,15,18,21,24,27,30]]
def K33 : List Nat := [11,3]
theorem cert33 : check 33 C33 K33 := by decide
theorem result33 : EqualChromaticClique 33 := check_sound (by decide) cert33
def C34 : List (List Nat) := [[17],[2,4,6,8,10,12,14,16,18,20,22,24,26,28,30,32]]
def K34 : List Nat := [17,2]
theorem cert34 : check 34 C34 K34 := by decide
theorem result34 : EqualChromaticClique 34 := check_sound (by decide) cert34
def C35 : List (List Nat) := [[7,14,21,28],[5,10,15,20,25,30]]
def K35 : List Nat := [7,5]
theorem cert35 : check 35 C35 K35 := by decide
theorem result35 : EqualChromaticClique 35 := check_sound (by decide) cert35
def C36 : List (List Nat) := [[6],[12,2,4,8,10,14,16,20,22,26,28,32,34],[18,3,9,15,21,27,33],[24],[30]]
def K36 : List Nat := [6,12,18,24,30]
theorem cert36 : check 36 C36 K36 := by decide
theorem result36 : EqualChromaticClique 36 := check_sound (by decide) cert36
def C37 : List (List Nat) := []
def K37 : List Nat := []
theorem cert37 : check 37 C37 K37 := by decide
theorem result37 : EqualChromaticClique 37 := check_sound (by decide) cert37
def C38 : List (List Nat) := [[19],[2,4,6,8,10,12,14,16,18,20,22,24,26,28,30,32,34,36]]
def K38 : List Nat := [19,2]
theorem cert38 : check 38 C38 K38 := by decide
theorem result38 : EqualChromaticClique 38 := check_sound (by decide) cert38
def C39 : List (List Nat) := [[13,26],[3,6,9,12,15,18,21,24,27,30,33,36]]
def K39 : List Nat := [13,3]
theorem cert39 : check 39 C39 K39 := by decide
theorem result39 : EqualChromaticClique 39 := check_sound (by decide) cert39
def C40 : List (List Nat) := [[20],[2,5,6,10,14,15,18,22,25,26,30,34,35,38],[4,8,12,16,24,28,32,36]]
def K40 : List Nat := [20,10,8]
theorem cert40 : check 40 C40 K40 := by decide
theorem result40 : EqualChromaticClique 40 := check_sound (by decide) cert40
def C41 : List (List Nat) := []
def K41 : List Nat := []
theorem cert41 : check 41 C41 K41 := by decide
theorem result41 : EqualChromaticClique 41 := check_sound (by decide) cert41
def C42 : List (List Nat) := [[3,7,9,15,21,27,33,35,39],[2,4,8,10,14,16,20,22,26,28,32,34,38,40],[6,12,18,24,30,36]]
def K42 : List Nat := [21,14,6]
theorem cert42 : check 42 C42 K42 := by decide
theorem result42 : EqualChromaticClique 42 := check_sound (by decide) cert42
def C43 : List (List Nat) := []
def K43 : List Nat := []
theorem cert43 : check 43 C43 K43 := by decide
theorem result43 : EqualChromaticClique 43 := check_sound (by decide) cert43
def C44 : List (List Nat) := [[22,11,33],[2,4,6,8,10,12,14,16,18,20,24,26,28,30,32,34,36,38,40,42]]
def K44 : List Nat := [22,4]
theorem cert44 : check 44 C44 K44 := by decide
theorem result44 : EqualChromaticClique 44 := check_sound (by decide) cert44
def C45 : List (List Nat) := [[15,5,10,20,25,35,40],[30],[3,6,9,12,18,21,24,27,33,36,39,42]]
def K45 : List Nat := [15,30,9]
theorem cert45 : check 45 C45 K45 := by decide
theorem result45 : EqualChromaticClique 45 := check_sound (by decide) cert45
def C46 : List (List Nat) := [[23],[2,4,6,8,10,12,14,16,18,20,22,24,26,28,30,32,34,36,38,40,42,44]]
def K46 : List Nat := [23,2]
theorem cert46 : check 46 C46 K46 := by decide
theorem result46 : EqualChromaticClique 46 := check_sound (by decide) cert46
def C47 : List (List Nat) := []
def K47 : List Nat := []
theorem cert47 : check 47 C47 K47 := by decide
theorem result47 : EqualChromaticClique 47 := check_sound (by decide) cert47
def C48 : List (List Nat) := [[12,2,3,6,9,10,14,15,18,21,22,26,27,30,33,34,38,39,42,45,46],[24],[36],[4,8,16,20,28,32,40,44]]
def K48 : List Nat := [12,24,36,16]
theorem cert48 : check 48 C48 K48 := by decide
theorem result48 : EqualChromaticClique 48 := check_sound (by decide) cert48
def C49 : List (List Nat) := [[7],[14],[21],[28],[35],[42]]
def K49 : List Nat := [7,14,21,28,35,42]
theorem cert49 : check 49 C49 K49 := by decide
theorem result49 : EqualChromaticClique 49 := check_sound (by decide) cert49
def C50 : List (List Nat) := [[10,2,4,6,8,12,14,16,18,22,24,26,28,32,34,36,38,42,44,46,48],[20],[30],[40],[5,15,25,35,45]]
def K50 : List Nat := [10,20,30,40,25]
theorem cert50 : check 50 C50 K50 := by decide
theorem result50 : EqualChromaticClique 50 := check_sound (by decide) cert50
theorem range1_50 (n : Nat) (hl : 1 ≤ n) (hh : n ≤ 50) : EqualChromaticClique n := by
  have h : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 13 ∨ n = 14 ∨ n = 15 ∨ n = 16 ∨ n = 17 ∨ n = 18 ∨ n = 19 ∨ n = 20 ∨ n = 21 ∨ n = 22 ∨ n = 23 ∨ n = 24 ∨ n = 25 ∨ n = 26 ∨ n = 27 ∨ n = 28 ∨ n = 29 ∨ n = 30 ∨ n = 31 ∨ n = 32 ∨ n = 33 ∨ n = 34 ∨ n = 35 ∨ n = 36 ∨ n = 37 ∨ n = 38 ∨ n = 39 ∨ n = 40 ∨ n = 41 ∨ n = 42 ∨ n = 43 ∨ n = 44 ∨ n = 45 ∨ n = 46 ∨ n = 47 ∨ n = 48 ∨ n = 49 ∨ n = 50 := by omega
  rcases h with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39 | h40 | h41 | h42 | h43 | h44 | h45 | h46 | h47 | h48 | h49 | h50
  · subst n; exact result1
  · subst n; exact result2
  · subst n; exact result3
  · subst n; exact result4
  · subst n; exact result5
  · subst n; exact result6
  · subst n; exact result7
  · subst n; exact result8
  · subst n; exact result9
  · subst n; exact result10
  · subst n; exact result11
  · subst n; exact result12
  · subst n; exact result13
  · subst n; exact result14
  · subst n; exact result15
  · subst n; exact result16
  · subst n; exact result17
  · subst n; exact result18
  · subst n; exact result19
  · subst n; exact result20
  · subst n; exact result21
  · subst n; exact result22
  · subst n; exact result23
  · subst n; exact result24
  · subst n; exact result25
  · subst n; exact result26
  · subst n; exact result27
  · subst n; exact result28
  · subst n; exact result29
  · subst n; exact result30
  · subst n; exact result31
  · subst n; exact result32
  · subst n; exact result33
  · subst n; exact result34
  · subst n; exact result35
  · subst n; exact result36
  · subst n; exact result37
  · subst n; exact result38
  · subst n; exact result39
  · subst n; exact result40
  · subst n; exact result41
  · subst n; exact result42
  · subst n; exact result43
  · subst n; exact result44
  · subst n; exact result45
  · subst n; exact result46
  · subst n; exact result47
  · subst n; exact result48
  · subst n; exact result49
  · subst n; exact result50
end TLMC2222
