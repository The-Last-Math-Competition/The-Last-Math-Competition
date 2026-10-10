import Basic
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace TLMC2222
def C51 : List (List Nat) := [[17,34],[3,6,9,12,15,18,21,24,27,30,33,36,39,42,45,48]]
def K51 : List Nat := [17,3]
theorem cert51 : check 51 C51 K51 := by decide
theorem result51 : EqualChromaticClique 51 := check_sound (by decide) cert51
def C52 : List (List Nat) := [[26,13,39],[2,4,6,8,10,12,14,16,18,20,22,24,28,30,32,34,36,38,40,42,44,46,48,50]]
def K52 : List Nat := [26,4]
theorem cert52 : check 52 C52 K52 := by decide
theorem result52 : EqualChromaticClique 52 := check_sound (by decide) cert52
def C53 : List (List Nat) := []
def K53 : List Nat := []
theorem cert53 : check 53 C53 K53 := by decide
theorem result53 : EqualChromaticClique 53 := check_sound (by decide) cert53
def C54 : List (List Nat) := [[18],[36],[3,9,15,21,27,33,39,45,51],[2,4,6,8,10,12,14,16,20,22,24,26,28,30,32,34,38,40,42,44,46,48,50,52]]
def K54 : List Nat := [18,36,27,6]
theorem cert54 : check 54 C54 K54 := by decide
theorem result54 : EqualChromaticClique 54 := check_sound (by decide) cert54
def C55 : List (List Nat) := [[11,22,33,44],[5,10,15,20,25,30,35,40,45,50]]
def K55 : List Nat := [11,5]
theorem cert55 : check 55 C55 K55 := by decide
theorem result55 : EqualChromaticClique 55 := check_sound (by decide) cert55
def C56 : List (List Nat) := [[28],[2,6,7,10,14,18,21,22,26,30,34,35,38,42,46,49,50,54],[4,8,12,16,20,24,32,36,40,44,48,52]]
def K56 : List Nat := [28,14,8]
theorem cert56 : check 56 C56 K56 := by decide
theorem result56 : EqualChromaticClique 56 := check_sound (by decide) cert56
def C57 : List (List Nat) := [[19,38],[3,6,9,12,15,18,21,24,27,30,33,36,39,42,45,48,51,54]]
def K57 : List Nat := [19,3]
theorem cert57 : check 57 C57 K57 := by decide
theorem result57 : EqualChromaticClique 57 := check_sound (by decide) cert57
def C58 : List (List Nat) := [[29],[2,4,6,8,10,12,14,16,18,20,22,24,26,28,30,32,34,36,38,40,42,44,46,48,50,52,54,56]]
def K58 : List Nat := [29,2]
theorem cert58 : check 58 C58 K58 := by decide
theorem result58 : EqualChromaticClique 58 := check_sound (by decide) cert58
def C59 : List (List Nat) := []
def K59 : List Nat := []
theorem cert59 : check 59 C59 K59 := by decide
theorem result59 : EqualChromaticClique 59 := check_sound (by decide) cert59
def C60 : List (List Nat) := [[30,3,5,9,15,21,25,27,33,35,39,45,51,55,57],[2,4,8,10,14,16,20,22,26,28,32,34,38,40,44,46,50,52,56,58],[6,12,18,24,36,42,48,54]]
def K60 : List Nat := [30,20,12]
theorem cert60 : check 60 C60 K60 := by decide
theorem result60 : EqualChromaticClique 60 := check_sound (by decide) cert60
def C61 : List (List Nat) := []
def K61 : List Nat := []
theorem cert61 : check 61 C61 K61 := by decide
theorem result61 : EqualChromaticClique 61 := check_sound (by decide) cert61
def C62 : List (List Nat) := [[31],[2,4,6,8,10,12,14,16,18,20,22,24,26,28,30,32,34,36,38,40,42,44,46,48,50,52,54,56,58,60]]
def K62 : List Nat := [31,2]
theorem cert62 : check 62 C62 K62 := by decide
theorem result62 : EqualChromaticClique 62 := check_sound (by decide) cert62
def C63 : List (List Nat) := [[21,7,14,28,35,49,56],[42],[3,6,9,12,15,18,24,27,30,33,36,39,45,48,51,54,57,60]]
def K63 : List Nat := [21,42,9]
theorem cert63 : check 63 C63 K63 := by decide
theorem result63 : EqualChromaticClique 63 := check_sound (by decide) cert63
def C64 : List (List Nat) := [[8,2,4,6,10,12,14,18,20,22,26,28,30,34,36,38,42,44,46,50,52,54,58,60,62],[16],[24],[32],[40],[48],[56]]
def K64 : List Nat := [8,16,24,32,40,48,56]
theorem cert64 : check 64 C64 K64 := by decide
theorem result64 : EqualChromaticClique 64 := check_sound (by decide) cert64
def C65 : List (List Nat) := [[13,26,39,52],[5,10,15,20,25,30,35,40,45,50,55,60]]
def K65 : List Nat := [13,5]
theorem cert65 : check 65 C65 K65 := by decide
theorem result65 : EqualChromaticClique 65 := check_sound (by decide) cert65
def C66 : List (List Nat) := [[3,9,11,15,21,27,33,39,45,51,55,57,63],[2,4,8,10,14,16,20,22,26,28,32,34,38,40,44,46,50,52,56,58,62,64],[6,12,18,24,30,36,42,48,54,60]]
def K66 : List Nat := [33,22,6]
theorem cert66 : check 66 C66 K66 := by decide
theorem result66 : EqualChromaticClique 66 := check_sound (by decide) cert66
def C67 : List (List Nat) := []
def K67 : List Nat := []
theorem cert67 : check 67 C67 K67 := by decide
theorem result67 : EqualChromaticClique 67 := check_sound (by decide) cert67
def C68 : List (List Nat) := [[34,17,51],[2,4,6,8,10,12,14,16,18,20,22,24,26,28,30,32,36,38,40,42,44,46,48,50,52,54,56,58,60,62,64,66]]
def K68 : List Nat := [34,4]
theorem cert68 : check 68 C68 K68 := by decide
theorem result68 : EqualChromaticClique 68 := check_sound (by decide) cert68
def C69 : List (List Nat) := [[23,46],[3,6,9,12,15,18,21,24,27,30,33,36,39,42,45,48,51,54,57,60,63,66]]
def K69 : List Nat := [23,3]
theorem cert69 : check 69 C69 K69 := by decide
theorem result69 : EqualChromaticClique 69 := check_sound (by decide) cert69
def C70 : List (List Nat) := [[5,7,15,21,25,35,45,49,55,63,65],[2,4,6,8,12,14,16,18,22,24,26,28,32,34,36,38,42,44,46,48,52,54,56,58,62,64,66,68],[10,20,30,40,50,60]]
def K70 : List Nat := [35,14,10]
theorem cert70 : check 70 C70 K70 := by decide
theorem result70 : EqualChromaticClique 70 := check_sound (by decide) cert70
def C71 : List (List Nat) := []
def K71 : List Nat := []
theorem cert71 : check 71 C71 K71 := by decide
theorem result71 : EqualChromaticClique 71 := check_sound (by decide) cert71
def C72 : List (List Nat) := [[12],[24,4,8,16,20,28,32,40,44,52,56,64,68],[36],[48],[60],[2,3,6,9,10,14,15,18,21,22,26,27,30,33,34,38,39,42,45,46,50,51,54,57,58,62,63,66,69,70]]
def K72 : List Nat := [12,24,36,48,60,18]
theorem cert72 : check 72 C72 K72 := by decide
theorem result72 : EqualChromaticClique 72 := check_sound (by decide) cert72
def C73 : List (List Nat) := []
def K73 : List Nat := []
theorem cert73 : check 73 C73 K73 := by decide
theorem result73 : EqualChromaticClique 73 := check_sound (by decide) cert73
def C74 : List (List Nat) := [[37],[2,4,6,8,10,12,14,16,18,20,22,24,26,28,30,32,34,36,38,40,42,44,46,48,50,52,54,56,58,60,62,64,66,68,70,72]]
def K74 : List Nat := [37,2]
theorem cert74 : check 74 C74 K74 := by decide
theorem result74 : EqualChromaticClique 74 := check_sound (by decide) cert74
def C75 : List (List Nat) := [[15,3,6,9,12,18,21,24,27,33,36,39,42,48,51,54,57,63,66,69,72],[30],[45],[60],[5,10,20,25,35,40,50,55,65,70]]
def K75 : List Nat := [15,30,45,60,25]
theorem cert75 : check 75 C75 K75 := by decide
theorem result75 : EqualChromaticClique 75 := check_sound (by decide) cert75
def C76 : List (List Nat) := [[38,19,57],[2,4,6,8,10,12,14,16,18,20,22,24,26,28,30,32,34,36,40,42,44,46,48,50,52,54,56,58,60,62,64,66,68,70,72,74]]
def K76 : List Nat := [38,4]
theorem cert76 : check 76 C76 K76 := by decide
theorem result76 : EqualChromaticClique 76 := check_sound (by decide) cert76
def C77 : List (List Nat) := [[11,22,33,44,55,66],[7,14,21,28,35,42,49,56,63,70]]
def K77 : List Nat := [11,7]
theorem cert77 : check 77 C77 K77 := by decide
theorem result77 : EqualChromaticClique 77 := check_sound (by decide) cert77
def C78 : List (List Nat) := [[3,9,13,15,21,27,33,39,45,51,57,63,65,69,75],[2,4,8,10,14,16,20,22,26,28,32,34,38,40,44,46,50,52,56,58,62,64,68,70,74,76],[6,12,18,24,30,36,42,48,54,60,66,72]]
def K78 : List Nat := [39,26,6]
theorem cert78 : check 78 C78 K78 := by decide
theorem result78 : EqualChromaticClique 78 := check_sound (by decide) cert78
def C79 : List (List Nat) := []
def K79 : List Nat := []
theorem cert79 : check 79 C79 K79 := by decide
theorem result79 : EqualChromaticClique 79 := check_sound (by decide) cert79
def C80 : List (List Nat) := [[20,2,5,6,10,14,15,18,22,25,26,30,34,35,38,42,45,46,50,54,55,58,62,65,66,70,74,75,78],[40],[60],[4,8,12,16,24,28,32,36,44,48,52,56,64,68,72,76]]
def K80 : List Nat := [20,40,60,16]
theorem cert80 : check 80 C80 K80 := by decide
theorem result80 : EqualChromaticClique 80 := check_sound (by decide) cert80
def C81 : List (List Nat) := [[9,3,6,12,15,21,24,30,33,39,42,48,51,57,60,66,69,75,78],[18],[27],[36],[45],[54],[63],[72]]
def K81 : List Nat := [9,18,27,36,45,54,63,72]
theorem cert81 : check 81 C81 K81 := by decide
theorem result81 : EqualChromaticClique 81 := check_sound (by decide) cert81
def C82 : List (List Nat) := [[41],[2,4,6,8,10,12,14,16,18,20,22,24,26,28,30,32,34,36,38,40,42,44,46,48,50,52,54,56,58,60,62,64,66,68,70,72,74,76,78,80]]
def K82 : List Nat := [41,2]
theorem cert82 : check 82 C82 K82 := by decide
theorem result82 : EqualChromaticClique 82 := check_sound (by decide) cert82
def C83 : List (List Nat) := []
def K83 : List Nat := []
theorem cert83 : check 83 C83 K83 := by decide
theorem result83 : EqualChromaticClique 83 := check_sound (by decide) cert83
def C84 : List (List Nat) := [[42,3,7,9,15,21,27,33,35,39,45,49,51,57,63,69,75,77,81],[2,4,8,10,14,16,20,22,26,28,32,34,38,40,44,46,50,52,56,58,62,64,68,70,74,76,80,82],[6,12,18,24,30,36,48,54,60,66,72,78]]
def K84 : List Nat := [42,28,12]
theorem cert84 : check 84 C84 K84 := by decide
theorem result84 : EqualChromaticClique 84 := check_sound (by decide) cert84
def C85 : List (List Nat) := [[17,34,51,68],[5,10,15,20,25,30,35,40,45,50,55,60,65,70,75,80]]
def K85 : List Nat := [17,5]
theorem cert85 : check 85 C85 K85 := by decide
theorem result85 : EqualChromaticClique 85 := check_sound (by decide) cert85
def C86 : List (List Nat) := [[43],[2,4,6,8,10,12,14,16,18,20,22,24,26,28,30,32,34,36,38,40,42,44,46,48,50,52,54,56,58,60,62,64,66,68,70,72,74,76,78,80,82,84]]
def K86 : List Nat := [43,2]
theorem cert86 : check 86 C86 K86 := by decide
theorem result86 : EqualChromaticClique 86 := check_sound (by decide) cert86
def C87 : List (List Nat) := [[29,58],[3,6,9,12,15,18,21,24,27,30,33,36,39,42,45,48,51,54,57,60,63,66,69,72,75,78,81,84]]
def K87 : List Nat := [29,3]
theorem cert87 : check 87 C87 K87 := by decide
theorem result87 : EqualChromaticClique 87 := check_sound (by decide) cert87
def C88 : List (List Nat) := [[44],[2,6,10,11,14,18,22,26,30,33,34,38,42,46,50,54,55,58,62,66,70,74,77,78,82,86],[4,8,12,16,20,24,28,32,36,40,48,52,56,60,64,68,72,76,80,84]]
def K88 : List Nat := [44,22,8]
theorem cert88 : check 88 C88 K88 := by decide
theorem result88 : EqualChromaticClique 88 := check_sound (by decide) cert88
def C89 : List (List Nat) := []
def K89 : List Nat := []
theorem cert89 : check 89 C89 K89 := by decide
theorem result89 : EqualChromaticClique 89 := check_sound (by decide) cert89
def C90 : List (List Nat) := [[30,2,4,8,10,14,16,20,22,26,28,32,34,38,40,44,46,50,52,56,58,62,64,68,70,74,76,80,82,86,88],[60],[3,5,9,15,21,25,27,33,35,39,45,51,55,57,63,65,69,75,81,85,87],[6,12,18,24,36,42,48,54,66,72,78,84]]
def K90 : List Nat := [30,60,45,18]
theorem cert90 : check 90 C90 K90 := by decide
theorem result90 : EqualChromaticClique 90 := check_sound (by decide) cert90
def C91 : List (List Nat) := [[13,26,39,52,65,78],[7,14,21,28,35,42,49,56,63,70,77,84]]
def K91 : List Nat := [13,7]
theorem cert91 : check 91 C91 K91 := by decide
theorem result91 : EqualChromaticClique 91 := check_sound (by decide) cert91
def C92 : List (List Nat) := [[46,23,69],[2,4,6,8,10,12,14,16,18,20,22,24,26,28,30,32,34,36,38,40,42,44,48,50,52,54,56,58,60,62,64,66,68,70,72,74,76,78,80,82,84,86,88,90]]
def K92 : List Nat := [46,4]
theorem cert92 : check 92 C92 K92 := by decide
theorem result92 : EqualChromaticClique 92 := check_sound (by decide) cert92
def C93 : List (List Nat) := [[31,62],[3,6,9,12,15,18,21,24,27,30,33,36,39,42,45,48,51,54,57,60,63,66,69,72,75,78,81,84,87,90]]
def K93 : List Nat := [31,3]
theorem cert93 : check 93 C93 K93 := by decide
theorem result93 : EqualChromaticClique 93 := check_sound (by decide) cert93
def C94 : List (List Nat) := [[47],[2,4,6,8,10,12,14,16,18,20,22,24,26,28,30,32,34,36,38,40,42,44,46,48,50,52,54,56,58,60,62,64,66,68,70,72,74,76,78,80,82,84,86,88,90,92]]
def K94 : List Nat := [47,2]
theorem cert94 : check 94 C94 K94 := by decide
theorem result94 : EqualChromaticClique 94 := check_sound (by decide) cert94
def C95 : List (List Nat) := [[19,38,57,76],[5,10,15,20,25,30,35,40,45,50,55,60,65,70,75,80,85,90]]
def K95 : List Nat := [19,5]
theorem cert95 : check 95 C95 K95 := by decide
theorem result95 : EqualChromaticClique 95 := check_sound (by decide) cert95
def C96 : List (List Nat) := [[24],[48],[72],[2,3,4,6,9,10,12,14,15,18,20,21,22,26,27,28,30,33,34,36,38,39,42,44,45,46,50,51,52,54,57,58,60,62,63,66,68,69,70,74,75,76,78,81,82,84,86,87,90,92,93,94],[8,16,32,40,56,64,80,88]]
def K96 : List Nat := [24,48,72,12,32]
theorem cert96 : check 96 C96 K96 := by decide
theorem result96 : EqualChromaticClique 96 := check_sound (by decide) cert96
def C97 : List (List Nat) := []
def K97 : List Nat := []
theorem cert97 : check 97 C97 K97 := by decide
theorem result97 : EqualChromaticClique 97 := check_sound (by decide) cert97
def C98 : List (List Nat) := [[14,2,4,6,8,10,12,16,18,20,22,24,26,30,32,34,36,38,40,44,46,48,50,52,54,58,60,62,64,66,68,72,74,76,78,80,82,86,88,90,92,94,96],[28],[42],[56],[70],[84],[7,21,35,49,63,77,91]]
def K98 : List Nat := [14,28,42,56,70,84,49]
theorem cert98 : check 98 C98 K98 := by decide
theorem result98 : EqualChromaticClique 98 := check_sound (by decide) cert98
def C99 : List (List Nat) := [[33,11,22,44,55,77,88],[66],[3,6,9,12,15,18,21,24,27,30,36,39,42,45,48,51,54,57,60,63,69,72,75,78,81,84,87,90,93,96]]
def K99 : List Nat := [33,66,9]
theorem cert99 : check 99 C99 K99 := by decide
theorem result99 : EqualChromaticClique 99 := check_sound (by decide) cert99
def C100 : List (List Nat) := [[10],[20,2,4,6,8,12,14,16,18,22,24,26,28,32,34,36,38,42,44,46,48,52,54,56,58,62,64,66,68,72,74,76,78,82,84,86,88,92,94,96,98],[30],[40],[50,5,15,25,35,45,55,65,75,85,95],[60],[70],[80],[90]]
def K100 : List Nat := [10,20,30,40,50,60,70,80,90]
theorem cert100 : check 100 C100 K100 := by decide
theorem result100 : EqualChromaticClique 100 := check_sound (by decide) cert100
theorem range51_100 (n : Nat) (hl : 51 ≤ n) (hh : n ≤ 100) : EqualChromaticClique n := by
  have h : n = 51 ∨ n = 52 ∨ n = 53 ∨ n = 54 ∨ n = 55 ∨ n = 56 ∨ n = 57 ∨ n = 58 ∨ n = 59 ∨ n = 60 ∨ n = 61 ∨ n = 62 ∨ n = 63 ∨ n = 64 ∨ n = 65 ∨ n = 66 ∨ n = 67 ∨ n = 68 ∨ n = 69 ∨ n = 70 ∨ n = 71 ∨ n = 72 ∨ n = 73 ∨ n = 74 ∨ n = 75 ∨ n = 76 ∨ n = 77 ∨ n = 78 ∨ n = 79 ∨ n = 80 ∨ n = 81 ∨ n = 82 ∨ n = 83 ∨ n = 84 ∨ n = 85 ∨ n = 86 ∨ n = 87 ∨ n = 88 ∨ n = 89 ∨ n = 90 ∨ n = 91 ∨ n = 92 ∨ n = 93 ∨ n = 94 ∨ n = 95 ∨ n = 96 ∨ n = 97 ∨ n = 98 ∨ n = 99 ∨ n = 100 := by omega
  rcases h with h51 | h52 | h53 | h54 | h55 | h56 | h57 | h58 | h59 | h60 | h61 | h62 | h63 | h64 | h65 | h66 | h67 | h68 | h69 | h70 | h71 | h72 | h73 | h74 | h75 | h76 | h77 | h78 | h79 | h80 | h81 | h82 | h83 | h84 | h85 | h86 | h87 | h88 | h89 | h90 | h91 | h92 | h93 | h94 | h95 | h96 | h97 | h98 | h99 | h100
  · subst n; exact result51
  · subst n; exact result52
  · subst n; exact result53
  · subst n; exact result54
  · subst n; exact result55
  · subst n; exact result56
  · subst n; exact result57
  · subst n; exact result58
  · subst n; exact result59
  · subst n; exact result60
  · subst n; exact result61
  · subst n; exact result62
  · subst n; exact result63
  · subst n; exact result64
  · subst n; exact result65
  · subst n; exact result66
  · subst n; exact result67
  · subst n; exact result68
  · subst n; exact result69
  · subst n; exact result70
  · subst n; exact result71
  · subst n; exact result72
  · subst n; exact result73
  · subst n; exact result74
  · subst n; exact result75
  · subst n; exact result76
  · subst n; exact result77
  · subst n; exact result78
  · subst n; exact result79
  · subst n; exact result80
  · subst n; exact result81
  · subst n; exact result82
  · subst n; exact result83
  · subst n; exact result84
  · subst n; exact result85
  · subst n; exact result86
  · subst n; exact result87
  · subst n; exact result88
  · subst n; exact result89
  · subst n; exact result90
  · subst n; exact result91
  · subst n; exact result92
  · subst n; exact result93
  · subst n; exact result94
  · subst n; exact result95
  · subst n; exact result96
  · subst n; exact result97
  · subst n; exact result98
  · subst n; exact result99
  · subst n; exact result100
end TLMC2222
