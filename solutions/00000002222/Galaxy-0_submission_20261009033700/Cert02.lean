import Basic
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace TLMC2222
def C101 : List (List Nat) := []
def K101 : List Nat := []
theorem cert101 : check 101 C101 K101 := by decide
theorem result101 : EqualChromaticClique 101 := check_sound (by decide) cert101
def C102 : List (List Nat) := [[3,9,15,17,21,27,33,39,45,51,57,63,69,75,81,85,87,93,99],[2,4,8,10,14,16,20,22,26,28,32,34,38,40,44,46,50,52,56,58,62,64,68,70,74,76,80,82,86,88,92,94,98,100],[6,12,18,24,30,36,42,48,54,60,66,72,78,84,90,96]]
def K102 : List Nat := [51,34,6]
theorem cert102 : check 102 C102 K102 := by decide
theorem result102 : EqualChromaticClique 102 := check_sound (by decide) cert102
def C103 : List (List Nat) := []
def K103 : List Nat := []
theorem cert103 : check 103 C103 K103 := by decide
theorem result103 : EqualChromaticClique 103 := check_sound (by decide) cert103
def C104 : List (List Nat) := [[52],[2,6,10,13,14,18,22,26,30,34,38,39,42,46,50,54,58,62,65,66,70,74,78,82,86,90,91,94,98,102],[4,8,12,16,20,24,28,32,36,40,44,48,56,60,64,68,72,76,80,84,88,92,96,100]]
def K104 : List Nat := [52,26,8]
theorem cert104 : check 104 C104 K104 := by decide
theorem result104 : EqualChromaticClique 104 := check_sound (by decide) cert104
def C105 : List (List Nat) := [[5,7,10,14,20,25,28,35,40,49,50,55,56,65,70,77,80,85,91,95,98,100],[3,6,9,12,18,21,24,27,33,36,39,42,48,51,54,57,63,66,69,72,78,81,84,87,93,96,99,102],[15,30,45,60,75,90]]
def K105 : List Nat := [35,21,15]
theorem cert105 : check 105 C105 K105 := by decide
theorem result105 : EqualChromaticClique 105 := check_sound (by decide) cert105
def C106 : List (List Nat) := [[53],[2,4,6,8,10,12,14,16,18,20,22,24,26,28,30,32,34,36,38,40,42,44,46,48,50,52,54,56,58,60,62,64,66,68,70,72,74,76,78,80,82,84,86,88,90,92,94,96,98,100,102,104]]
def K106 : List Nat := [53,2]
theorem cert106 : check 106 C106 K106 := by decide
theorem result106 : EqualChromaticClique 106 := check_sound (by decide) cert106
def C107 : List (List Nat) := []
def K107 : List Nat := []
theorem cert107 : check 107 C107 K107 := by decide
theorem result107 : EqualChromaticClique 107 := check_sound (by decide) cert107
def C108 : List (List Nat) := [[18],[36],[54,3,9,15,21,27,33,39,45,51,57,63,69,75,81,87,93,99,105],[72],[90],[2,4,6,8,10,12,14,16,20,22,24,26,28,30,32,34,38,40,42,44,46,48,50,52,56,58,60,62,64,66,68,70,74,76,78,80,82,84,86,88,92,94,96,98,100,102,104,106]]
def K108 : List Nat := [18,36,54,72,90,12]
theorem cert108 : check 108 C108 K108 := by decide
theorem result108 : EqualChromaticClique 108 := check_sound (by decide) cert108
def C109 : List (List Nat) := []
def K109 : List Nat := []
theorem cert109 : check 109 C109 K109 := by decide
theorem result109 : EqualChromaticClique 109 := check_sound (by decide) cert109
def C110 : List (List Nat) := [[5,11,15,25,33,35,45,55,65,75,77,85,95,99,105],[2,4,6,8,12,14,16,18,22,24,26,28,32,34,36,38,42,44,46,48,52,54,56,58,62,64,66,68,72,74,76,78,82,84,86,88,92,94,96,98,102,104,106,108],[10,20,30,40,50,60,70,80,90,100]]
def K110 : List Nat := [55,22,10]
theorem cert110 : check 110 C110 K110 := by decide
theorem result110 : EqualChromaticClique 110 := check_sound (by decide) cert110
def C111 : List (List Nat) := [[37,74],[3,6,9,12,15,18,21,24,27,30,33,36,39,42,45,48,51,54,57,60,63,66,69,72,75,78,81,84,87,90,93,96,99,102,105,108]]
def K111 : List Nat := [37,3]
theorem cert111 : check 111 C111 K111 := by decide
theorem result111 : EqualChromaticClique 111 := check_sound (by decide) cert111
def C112 : List (List Nat) := [[28,2,6,7,10,14,18,21,22,26,30,34,35,38,42,46,49,50,54,58,62,63,66,70,74,77,78,82,86,90,91,94,98,102,105,106,110],[56],[84],[4,8,12,16,20,24,32,36,40,44,48,52,60,64,68,72,76,80,88,92,96,100,104,108]]
def K112 : List Nat := [28,56,84,16]
theorem cert112 : check 112 C112 K112 := by decide
theorem result112 : EqualChromaticClique 112 := check_sound (by decide) cert112
def C113 : List (List Nat) := []
def K113 : List Nat := []
theorem cert113 : check 113 C113 K113 := by decide
theorem result113 : EqualChromaticClique 113 := check_sound (by decide) cert113
def C114 : List (List Nat) := [[3,9,15,19,21,27,33,39,45,51,57,63,69,75,81,87,93,95,99,105,111],[2,4,8,10,14,16,20,22,26,28,32,34,38,40,44,46,50,52,56,58,62,64,68,70,74,76,80,82,86,88,92,94,98,100,104,106,110,112],[6,12,18,24,30,36,42,48,54,60,66,72,78,84,90,96,102,108]]
def K114 : List Nat := [57,38,6]
theorem cert114 : check 114 C114 K114 := by decide
theorem result114 : EqualChromaticClique 114 := check_sound (by decide) cert114
def C115 : List (List Nat) := [[23,46,69,92],[5,10,15,20,25,30,35,40,45,50,55,60,65,70,75,80,85,90,95,100,105,110]]
def K115 : List Nat := [23,5]
theorem cert115 : check 115 C115 K115 := by decide
theorem result115 : EqualChromaticClique 115 := check_sound (by decide) cert115
def C116 : List (List Nat) := [[58,29,87],[2,4,6,8,10,12,14,16,18,20,22,24,26,28,30,32,34,36,38,40,42,44,46,48,50,52,54,56,60,62,64,66,68,70,72,74,76,78,80,82,84,86,88,90,92,94,96,98,100,102,104,106,108,110,112,114]]
def K116 : List Nat := [58,4]
theorem cert116 : check 116 C116 K116 := by decide
theorem result116 : EqualChromaticClique 116 := check_sound (by decide) cert116
def C117 : List (List Nat) := [[39,13,26,52,65,91,104],[78],[3,6,9,12,15,18,21,24,27,30,33,36,42,45,48,51,54,57,60,63,66,69,72,75,81,84,87,90,93,96,99,102,105,108,111,114]]
def K117 : List Nat := [39,78,9]
theorem cert117 : check 117 C117 K117 := by decide
theorem result117 : EqualChromaticClique 117 := check_sound (by decide) cert117
def C118 : List (List Nat) := [[59],[2,4,6,8,10,12,14,16,18,20,22,24,26,28,30,32,34,36,38,40,42,44,46,48,50,52,54,56,58,60,62,64,66,68,70,72,74,76,78,80,82,84,86,88,90,92,94,96,98,100,102,104,106,108,110,112,114,116]]
def K118 : List Nat := [59,2]
theorem cert118 : check 118 C118 K118 := by decide
theorem result118 : EqualChromaticClique 118 := check_sound (by decide) cert118
def C119 : List (List Nat) := [[17,34,51,68,85,102],[7,14,21,28,35,42,49,56,63,70,77,84,91,98,105,112]]
def K119 : List Nat := [17,7]
theorem cert119 : check 119 C119 K119 := by decide
theorem result119 : EqualChromaticClique 119 := check_sound (by decide) cert119
def C120 : List (List Nat) := [[60],[2,3,5,6,9,10,14,15,18,21,22,25,26,27,30,33,34,35,38,39,42,45,46,50,51,54,55,57,58,62,63,65,66,69,70,74,75,78,81,82,85,86,87,90,93,94,95,98,99,102,105,106,110,111,114,115,117,118],[4,8,16,20,28,32,40,44,52,56,64,68,76,80,88,92,100,104,112,116],[12,24,36,48,72,84,96,108]]
def K120 : List Nat := [60,30,40,24]
theorem cert120 : check 120 C120 K120 := by decide
theorem result120 : EqualChromaticClique 120 := check_sound (by decide) cert120
def C121 : List (List Nat) := [[11],[22],[33],[44],[55],[66],[77],[88],[99],[110]]
def K121 : List Nat := [11,22,33,44,55,66,77,88,99,110]
theorem cert121 : check 121 C121 K121 := by decide
theorem result121 : EqualChromaticClique 121 := check_sound (by decide) cert121
def C122 : List (List Nat) := [[61],[2,4,6,8,10,12,14,16,18,20,22,24,26,28,30,32,34,36,38,40,42,44,46,48,50,52,54,56,58,60,62,64,66,68,70,72,74,76,78,80,82,84,86,88,90,92,94,96,98,100,102,104,106,108,110,112,114,116,118,120]]
def K122 : List Nat := [61,2]
theorem cert122 : check 122 C122 K122 := by decide
theorem result122 : EqualChromaticClique 122 := check_sound (by decide) cert122
def C123 : List (List Nat) := [[41,82],[3,6,9,12,15,18,21,24,27,30,33,36,39,42,45,48,51,54,57,60,63,66,69,72,75,78,81,84,87,90,93,96,99,102,105,108,111,114,117,120]]
def K123 : List Nat := [41,3]
theorem cert123 : check 123 C123 K123 := by decide
theorem result123 : EqualChromaticClique 123 := check_sound (by decide) cert123
def C124 : List (List Nat) := [[62,31,93],[2,4,6,8,10,12,14,16,18,20,22,24,26,28,30,32,34,36,38,40,42,44,46,48,50,52,54,56,58,60,64,66,68,70,72,74,76,78,80,82,84,86,88,90,92,94,96,98,100,102,104,106,108,110,112,114,116,118,120,122]]
def K124 : List Nat := [62,4]
theorem cert124 : check 124 C124 K124 := by decide
theorem result124 : EqualChromaticClique 124 := check_sound (by decide) cert124
def C125 : List (List Nat) := [[25],[50],[75],[100],[5,10,15,20,30,35,40,45,55,60,65,70,80,85,90,95,105,110,115,120]]
def K125 : List Nat := [25,50,75,100,5]
theorem cert125 : check 125 C125 K125 := by decide
theorem result125 : EqualChromaticClique 125 := check_sound (by decide) cert125
def C126 : List (List Nat) := [[42,2,4,8,10,14,16,20,22,26,28,32,34,38,40,44,46,50,52,56,58,62,64,68,70,74,76,80,82,86,88,92,94,98,100,104,106,110,112,116,118,122,124],[84],[3,7,9,15,21,27,33,35,39,45,49,51,57,63,69,75,77,81,87,91,93,99,105,111,117,119,123],[6,12,18,24,30,36,48,54,60,66,72,78,90,96,102,108,114,120]]
def K126 : List Nat := [42,84,63,18]
theorem cert126 : check 126 C126 K126 := by decide
theorem result126 : EqualChromaticClique 126 := check_sound (by decide) cert126
def C127 : List (List Nat) := []
def K127 : List Nat := []
theorem cert127 : check 127 C127 K127 := by decide
theorem result127 : EqualChromaticClique 127 := check_sound (by decide) cert127
def C128 : List (List Nat) := [[16],[32],[48],[64],[80],[96],[112],[2,4,6,8,10,12,14,18,20,22,24,26,28,30,34,36,38,40,42,44,46,50,52,54,56,58,60,62,66,68,70,72,74,76,78,82,84,86,88,90,92,94,98,100,102,104,106,108,110,114,116,118,120,122,124,126]]
def K128 : List Nat := [16,32,48,64,80,96,112,8]
theorem cert128 : check 128 C128 K128 := by decide
theorem result128 : EqualChromaticClique 128 := check_sound (by decide) cert128
def C129 : List (List Nat) := [[43,86],[3,6,9,12,15,18,21,24,27,30,33,36,39,42,45,48,51,54,57,60,63,66,69,72,75,78,81,84,87,90,93,96,99,102,105,108,111,114,117,120,123,126]]
def K129 : List Nat := [43,3]
theorem cert129 : check 129 C129 K129 := by decide
theorem result129 : EqualChromaticClique 129 := check_sound (by decide) cert129
def C130 : List (List Nat) := [[5,13,15,25,35,39,45,55,65,75,85,91,95,105,115,117,125],[2,4,6,8,12,14,16,18,22,24,26,28,32,34,36,38,42,44,46,48,52,54,56,58,62,64,66,68,72,74,76,78,82,84,86,88,92,94,96,98,102,104,106,108,112,114,116,118,122,124,126,128],[10,20,30,40,50,60,70,80,90,100,110,120]]
def K130 : List Nat := [65,26,10]
theorem cert130 : check 130 C130 K130 := by decide
theorem result130 : EqualChromaticClique 130 := check_sound (by decide) cert130
def C131 : List (List Nat) := []
def K131 : List Nat := []
theorem cert131 : check 131 C131 K131 := by decide
theorem result131 : EqualChromaticClique 131 := check_sound (by decide) cert131
def C132 : List (List Nat) := [[66,3,9,11,15,21,27,33,39,45,51,55,57,63,69,75,77,81,87,93,99,105,111,117,121,123,129],[2,4,8,10,14,16,20,22,26,28,32,34,38,40,44,46,50,52,56,58,62,64,68,70,74,76,80,82,86,88,92,94,98,100,104,106,110,112,116,118,122,124,128,130],[6,12,18,24,30,36,42,48,54,60,72,78,84,90,96,102,108,114,120,126]]
def K132 : List Nat := [66,44,12]
theorem cert132 : check 132 C132 K132 := by decide
theorem result132 : EqualChromaticClique 132 := check_sound (by decide) cert132
def C133 : List (List Nat) := [[19,38,57,76,95,114],[7,14,21,28,35,42,49,56,63,70,77,84,91,98,105,112,119,126]]
def K133 : List Nat := [19,7]
theorem cert133 : check 133 C133 K133 := by decide
theorem result133 : EqualChromaticClique 133 := check_sound (by decide) cert133
def C134 : List (List Nat) := [[67],[2,4,6,8,10,12,14,16,18,20,22,24,26,28,30,32,34,36,38,40,42,44,46,48,50,52,54,56,58,60,62,64,66,68,70,72,74,76,78,80,82,84,86,88,90,92,94,96,98,100,102,104,106,108,110,112,114,116,118,120,122,124,126,128,130,132]]
def K134 : List Nat := [67,2]
theorem cert134 : check 134 C134 K134 := by decide
theorem result134 : EqualChromaticClique 134 := check_sound (by decide) cert134
def C135 : List (List Nat) := [[45],[90],[3,5,6,10,12,15,20,21,24,25,30,33,35,39,40,42,48,50,51,55,57,60,65,66,69,70,75,78,80,84,85,87,93,95,96,100,102,105,110,111,114,115,120,123,125,129,130,132],[9,18,27,36,54,63,72,81,99,108,117,126]]
def K135 : List Nat := [45,90,15,27]
theorem cert135 : check 135 C135 K135 := by decide
theorem result135 : EqualChromaticClique 135 := check_sound (by decide) cert135
def C136 : List (List Nat) := [[68],[2,6,10,14,17,18,22,26,30,34,38,42,46,50,51,54,58,62,66,70,74,78,82,85,86,90,94,98,102,106,110,114,118,119,122,126,130,134],[4,8,12,16,20,24,28,32,36,40,44,48,52,56,60,64,72,76,80,84,88,92,96,100,104,108,112,116,120,124,128,132]]
def K136 : List Nat := [68,34,8]
theorem cert136 : check 136 C136 K136 := by decide
theorem result136 : EqualChromaticClique 136 := check_sound (by decide) cert136
def C137 : List (List Nat) := []
def K137 : List Nat := []
theorem cert137 : check 137 C137 K137 := by decide
theorem result137 : EqualChromaticClique 137 := check_sound (by decide) cert137
def C138 : List (List Nat) := [[3,9,15,21,23,27,33,39,45,51,57,63,69,75,81,87,93,99,105,111,115,117,123,129,135],[2,4,8,10,14,16,20,22,26,28,32,34,38,40,44,46,50,52,56,58,62,64,68,70,74,76,80,82,86,88,92,94,98,100,104,106,110,112,116,118,122,124,128,130,134,136],[6,12,18,24,30,36,42,48,54,60,66,72,78,84,90,96,102,108,114,120,126,132]]
def K138 : List Nat := [69,46,6]
theorem cert138 : check 138 C138 K138 := by decide
theorem result138 : EqualChromaticClique 138 := check_sound (by decide) cert138
def C139 : List (List Nat) := []
def K139 : List Nat := []
theorem cert139 : check 139 C139 K139 := by decide
theorem result139 : EqualChromaticClique 139 := check_sound (by decide) cert139
def C140 : List (List Nat) := [[70,5,7,15,21,25,35,45,49,55,63,65,75,77,85,91,95,105,115,119,125,133,135],[2,4,6,8,12,14,16,18,22,24,26,28,32,34,36,38,42,44,46,48,52,54,56,58,62,64,66,68,72,74,76,78,82,84,86,88,92,94,96,98,102,104,106,108,112,114,116,118,122,124,126,128,132,134,136,138],[10,20,30,40,50,60,80,90,100,110,120,130]]
def K140 : List Nat := [70,28,20]
theorem cert140 : check 140 C140 K140 := by decide
theorem result140 : EqualChromaticClique 140 := check_sound (by decide) cert140
def C141 : List (List Nat) := [[47,94],[3,6,9,12,15,18,21,24,27,30,33,36,39,42,45,48,51,54,57,60,63,66,69,72,75,78,81,84,87,90,93,96,99,102,105,108,111,114,117,120,123,126,129,132,135,138]]
def K141 : List Nat := [47,3]
theorem cert141 : check 141 C141 K141 := by decide
theorem result141 : EqualChromaticClique 141 := check_sound (by decide) cert141
def C142 : List (List Nat) := [[71],[2,4,6,8,10,12,14,16,18,20,22,24,26,28,30,32,34,36,38,40,42,44,46,48,50,52,54,56,58,60,62,64,66,68,70,72,74,76,78,80,82,84,86,88,90,92,94,96,98,100,102,104,106,108,110,112,114,116,118,120,122,124,126,128,130,132,134,136,138,140]]
def K142 : List Nat := [71,2]
theorem cert142 : check 142 C142 K142 := by decide
theorem result142 : EqualChromaticClique 142 := check_sound (by decide) cert142
def C143 : List (List Nat) := [[13,26,39,52,65,78,91,104,117,130],[11,22,33,44,55,66,77,88,99,110,121,132]]
def K143 : List Nat := [13,11]
theorem cert143 : check 143 C143 K143 := by decide
theorem result143 : EqualChromaticClique 143 := check_sound (by decide) cert143
def C144 : List (List Nat) := [[12],[24],[36,2,3,6,9,10,14,15,18,21,22,26,27,30,33,34,38,39,42,45,46,50,51,54,57,58,62,63,66,69,70,74,75,78,81,82,86,87,90,93,94,98,99,102,105,106,110,111,114,117,118,122,123,126,129,130,134,135,138,141,142],[48,4,8,16,20,28,32,40,44,52,56,64,68,76,80,88,92,100,104,112,116,124,128,136,140],[60],[72],[84],[96],[108],[120],[132]]
def K144 : List Nat := [12,24,36,48,60,72,84,96,108,120,132]
theorem cert144 : check 144 C144 K144 := by decide
theorem result144 : EqualChromaticClique 144 := check_sound (by decide) cert144
def C145 : List (List Nat) := [[29,58,87,116],[5,10,15,20,25,30,35,40,45,50,55,60,65,70,75,80,85,90,95,100,105,110,115,120,125,130,135,140]]
def K145 : List Nat := [29,5]
theorem cert145 : check 145 C145 K145 := by decide
theorem result145 : EqualChromaticClique 145 := check_sound (by decide) cert145
def C146 : List (List Nat) := [[73],[2,4,6,8,10,12,14,16,18,20,22,24,26,28,30,32,34,36,38,40,42,44,46,48,50,52,54,56,58,60,62,64,66,68,70,72,74,76,78,80,82,84,86,88,90,92,94,96,98,100,102,104,106,108,110,112,114,116,118,120,122,124,126,128,130,132,134,136,138,140,142,144]]
def K146 : List Nat := [73,2]
theorem cert146 : check 146 C146 K146 := by decide
theorem result146 : EqualChromaticClique 146 := check_sound (by decide) cert146
def C147 : List (List Nat) := [[21,3,6,9,12,15,18,24,27,30,33,36,39,45,48,51,54,57,60,66,69,72,75,78,81,87,90,93,96,99,102,108,111,114,117,120,123,129,132,135,138,141,144],[42],[63],[84],[105],[126],[7,14,28,35,49,56,70,77,91,98,112,119,133,140]]
def K147 : List Nat := [21,42,63,84,105,126,49]
theorem cert147 : check 147 C147 K147 := by decide
theorem result147 : EqualChromaticClique 147 := check_sound (by decide) cert147
def C148 : List (List Nat) := [[74,37,111],[2,4,6,8,10,12,14,16,18,20,22,24,26,28,30,32,34,36,38,40,42,44,46,48,50,52,54,56,58,60,62,64,66,68,70,72,76,78,80,82,84,86,88,90,92,94,96,98,100,102,104,106,108,110,112,114,116,118,120,122,124,126,128,130,132,134,136,138,140,142,144,146]]
def K148 : List Nat := [74,4]
theorem cert148 : check 148 C148 K148 := by decide
theorem result148 : EqualChromaticClique 148 := check_sound (by decide) cert148
def C149 : List (List Nat) := []
def K149 : List Nat := []
theorem cert149 : check 149 C149 K149 := by decide
theorem result149 : EqualChromaticClique 149 := check_sound (by decide) cert149
def C150 : List (List Nat) := [[30,6,12,18,24,36,42,48,54,66,72,78,84,96,102,108,114,126,132,138,144],[60],[90],[120],[3,5,9,15,21,25,27,33,35,39,45,51,55,57,63,65,69,75,81,85,87,93,95,99,105,111,115,117,123,125,129,135,141,145,147],[2,4,8,10,14,16,20,22,26,28,32,34,38,40,44,46,50,52,56,58,62,64,68,70,74,76,80,82,86,88,92,94,98,100,104,106,110,112,116,118,122,124,128,130,134,136,140,142,146,148]]
def K150 : List Nat := [30,60,90,120,75,50]
theorem cert150 : check 150 C150 K150 := by decide
theorem result150 : EqualChromaticClique 150 := check_sound (by decide) cert150
theorem range101_150 (n : Nat) (hl : 101 ≤ n) (hh : n ≤ 150) : EqualChromaticClique n := by
  have h : n = 101 ∨ n = 102 ∨ n = 103 ∨ n = 104 ∨ n = 105 ∨ n = 106 ∨ n = 107 ∨ n = 108 ∨ n = 109 ∨ n = 110 ∨ n = 111 ∨ n = 112 ∨ n = 113 ∨ n = 114 ∨ n = 115 ∨ n = 116 ∨ n = 117 ∨ n = 118 ∨ n = 119 ∨ n = 120 ∨ n = 121 ∨ n = 122 ∨ n = 123 ∨ n = 124 ∨ n = 125 ∨ n = 126 ∨ n = 127 ∨ n = 128 ∨ n = 129 ∨ n = 130 ∨ n = 131 ∨ n = 132 ∨ n = 133 ∨ n = 134 ∨ n = 135 ∨ n = 136 ∨ n = 137 ∨ n = 138 ∨ n = 139 ∨ n = 140 ∨ n = 141 ∨ n = 142 ∨ n = 143 ∨ n = 144 ∨ n = 145 ∨ n = 146 ∨ n = 147 ∨ n = 148 ∨ n = 149 ∨ n = 150 := by omega
  rcases h with h101 | h102 | h103 | h104 | h105 | h106 | h107 | h108 | h109 | h110 | h111 | h112 | h113 | h114 | h115 | h116 | h117 | h118 | h119 | h120 | h121 | h122 | h123 | h124 | h125 | h126 | h127 | h128 | h129 | h130 | h131 | h132 | h133 | h134 | h135 | h136 | h137 | h138 | h139 | h140 | h141 | h142 | h143 | h144 | h145 | h146 | h147 | h148 | h149 | h150
  · subst n; exact result101
  · subst n; exact result102
  · subst n; exact result103
  · subst n; exact result104
  · subst n; exact result105
  · subst n; exact result106
  · subst n; exact result107
  · subst n; exact result108
  · subst n; exact result109
  · subst n; exact result110
  · subst n; exact result111
  · subst n; exact result112
  · subst n; exact result113
  · subst n; exact result114
  · subst n; exact result115
  · subst n; exact result116
  · subst n; exact result117
  · subst n; exact result118
  · subst n; exact result119
  · subst n; exact result120
  · subst n; exact result121
  · subst n; exact result122
  · subst n; exact result123
  · subst n; exact result124
  · subst n; exact result125
  · subst n; exact result126
  · subst n; exact result127
  · subst n; exact result128
  · subst n; exact result129
  · subst n; exact result130
  · subst n; exact result131
  · subst n; exact result132
  · subst n; exact result133
  · subst n; exact result134
  · subst n; exact result135
  · subst n; exact result136
  · subst n; exact result137
  · subst n; exact result138
  · subst n; exact result139
  · subst n; exact result140
  · subst n; exact result141
  · subst n; exact result142
  · subst n; exact result143
  · subst n; exact result144
  · subst n; exact result145
  · subst n; exact result146
  · subst n; exact result147
  · subst n; exact result148
  · subst n; exact result149
  · subst n; exact result150
end TLMC2222
