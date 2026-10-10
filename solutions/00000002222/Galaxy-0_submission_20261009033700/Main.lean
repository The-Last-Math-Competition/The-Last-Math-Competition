import Cert00
import Cert01
import Cert02
import Cert03
import Cert04
import Cert05
import Cert06
import Cert07
import Cert08
import Cert09
import Cert10
import Cert11
import Cert12
import Cert13
import Cert14
import Cert15
import Cert16
import Cert17
import Cert18
import Cert19
namespace TLMC2222
theorem conjecture2222 (n : Nat) (hn : 0 < n) (hmax : n ≤ 1000) : EqualChromaticClique n := by
  by_cases h50 : n ≤ 50
  · exact range1_50 n (by omega) h50
  by_cases h100 : n ≤ 100
  · exact range51_100 n (by omega) h100
  by_cases h150 : n ≤ 150
  · exact range101_150 n (by omega) h150
  by_cases h200 : n ≤ 200
  · exact range151_200 n (by omega) h200
  by_cases h250 : n ≤ 250
  · exact range201_250 n (by omega) h250
  by_cases h300 : n ≤ 300
  · exact range251_300 n (by omega) h300
  by_cases h350 : n ≤ 350
  · exact range301_350 n (by omega) h350
  by_cases h400 : n ≤ 400
  · exact range351_400 n (by omega) h400
  by_cases h450 : n ≤ 450
  · exact range401_450 n (by omega) h450
  by_cases h500 : n ≤ 500
  · exact range451_500 n (by omega) h500
  by_cases h550 : n ≤ 550
  · exact range501_550 n (by omega) h550
  by_cases h600 : n ≤ 600
  · exact range551_600 n (by omega) h600
  by_cases h650 : n ≤ 650
  · exact range601_650 n (by omega) h650
  by_cases h700 : n ≤ 700
  · exact range651_700 n (by omega) h700
  by_cases h750 : n ≤ 750
  · exact range701_750 n (by omega) h750
  by_cases h800 : n ≤ 800
  · exact range751_800 n (by omega) h800
  by_cases h850 : n ≤ 850
  · exact range801_850 n (by omega) h850
  by_cases h900 : n ≤ 900
  · exact range851_900 n (by omega) h900
  by_cases h950 : n ≤ 950
  · exact range901_950 n (by omega) h950
  exact range951_1000 n (by omega) hmax
#print axioms conjecture2222
end TLMC2222
