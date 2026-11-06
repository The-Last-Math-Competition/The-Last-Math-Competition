/-
The Higman–Sims graph, built from the Steiner system S(3,6,22), together with a
kernel-checked proof that it is strongly regular with parameters (100, 22, 0, 6).
-/
import Mathlib

namespace Conjecture2160

/-- The 77 hexads of the Steiner system S(3,6,22), each encoded as a 22-bit mask over the
points `0, …, 21` (bit `p` set iff point `p` lies in the hexad). -/
def hexadMasks : List ℕ :=
  [1319, 4536, 11289, 14470, 17348, 35041, 46400,
  52738, 68148, 74506, 88136, 114961, 137985, 140960,
  155715, 164440, 184356, 196749, 201746, 263370, 266325,
  279081, 297228, 303154, 353284, 365184, 411792, 459104,
  528994, 540702, 545921, 551200, 565765, 598224, 623656,
  658500, 688514, 788240, 854019, 929800, 1049235, 1054220,
  1066096, 1106056, 1117568, 1126433, 1146950, 1181738, 1188116,
  1321536, 1331458, 1475585, 1573193, 1611792, 1786368, 1835172,
  2099538, 2105452, 2126352, 2131092, 2134027, 2164289, 2179234,
  2245896, 2336768, 2366496, 2367873, 2490886, 2624136, 2691332,
  2752561, 2932800, 3164165, 3179296, 3281088, 3473432, 3679234]

/-- The `b`-th hexad (as a 22-bit mask). -/
def hexad (b : ℕ) : ℕ := hexadMasks.getD b 0

/-- Sanity check on the data: there are 77 hexads, each has exactly 6 points, and every
3 distinct points of `{0, …, 21}` lie in exactly one hexad, i.e. the hexads form a
Steiner system S(3,6,22). -/
theorem hexads_steiner :
    hexadMasks.length = 77 ∧
    (∀ h ∈ hexadMasks, ((List.range 22).filter (fun p => h.testBit p)).length = 6) ∧
    (∀ a ∈ List.range 22, ∀ b ∈ List.range 22, ∀ c ∈ List.range 22, a ≠ b → b ≠ c → a ≠ c →
      (hexadMasks.filter (fun h => h.testBit a && h.testBit b && h.testBit c)).length = 1) := by
  decide +kernel

/-- Adjacency on the vertex labels `0, …, 99`: `0` is `∞`, `1 + p` is the point `p`
(`0 ≤ p ≤ 21`) and `23 + b` is the hexad `hexad b` (`0 ≤ b ≤ 76`). -/
def hsAdjNat (i j : ℕ) : Bool :=
  if i = j then false
  else if i = 0 then decide (1 ≤ j ∧ j ≤ 22)
  else if i ≤ 22 then decide (j = 0) || (decide (23 ≤ j) && (hexad (j - 23)).testBit (i - 1))
  else (decide (1 ≤ j ∧ j ≤ 22) && (hexad (i - 23)).testBit (j - 1)) ||
    (decide (23 ≤ j) && decide (hexad (i - 23) &&& hexad (j - 23) = 0))

/-- Precomputed neighbourhood bitmasks (row `i` has bit `j` set iff `i ~ j`); they are
checked against `hsAdjNat` in `rowsAgree_eq`, so they are only a computational aid. -/
def rowMasks : List ℕ :=
  [8388606, 50165642785848630568124678145, 635112212876827378626743762945, 45810131284366791984048766977,
  319476820776977546264908398593, 326824106355561842502765903873, 89481366134669521193856401409, 178284564987789339214858944513,
  161594998918945832640578584577, 84876918140584272929539227649, 82963899163829094106452197377, 634236353986758212630156935169,
  42554874924353222320041492481, 163729744774502266634747510785, 634602646873349511211663753217, 59539757287193616055665688577,
  99204547869745906732020793345, 322077333309719733399348838401, 169830072691909422282614767617, 338886421050465831932460531713,
  670964067985875173589792063489, 1228037123424783667977663807489, 1267649995765319594182115852289, 497809287623701997530476710478,
  694658622677608760413530366832, 263720377376804918747931367474, 425948295402056899787917127948, 961115465336874928031391582088,
  957007602417553175162491310530, 370183211911864646821275069056, 490844777173875686263301970948, 812794744641979298747733120104,
  228095684657585633235956811284, 724819052197961539569089425552, 796306447353902400437322220066, 970590023987715947144654632450,
  381295931343498604601472732480, 403883151476770452791737237638, 679358594305322826494640456880, 953852790207035640154729848904,
  733173100344345425125906448666, 141745688230589977856552871972, 133854913929347339637934786964, 715800294608962067670378225834,
  797393646628737316620333515858, 802245743204982685783929983512, 205594949647919546134428205156, 250074278332302834364999976968,
  683422127684625631723844740352, 718035484614015643529538998560, 675932262070662592820170064576, 357382672266487518413097804996,
  238787051944837234183988346940, 397535317358685549835672660226, 476640784555252771643435569728, 475795132246793904994682749962,
  120476741012752800405267825056, 199930355196644584967806060624, 396810567298279781238243072136, 356859190987438329600658440964,
  198274716888998030660326657568, 237770323766296102296868229126, 118905713160912897575457939472, 25301608483777922359241999654,
  30523563559514099845127220248, 9448964213638278004051314912, 16422652800305313645122928912, 30961799170804835727385434880,
  23603672167088546362700226626, 13387644532204613246765957260, 25404367174652263598605471828, 22660105565318129922194293288,
  14985844460677033854417523840, 12559530340516815896868069892, 7470557102405428392338720770, 1748106735163812138577822354,
  1993518676545813446829092896, 944775528028951448223384576, 264150291585799152085762376, 472628831191237841130148,
  255168632478729322381528, 360821629897666692441120, 204544437228194253310248, 460616732574059163885590,
  390854824767579761020034, 139334346899714725806404, 383408768741858561264144, 349520852051501521522688,
  191929837767187459749952, 228500257945039357362946, 113890441105489280107532, 31617720691044352267536,
  24912328527336097063432, 14997203393735451476066, 4012166839440015720576, 6560977546414952458,
  7292048122964936256, 3661690404587446656, 929994115421700144, 2033884337293316]

/-- Population count of the lowest `f` bits. -/
def pc : ℕ → ℕ → ℕ
  | 0, _ => 0
  | f + 1, m => m % 2 + pc f (m / 2)

def rowsAgree : Bool :=
  (List.range 100).all fun i => (List.range 100).all fun j =>
    (rowMasks.getD i 0).testBit j == hsAdjNat i j

def srgCheck : Bool :=
  (List.range 100).all fun i => (List.range 100).all fun j =>
    pc 100 (rowMasks.getD i 0 &&& rowMasks.getD j 0) ==
      (if i = j then 22 else if hsAdjNat i j then 0 else 6)

set_option maxRecDepth 100000 in
theorem rowsAgree_eq : rowsAgree = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem srgCheck_eq : srgCheck = true := by decide +kernel


theorem pc_eq_countP (n m : ℕ) : pc n m = (List.range n).countP (fun k => m.testBit k) := by
  induction n generalizing m with
  | zero => simp [pc]
  | succ n ih =>
    rw [pc, ih, List.range_succ_eq_map, List.countP_cons, List.countP_map]
    have h1 : (fun k => m.testBit k) ∘ Nat.succ = fun k => (m / 2).testBit k := by
      funext k; simp [Nat.testBit_succ]
    rw [h1]
    have h2 : m % 2 = if m.testBit 0 = true then 1 else 0 := by
      rcases Nat.mod_two_eq_zero_or_one m with h | h <;> simp [Nat.testBit_zero, h]
    omega

theorem card_filter_fin_eq_countP (n : ℕ) (P : ℕ → Bool) :
    (Finset.univ.filter (fun u : Fin n => P u = true)).card = (List.range n).countP P := by
  rw [Finset.card_filter, Fin.sum_univ_eq_sum_range (fun i => if P i = true then 1 else 0) n]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, List.range_succ, List.countP_append]
    simp [List.countP_cons]

def symmCheck : Bool :=
  (List.range 100).all fun i => (List.range 100).all fun j => hsAdjNat i j == hsAdjNat j i

set_option maxRecDepth 100000 in
theorem symmCheck_eq : symmCheck = true := by decide +kernel

theorem hsAdjNat_symm (i j : Fin 100) (h : hsAdjNat i j = true) : hsAdjNat j i = true := by
  have := symmCheck_eq
  simp only [symmCheck, List.all_eq_true, List.mem_range, beq_iff_eq] at this
  rw [← this i i.2 j j.2]; exact h

/-- The Higman–Sims graph on the vertex set `Fin 100`: vertex `0` is the extra point `∞`,
vertices `1, …, 22` are the 22 points of S(3,6,22) and vertices `23, …, 99` are its 77 hexads.
`∞` is adjacent to every point, a point is adjacent to the hexads containing it, and two hexads
are adjacent iff they are disjoint. -/
def higmanSims : SimpleGraph (Fin 100) where
  Adj i j := hsAdjNat i j = true
  symm i j h := hsAdjNat_symm i j h
  loopless := ⟨fun i h => by simp [hsAdjNat] at h⟩

instance : DecidableRel higmanSims.Adj := fun i j =>
  inferInstanceAs (Decidable (hsAdjNat i j = true))

theorem row_testBit (i j : Fin 100) : (rowMasks.getD i 0).testBit j = hsAdjNat i j := by
  have := rowsAgree_eq
  simp only [rowsAgree, List.all_eq_true, List.mem_range, beq_iff_eq] at this
  exact this i i.2 j j.2

theorem row_pc (i j : Fin 100) : pc 100 (rowMasks.getD i 0 &&& rowMasks.getD j 0) =
    (if (i : ℕ) = j then 22 else if hsAdjNat i j then 0 else 6) := by
  have := srgCheck_eq
  simp only [srgCheck, List.all_eq_true, List.mem_range, beq_iff_eq] at this
  exact this i i.2 j j.2

theorem card_common (v w : Fin 100) :
    (Finset.univ.filter (fun u => higmanSims.Adj v u ∧ higmanSims.Adj w u)).card =
      (if (v : ℕ) = w then 22 else if hsAdjNat v w then 0 else 6) := by
  rw [← row_pc, pc_eq_countP, ← card_filter_fin_eq_countP]
  congr 1
  apply Finset.filter_congr
  intro u _
  rw [Nat.testBit_land, Bool.and_eq_true, row_testBit, row_testBit]
  rfl

theorem higmanSims_isSRG : higmanSims.IsSRGWith 100 22 0 6 where
  card := by simp
  regular v := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]
    have := card_common v v
    simp only [and_self] at this
    exact this
  of_adj v w h := by
    have := card_common v w
    have hvw : (v : ℕ) ≠ w := fun e => higmanSims.ne_of_adj h (Fin.ext e)
    simp only [if_neg hvw, show hsAdjNat v w = true from h, if_true] at this
    rw [← this, ← Set.toFinset_card]
    congr 1
    ext u; simp [SimpleGraph.mem_commonNeighbors]
  of_not_adj v w hne h := by
    have := card_common v w
    have hvw : (v : ℕ) ≠ w := fun e => hne (Fin.ext e)
    simp only [if_neg hvw, show hsAdjNat v w = false from by simpa [higmanSims] using h, Bool.false_eq_true, if_false] at this
    rw [← this, ← Set.toFinset_card]
    congr 1
    ext u; simp [SimpleGraph.mem_commonNeighbors]

end Conjecture2160
