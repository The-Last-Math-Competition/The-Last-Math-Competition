import Mathlib.GroupTheory.FreeGroup.CyclicallyReduced
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.Analysis.Subadditive
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Group

/-! Genuine commutator lengths and Brooks word counts. The precise published
projective Gamma(2) lattice identification is an external geometric boundary,
not an added premise or a lattice/rank label in this formalization. -/

noncomputable section
open scoped commutatorElement
open Filter Topology
namespace TLMC1158
attribute [local instance] Classical.propDecidable

section Length
variable {G H : Type*} [Group G] [Group H]

def commProduct (L : List (G × G)) : G :=
  (L.map fun p => ⁅p.1, p.2⁆).prod

theorem commProduct_append (L M : List (G × G)) :
    commProduct (L ++ M) = commProduct L * commProduct M := by
  simp [commProduct]

theorem commProduct_reverse_swap (L : List (G × G)) :
    commProduct (L.reverse.map Prod.swap) = (commProduct L)⁻¹ := by
  simp only [commProduct, List.map_map, List.map_reverse]
  simpa only [List.map_map, Function.comp_def, Prod.fst_swap, Prod.snd_swap, commutatorElement_inv]
    using (List.prod_inv_reverse (L.map fun p => ⁅p.1, p.2⁆)).symm

def commProducts (G : Type*) [Group G] : Subgroup G where
  carrier := {x | ∃ L : List (G × G), commProduct L = x}
  one_mem' := ⟨[], rfl⟩
  mul_mem' := by
    rintro x y ⟨L, rfl⟩ ⟨M, rfl⟩
    exact ⟨L ++ M, commProduct_append L M⟩
  inv_mem' := by
    rintro x ⟨L, rfl⟩
    exact ⟨L.reverse.map Prod.swap, commProduct_reverse_swap L⟩

theorem commProduct_mem (L : List (G × G)) : commProduct L ∈ commutator G := by
  induction L with
  | nil => exact (commutator G).one_mem
  | cons p L ih =>
    exact (commutator G).mul_mem
      (Subgroup.commutator_mem_commutator (Subgroup.mem_top p.1) (Subgroup.mem_top p.2)) ih

theorem commProducts_eq : commProducts G = commutator G := by
  apply le_antisymm
  · rintro x ⟨L, rfl⟩
    exact commProduct_mem L
  · rw [commutator_eq_closure]
    rw [Subgroup.closure_le]
    rintro x ⟨a, b, rfl⟩
    exact ⟨[(a,b)], by simp [commProduct]⟩

theorem length_witness_exists (x : commutator G) :
    ∃ n : ℕ, ∃ L : List (G × G), L.length = n ∧ commProduct L = x.1 := by
  have hx : x.1 ∈ commProducts G := by rw [commProducts_eq]; exact x.2
  obtain ⟨L, hL⟩ := hx
  exact ⟨L.length, L, rfl, hL⟩

def commutatorLength (x : commutator G) : ℕ := Nat.find (length_witness_exists x)

theorem commutatorLength_witness (x : commutator G) :
    ∃ L : List (G × G), L.length = commutatorLength x ∧ commProduct L = x.1 :=
  Nat.find_spec (length_witness_exists x)

theorem commutatorLength_le (x : commutator G) (L : List (G × G))
    (hL : commProduct L = x.1) : commutatorLength x ≤ L.length :=
  Nat.find_min' (length_witness_exists x) ⟨L, rfl, hL⟩

theorem commutatorLength_mul (x y : commutator G) :
    commutatorLength (x*y) ≤ commutatorLength x + commutatorLength y := by
  obtain ⟨L, hlenL, hL⟩ := commutatorLength_witness x
  obtain ⟨M, hlenM, hM⟩ := commutatorLength_witness y
  calc
    commutatorLength (x*y) ≤ (L++M).length :=
      commutatorLength_le _ _ (by simp [commProduct_append, hL, hM])
    _ = _ := by simp [hlenL, hlenM]

theorem cl_powers_subadditive (x : commutator G) :
    Subadditive (fun n : ℕ => (commutatorLength (x^n) : ℝ)) := by
  intro m n
  dsimp only
  have h := commutatorLength_mul (x^m) (x^n)
  rw [← pow_add] at h
  exact_mod_cast h

theorem cl_powers_bddBelow (x : commutator G) :
    BddBelow (Set.range fun n : ℕ => (commutatorLength (x^n) : ℝ) / n) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨n, rfl⟩
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

def stableCommutatorLength (x : commutator G) : ℝ := (cl_powers_subadditive x).lim

theorem stableCommutatorLength_tendsto (x : commutator G) :
    Tendsto (fun n : ℕ => (commutatorLength (x^n) : ℝ)/n) atTop
      (𝓝 (stableCommutatorLength x)) :=
  (cl_powers_subadditive x).tendsto_lim (cl_powers_bddBelow x)

theorem stableCommutatorLength_nonneg (x : commutator G) :
    0 ≤ stableCommutatorLength x := by
  exact ge_of_tendsto (stableCommutatorLength_tendsto x)
    (Filter.Eventually.of_forall fun n => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

theorem stableCommutatorLength_le (x : commutator G) :
    stableCommutatorLength x ≤ commutatorLength x := by
  change (cl_powers_subadditive x).lim ≤ _
  simpa only [pow_one,Nat.cast_one,div_one] using
    (cl_powers_subadditive x).lim_le_div (cl_powers_bddBelow x) (n:=1) (by decide)
end Length

abbrev Letter := Bool × Bool
abbrev F2 := FreeGroup Bool

def inverseLetter (x : Letter) : Letter := (x.1, !x.2)

def turn (x y : Letter) : ℤ :=
  if x = (false,true) ∧ y = (true,true) then 1
  else if x = (true,false) ∧ y = (false,false) then -1 else 0

theorem turn_bounds (x y : Letter) : -1 ≤ turn x y ∧ turn x y ≤ 1 := by
  unfold turn
  split_ifs <;> norm_num

theorem turn_inverse (x y : Letter) :
    turn (inverseLetter y) (inverseLetter x) = -turn x y := by
  rcases x with ⟨i,s⟩; rcases y with ⟨j,t⟩
  cases i <;> cases s <;> cases j <;> cases t <;> decide

def wordCount : List Letter → ℤ
  | [] => 0
  | [_] => 0
  | x::y::L => turn x y + wordCount (y::L)

def boundary (L M : List Letter) : ℤ :=
  match L.getLast?, M.head? with
  | some x, some y => turn x y
  | _, _ => 0

theorem boundary_bounds (L M : List Letter) : -1 ≤ boundary L M ∧ boundary L M ≤ 1 := by
  unfold boundary
  split <;> first | exact turn_bounds _ _ | norm_num

theorem wordCount_append (L M : List Letter) :
    wordCount (L++M) = wordCount L + wordCount M + boundary L M := by
  induction L with
  | nil => simp [wordCount,boundary]
  | cons x L ih =>
    cases L with
    | nil => cases M <;> simp [wordCount,boundary,add_comm]
    | cons y L =>
      simpa [wordCount,boundary,add_assoc,add_left_comm,add_comm] using congrArg (turn x y + ·) ih

theorem boundary_inverse_snoc (L : List Letter) (x : Letter) :
    boundary [inverseLetter x] (FreeGroup.invRev L) = -boundary L [x] := by
  induction L using List.reverseRecOn with
  | nil => simp [boundary,FreeGroup.invRev]
  | append_singleton L y ih =>
    simp only [FreeGroup.invRev,List.map_append,List.map_cons,List.map_nil,
      List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,
      boundary,List.getLast?_append,List.getLast?_singleton,List.head?_cons]
    exact turn_inverse y x

theorem wordCount_invRev (L : List Letter) : wordCount (FreeGroup.invRev L) = -wordCount L := by
  induction L using List.reverseRecOn with
  | nil => simp [wordCount,FreeGroup.invRev]
  | append_singleton L x ih =>
    rw [FreeGroup.invRev_append]
    change wordCount ([inverseLetter x] ++ FreeGroup.invRev L) = -wordCount (L++[x])
    rw [wordCount_append,wordCount_append,ih,boundary_inverse_snoc]
    simp [wordCount,add_comm]

def brooks (g : F2) : ℤ := wordCount g.toWord

theorem brooks_inverse (g : F2) : brooks g⁻¹ = -brooks g := by
  simpa only [brooks,FreeGroup.toWord_inv] using wordCount_invRev g.toWord

theorem cancellation_decomposition (L M : List Letter)
    (hL : FreeGroup.IsReduced L) (hM : FreeGroup.IsReduced M) :
    ∃ A C B : List Letter, L = A++C ∧ M = FreeGroup.invRev C++B ∧
      FreeGroup.IsReduced (A++B) := by
  induction L using List.reverseRecOn generalizing M with
  | nil => exact ⟨[],[],M,rfl,rfl,hM⟩
  | append_singleton L x ih =>
    cases M with
    | nil => exact ⟨L++[x],[],[],by simp,by simp,by simpa using hL⟩
    | cons y M =>
      by_cases h : x.1 = y.1 ∧ x.2 = !y.2
      · have hy : y = inverseLetter x := by
          apply Prod.ext
          · exact h.1.symm
          simpa [inverseLetter] using congrArg Bool.not h.2.symm
        have hl : FreeGroup.IsReduced L := List.IsChain.left_of_append hL
        obtain ⟨A,C,B,hA,hB,hred⟩ := ih M hl hM.tail
        refine ⟨A,C++[x],B,?_,?_,hred⟩
        · simpa [List.append_assoc] using congrArg (· ++ [x]) hA
        · simpa [FreeGroup.invRev_append,FreeGroup.invRev,inverseLetter,hy,
            List.append_assoc] using congrArg (y :: ·) hB
      · refine ⟨L++[x],[],y::M,by simp,by simp,?_⟩
        apply List.IsChain.append hL hM
        intro a ha b hb
        rw [List.getLast?_append,List.getLast?_singleton] at ha
        change some x = some a at ha
        have ha' := Option.some.inj ha
        change some y = some b at hb
        have hb' := Option.some.inj hb
        subst a; subst b
        intro hxy
        cases hx : x.2 <;> cases hy : y.2 <;> simp_all

theorem brooks_defect (g h : F2) :
    -3 ≤ brooks (g*h) - brooks g - brooks h ∧
    brooks (g*h) - brooks g - brooks h ≤ 3 := by
  obtain ⟨A,C,B,hg,hh,hred⟩ := cancellation_decomposition g.toWord h.toWord
    FreeGroup.isReduced_toWord FreeGroup.isReduced_toWord
  have hprod : g*h = FreeGroup.mk (A++B) := by
    rw [← FreeGroup.mk_toWord (x:=g),← FreeGroup.mk_toWord (x:=h),hg,hh]
    simp only [← FreeGroup.mul_mk,← FreeGroup.inv_mk]
    group
  have hw : (g*h).toWord = A++B := by
    rw [hprod,FreeGroup.toWord_mk,hred.reduce_eq]
  dsimp only [brooks]
  rw [hw,hg,hh,wordCount_append,wordCount_append,wordCount_append,wordCount_invRev]
  obtain ⟨h1,h2⟩ := boundary_bounds A B
  obtain ⟨h3,h4⟩ := boundary_bounds A C
  obtain ⟨h5,h6⟩ := boundary_bounds (FreeGroup.invRev C) B
  constructor <;> linarith

theorem brooks_commutator (g h : F2) :
    -9 ≤ brooks ⁅g,h⁆ ∧ brooks ⁅g,h⁆ ≤ 9 := by
  obtain ⟨h1,h2⟩ := brooks_defect g h
  obtain ⟨h3,h4⟩ := brooks_defect (g*h) g⁻¹
  obtain ⟨h5,h6⟩ := brooks_defect (g*h*g⁻¹) h⁻¹
  rw [brooks_inverse] at h3 h4
  rw [brooks_inverse] at h5 h6
  simp only [commutatorElement_def]
  constructor <;> linarith

theorem brooks_commProduct (L : List (F2 × F2)) :
    -(12*(L.length:ℤ)) ≤ brooks (commProduct L) ∧
    brooks (commProduct L) ≤ 12*(L.length:ℤ) := by
  induction L with
  | nil => norm_num [commProduct,brooks,FreeGroup.toWord_one,wordCount]
  | cons p L ih =>
    change -(12*((L.length+1:ℕ):ℤ)) ≤ brooks (⁅p.1,p.2⁆ * commProduct L) ∧
      brooks (⁅p.1,p.2⁆ * commProduct L) ≤ 12*((L.length+1:ℕ):ℤ)
    obtain ⟨h1,h2⟩ := brooks_defect ⁅p.1,p.2⁆ (commProduct L)
    obtain ⟨h3,h4⟩ := brooks_commutator p.1 p.2
    push_cast
    constructor <;> linarith [ih.1,ih.2]

def occurrences (x y : Letter) (L : List Letter) : ℕ :=
  (L.zip L.tail).countP fun p => decide (p.1=x ∧ p.2=y)

theorem turn_eq_indicators (x y : Letter) : turn x y =
    (if x=(false,true) ∧ y=(true,true) then (1:ℤ) else 0) -
    (if x=(true,false) ∧ y=(false,false) then (1:ℤ) else 0) := by
  rcases x with ⟨i,s⟩; rcases y with ⟨j,t⟩
  cases i <;> cases s <;> cases j <;> cases t <;> decide

theorem wordCount_occurrences (L : List Letter) : wordCount L =
    (occurrences (false,true) (true,true) L : ℤ) -
    (occurrences (true,false) (false,false) L : ℤ) := by
  induction L with
  | nil => rfl
  | cons x L ih =>
    cases L with
    | nil => rfl
    | cons y L =>
      simp only [wordCount,turn_eq_indicators,occurrences,List.tail_cons,
        List.zip_cons_cons,List.countP_cons] at ih ⊢
      split_ifs <;> simp_all <;> omega

def a : F2 := FreeGroup.of false
def b : F2 := FreeGroup.of true
def c : F2 := ⁅a,b⁆
def commWord : List Letter := [(false,true),(true,true),(false,false),(true,false)]

theorem c_word : c.toWord = commWord := by decide

theorem commWord_cyclically_reduced : FreeGroup.IsCyclicallyReduced commWord := by
  simp [FreeGroup.IsCyclicallyReduced,FreeGroup.IsReduced,commWord]

theorem c_power_word (n : ℕ) :
    (c^n).toWord = (List.replicate n commWord).flatten := by
  rw [FreeGroup.toWord_pow,c_word]
  exact (commWord_cyclically_reduced.flatten_replicate n).isReduced.reduce_eq

theorem brooks_c_power (n : ℕ) : brooks (c^n) = n := by
  rw [brooks,c_power_word]
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ,List.flatten_cons,wordCount_append,ih]
    have hb : boundary commWord (List.replicate n commWord).flatten = 0 := by
      cases n <;> rfl
    rw [hb]
    norm_num [commWord,wordCount,turn,add_comm]

def cDerived : commutator F2 :=
  ⟨c,Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)⟩

theorem brooks_le_cl (x : commutator F2) :
    brooks x.1 ≤ 12*(commutatorLength x : ℤ) := by
  obtain ⟨L,hlen,hL⟩ := commutatorLength_witness x
  simpa [hlen,hL] using (brooks_commProduct L).2

theorem c_power_slope_lower (N n : ℕ) (hn : 0<n) :
    (N:ℝ)/12 ≤ (commutatorLength ((cDerived^N)^n) : ℝ)/n := by
  have hi : ((N*n:ℕ):ℤ) ≤ 12*(commutatorLength ((cDerived^N)^n) : ℤ) := by
    simpa only [Subgroup.coe_pow,cDerived,← pow_mul,brooks_c_power]
      using brooks_le_cl ((cDerived^N)^n)
  have hr : ((N*n:ℕ):ℝ) ≤ 12*(commutatorLength ((cDerived^N)^n) : ℝ) := by
    exact_mod_cast hi
  apply (div_le_div_iff₀ (by norm_num : (0:ℝ)<12) (Nat.cast_pos.mpr hn)).mpr
  norm_cast at hr ⊢
  nlinarith

theorem stable_c_power_lower (N : ℕ) :
    (N:ℝ)/12 ≤ stableCommutatorLength (cDerived^N) := by
  apply ge_of_tendsto (stableCommutatorLength_tendsto (cDerived^N))
  exact Filter.eventually_atTop.mpr ⟨1,fun n hn => c_power_slope_lower N n (by omega)⟩

theorem c_power_cl_upper (N : ℕ) : commutatorLength (cDerived^N) ≤ N := by
  have h := commutatorLength_le (cDerived^N) (List.replicate N (a,b))
    (by simp [commProduct,cDerived,c])
  simpa using h

theorem stable_c_power_upper (N : ℕ) : stableCommutatorLength (cDerived^N) ≤ N :=
  (stableCommutatorLength_le _).trans (by exact_mod_cast c_power_cl_upper N)

theorem stable_commutator_length_unbounded (C : ℝ) :
    ∃ N : ℕ, C < stableCommutatorLength (cDerived^N) ∧
      0 ≤ stableCommutatorLength (cDerived^N) ∧ stableCommutatorLength (cDerived^N) ≤ N := by
  obtain ⟨N,hN⟩ := exists_nat_gt (12*C)
  refine ⟨N,?_,stableCommutatorLength_nonneg _,stable_c_power_upper N⟩
  exact (by linarith : C < (N:ℝ)/12).trans_le (stable_c_power_lower N)

theorem stable_commutator_length_not_bddAbove :
    ¬BddAbove (Set.range (stableCommutatorLength (G:=F2))) := by
  rintro ⟨C,hC⟩
  obtain ⟨N,hN,_,_⟩ := stable_commutator_length_unbounded C
  exact (not_le_of_gt hN) (hC (Set.mem_range_self (cDerived^N)))

section Transport
variable {G H : Type*} [Group G] [Group H]

theorem commProduct_map (f : G →* H) (L : List (G × G)) :
    commProduct (L.map fun p => (f p.1,f p.2)) = f (commProduct L) := by
  induction L with
  | nil => exact f.map_one.symm
  | cons p L ih =>
    change ⁅f p.1,f p.2⁆ * commProduct (L.map fun p => (f p.1,f p.2)) =
      f (⁅p.1,p.2⁆ * commProduct L)
    rw [map_mul,map_commutatorElement,ih]

def derivedMap (f : G →* H) : commutator G →* commutator H where
  toFun x := ⟨f x.1,by
    obtain ⟨L,_,hL⟩ := commutatorLength_witness x
    rw [←hL,←commProduct_map]
    exact commProduct_mem _⟩
  map_one' := Subtype.ext f.map_one
  map_mul' x y := Subtype.ext (f.map_mul x.1 y.1)

def derivedEquiv (e : G ≃* H) : commutator G ≃* commutator H where
  toFun := derivedMap e.toMonoidHom
  invFun := derivedMap e.symm.toMonoidHom
  left_inv x := Subtype.ext (e.left_inv x.1)
  right_inv x := Subtype.ext (e.right_inv x.1)
  map_mul' := (derivedMap e.toMonoidHom).map_mul

theorem commutatorLength_map_le (f : G →* H) (x : commutator G) :
    commutatorLength (derivedMap f x) ≤ commutatorLength x := by
  obtain ⟨L,hlen,hL⟩ := commutatorLength_witness x
  calc
    commutatorLength (derivedMap f x) ≤ (L.map fun p => (f p.1,f p.2)).length :=
      commutatorLength_le _ _ (by rw [commProduct_map,hL]; rfl)
    _ = _ := by simp [hlen]

theorem commutatorLength_equiv (e : G ≃* H) (x : commutator G) :
    commutatorLength (derivedEquiv e x) = commutatorLength x := by
  apply le_antisymm (commutatorLength_map_le e.toMonoidHom x)
  have h := commutatorLength_map_le e.symm.toMonoidHom (derivedMap e.toMonoidHom x)
  have he : derivedMap e.symm.toMonoidHom (derivedMap e.toMonoidHom x) = x :=
    Subtype.ext (e.left_inv x.1)
  rw [he] at h
  exact h

theorem stableCommutatorLength_equiv (e : G ≃* H) (x : commutator G) :
    stableCommutatorLength (derivedEquiv e x) = stableCommutatorLength x := by
  have he : (fun n : ℕ => (commutatorLength ((derivedEquiv e x)^n) : ℝ)/n) =
      (fun n : ℕ => (commutatorLength (x^n) : ℝ)/n) := by
    funext n
    rw [←map_pow,commutatorLength_equiv]
  exact tendsto_nhds_unique (stableCommutatorLength_tendsto (derivedEquiv e x))
    (he ▸ stableCommutatorLength_tendsto x)

theorem isomorphic_group_unbounded (e : F2 ≃* G) (C : ℝ) :
    ∃ x : commutator G, C < stableCommutatorLength x ∧
      0 ≤ stableCommutatorLength x ∧ stableCommutatorLength x ≤ commutatorLength x := by
  obtain ⟨N,hN,_,_⟩ := stable_commutator_length_unbounded C
  refine ⟨derivedEquiv e (cDerived^N),?_,stableCommutatorLength_nonneg _,stableCommutatorLength_le _⟩
  simpa only [stableCommutatorLength_equiv] using hN
end Transport

def exponentMap : F2 →* Multiplicative (ℤ × ℤ) :=
  FreeGroup.lift fun i => Multiplicative.ofAdd (if i then (0,1) else (1,0))

theorem exponentMap_surjective : Function.Surjective exponentMap := by
  intro z
  refine ⟨a^z.toAdd.1*b^z.toAdd.2,?_⟩
  apply Multiplicative.toAdd.injective
  ext <;> simp [exponentMap,a,b]

def abelianCoordinates : Abelianization F2 →* Multiplicative (ℤ × ℤ) :=
  Abelianization.lift exponentMap

theorem abelianCoordinates_surjective : Function.Surjective abelianCoordinates := by
  intro z
  obtain ⟨g,hg⟩ := exponentMap_surjective z
  exact ⟨Abelianization.of g,hg⟩

theorem integer_square_not_cyclic : ¬IsCyclic (Multiplicative (ℤ × ℤ)) := by
  intro h
  have := h
  obtain ⟨z,hz⟩ := IsCyclic.exists_generator (α:=Multiplicative (ℤ × ℤ))
  obtain ⟨m,hm⟩ := hz (Multiplicative.ofAdd (1,0))
  obtain ⟨n,hn⟩ := hz (Multiplicative.ofAdd (0,1))
  have h1 := congrArg (fun w : Multiplicative (ℤ × ℤ) => w.toAdd.1) hm
  have h2 := congrArg (fun w : Multiplicative (ℤ × ℤ) => w.toAdd.2) hm
  have h3 := congrArg (fun w : Multiplicative (ℤ × ℤ) => w.toAdd.2) hn
  simp only [toAdd_zpow,zsmul_eq_mul] at h1 h2 h3
  have hm0 : m ≠ 0 := by intro hm; subst m; norm_num at h1
  have hz0 : z.toAdd.2 = 0 := (mul_eq_zero.mp h2).resolve_left hm0
  simp [hz0] at h3

theorem abelianization_not_cyclic : ¬IsCyclic (Abelianization F2) := by
  intro h
  have := h
  exact integer_square_not_cyclic (isCyclic_of_surjective abelianCoordinates abelianCoordinates_surjective)

theorem not_equiv_group_with_cyclic_abelianization (G : Type*) [Group G]
    [IsCyclic (Abelianization G)] : ¬Nonempty (F2 ≃* G) := by
  rintro ⟨e⟩
  exact abelianization_not_cyclic (isCyclic_of_surjective
    (e.abelianizationCongr.symm) e.abelianizationCongr.symm.surjective)

theorem complete_counterexample :
    (∀ g : F2, brooks g =
      (occurrences (false,true) (true,true) g.toWord : ℤ) -
      (occurrences (true,false) (false,false) g.toWord : ℤ)) ∧
    (∀ x : commutator F2, Tendsto
      (fun n : ℕ => (commutatorLength (x^n) : ℝ)/n) atTop
      (𝓝 (stableCommutatorLength x))) ∧
    (∀ C : ℝ, ∃ N : ℕ, C < stableCommutatorLength (cDerived^N) ∧
      0 ≤ stableCommutatorLength (cDerived^N) ∧ stableCommutatorLength (cDerived^N) ≤ N) ∧
    ¬BddAbove (Set.range (stableCommutatorLength (G:=F2))) ∧
    ¬IsCyclic (Abelianization F2) :=
  ⟨fun g => wordCount_occurrences g.toWord,stableCommutatorLength_tendsto,
    stable_commutator_length_unbounded,stable_commutator_length_not_bddAbove,
    abelianization_not_cyclic⟩

end TLMC1158
