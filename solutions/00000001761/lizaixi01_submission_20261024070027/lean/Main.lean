import Mathlib.RepresentationTheory.Semisimple
import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Nat.Find
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

set_option maxHeartbeats 0
set_option maxRecDepth 10000

noncomputable section

namespace TLMC1761

instance prime_three : Fact (Nat.Prime 3) := ⟨by decide⟩

abbrev K := ZMod 3
abbrev G := Equiv.Perm (Fin 3)
abbrev V := Fin 3 → K

def shape : YoungDiagram := YoungDiagram.ofRowLens [2,1] (by decide)

theorem shape_cells : shape.cells = {(0,0),(0,1),(1,0)} := by decide

theorem shape_card : shape.card = 3 := by rw [YoungDiagram.card,shape_cells];decide

theorem shape_mem (i j : ℕ) : (i,j) ∈ shape ↔ i+j ≤ 1 := by
  rw [← YoungDiagram.mem_cells,shape_cells]
  simp only [Finset.mem_insert,Finset.mem_singleton,Prod.mk.injEq]
  omega

def cell (i : Fin 3) : ℕ × ℕ := ![(0,0),(0,1),(1,0)] i

theorem cell_mem (i : Fin 3) : cell i ∈ shape := by
  fin_cases i <;> simp [cell,shape_mem]

theorem cell_bijective : Function.Bijective (fun i : Fin 3 => (⟨cell i,cell_mem i⟩ : shape)) := by
  constructor
  · intro i j h
    have hh := congrArg Subtype.val h
    fin_cases i <;> fin_cases j <;> simp_all [cell]
  · rintro ⟨⟨i,j⟩,h⟩
    have hs := (shape_mem i j).mp h
    have cases : (i=0 ∧ j=0) ∨ (i=0 ∧ j=1) ∨ (i=1 ∧ j=0) := by omega
    rcases cases with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
    · exact ⟨2,rfl⟩

def cellEquiv : Fin 3 ≃ shape := Equiv.ofBijective _ cell_bijective

abbrev Tableau := G

def tableauLabeling (t : Tableau) : shape ≃ Fin 3 := cellEquiv.symm.trans t

theorem tableauLabeling_cell (t : Tableau) (i : Fin 3) :
    tableauLabeling t (cellEquiv i)=t i := by simp [tableauLabeling]

theorem all_tableaux_represented (T : shape ≃ Fin 3) : ∃ t, tableauLabeling t=T := by
  refine ⟨cellEquiv.trans T,?_⟩
  ext c
  simp [tableauLabeling]

def rowEquivalent (s t : Tableau) : Prop := s 2=t 2

def rowLabels (t : Tableau) (r : ℕ) : Finset (Fin 3) :=
  (Finset.univ.filter (fun i => (cell i).1=r)).image t

theorem rowEquivalent_two (s t : Tableau) : rowEquivalent s t ↔
    rowLabels s 0=rowLabels t 0 ∧ rowLabels s 1=rowLabels t 1 := by
  revert s t
  simp only [rowEquivalent]
  decide

theorem rowLabels_large (t : Tableau) (r : ℕ) (hr : 2≤r) : rowLabels t r=∅ := by
  have hb : ∀ i : Fin 3, (cell i).1≤1 := by decide
  have he : Finset.univ.filter (fun i : Fin 3 => (cell i).1=r)=∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro i _ hi
    have := hb i
    omega
  simp [rowLabels,he]

theorem rowEquivalent_iff_all_rows (s t : Tableau) :
    rowEquivalent s t ↔ ∀ r, rowLabels s r=rowLabels t r := by
  rw [rowEquivalent_two]
  constructor
  · rintro ⟨h0,h1⟩ r
    rcases r with _ | (_ | r)
    · exact h0
    · exact h1
    · rw [rowLabels_large _ _ (by omega),rowLabels_large _ _ (by omega)]
  · intro h
    exact ⟨h 0,h 1⟩

def rowSetoid : Setoid Tableau where
  r := rowEquivalent
  iseqv := ⟨fun _ => rfl,fun h => h.symm,fun h k => h.trans k⟩

abbrev Tabloid := Quotient rowSetoid

def tabloid (t : Tableau) : Tabloid := Quotient.mk rowSetoid t

def bottomLabel : Tabloid → Fin 3 := Quotient.lift (fun t => t 2) (fun _ _ h => h)

theorem bottomLabel_tabloid (t : Tableau) : bottomLabel (tabloid t)=t 2 := rfl

def tabloidEquiv : Tabloid ≃ Fin 3 where
  toFun := bottomLabel
  invFun i := tabloid (Equiv.swap 2 i)
  left_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro t
    apply Quotient.sound
    change (Equiv.swap 2 (t 2)) 2=t 2
    simp
  right_inv i := by
    change (Equiv.swap 2 i) 2=i
    simp

def actTabloid (g : G) : Tabloid → Tabloid :=
  Quotient.map (fun t => g*t) (fun s t h => by
    change g (s 2)=g (t 2)
    exact congrArg g h)

theorem tabloid_action (g : G) (q : Tabloid) : bottomLabel (actTabloid g q)=g (bottomLabel q) := by
  refine Quotient.inductionOn q ?_
  intro t
  rfl

def basisVector (i : Fin 3) : V := Pi.single i 1

def ambient : Representation K G V where
  toFun g :=
    { toFun := fun v i => v (g⁻¹ i)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := by ext v i;simp
  map_mul' g h := by ext v i;simp

theorem ambient_apply (g : G) (v : V) (i : Fin 3) : ambient g v i=v (g⁻¹ i) := rfl

theorem ambient_basis (g : G) (i : Fin 3) : ambient g (basisVector i)=basisVector (g i) := by
  revert g i
  decide

def tabloidVector (q : Tabloid) : V := basisVector (bottomLabel q)

theorem tabloidVector_action (g : G) (q : Tabloid) :
    ambient g (tabloidVector q)=tabloidVector (actTabloid g q) := by
  simp only [tabloidVector,ambient_basis,tabloid_action]

def columnGroup (t : Tableau) : Subgroup G := MulAction.stabilizer G (t 1)

def columnLabels (t : Tableau) (c : ℕ) : Finset (Fin 3) :=
  (Finset.univ.filter (fun i => (cell i).2=c)).image t

theorem columnGroup_two (t : Tableau) (g : G) : g ∈ columnGroup t ↔
    (columnLabels t 0).image g=columnLabels t 0 ∧
    (columnLabels t 1).image g=columnLabels t 1 := by
  revert t g
  simp only [columnGroup,MulAction.mem_stabilizer_iff]
  decide

theorem columnLabels_large (t : Tableau) (c : ℕ) (hc : 2≤c) : columnLabels t c=∅ := by
  have hb : ∀ i : Fin 3, (cell i).2≤1 := by decide
  have he : Finset.univ.filter (fun i : Fin 3 => (cell i).2=c)=∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro i _ hi
    have := hb i
    omega
  simp [columnLabels,he]

theorem columnGroup_iff_all_columns (t : Tableau) (g : G) :
    g ∈ columnGroup t ↔ ∀ c, (columnLabels t c).image g=columnLabels t c := by
  rw [columnGroup_two]
  constructor
  · rintro ⟨h0,h1⟩ c
    rcases c with _ | (_ | c)
    · exact h0
    · exact h1
    · simp [columnLabels_large t (c+2) (by omega)]
  · intro h
    exact ⟨h 0,h 1⟩

def columnPerms (t : Tableau) : Finset G := Finset.univ.filter (fun g => g (t 1)=t 1)

theorem mem_columnPerms (t : Tableau) (g : G) : g ∈ columnPerms t ↔ g ∈ columnGroup t := by
  simp [columnPerms,columnGroup,MulAction.mem_stabilizer_iff]

def polytabloid (t : Tableau) : V :=
  ∑ g ∈ columnPerms t, ((Equiv.Perm.sign g : ℤ) : K) • basisVector ((g*t) 2)

theorem polytabloid_column_antisymmetrizer (t : Tableau) :
    polytabloid t=∑ g ∈ columnPerms t,
      ((Equiv.Perm.sign g : ℤ) : K) • tabloidVector (actTabloid g (tabloid t)) := by
  simp only [polytabloid,tabloidVector,tabloid_action,bottomLabel_tabloid,
    Equiv.Perm.coe_mul,Function.comp_apply]

theorem polytabloid_formula (t : Tableau) : polytabloid t=basisVector (t 2)-basisVector (t 0) := by
  revert t
  decide

theorem polytabloid_action (g : G) (t : Tableau) :
    ambient g (polytabloid t)=polytabloid (g*t) := by
  simp only [polytabloid_formula,map_sub,ambient_basis,Equiv.Perm.coe_mul,Function.comp_apply]

def spechtSpace : Submodule K V := Submodule.span K (Set.range polytabloid)

def coordSum : V →ₗ[K] K where
  toFun v := ∑ i, v i
  map_add' v w := Finset.sum_add_distrib
  map_smul' a v := by simp [Finset.mul_sum]

def augmentation : Submodule K V := LinearMap.ker coordSum

theorem coordSum_three (v : V) : coordSum v=v 0+v 1+v 2 := by
  simp [coordSum,Fin.sum_univ_succ,add_assoc]

theorem basis_sum (i : Fin 3) : coordSum (basisVector i)=1 := by
  simp [coordSum,basisVector]

theorem vector_decomposition (v : V) (h : coordSum v=0) :
    v=v 1 • (basisVector 1-basisVector 0)+v 2 • (basisVector 2-basisVector 0) := by
  revert v
  decide

theorem specht_eq_augmentation : spechtSpace=augmentation := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨t,rfl⟩
    change coordSum (polytabloid t)=0
    rw [polytabloid_formula,map_sub,basis_sum,basis_sum,sub_self]
  · intro v hv
    have h1 : basisVector 1-basisVector 0 ∈ spechtSpace := by
      have h : polytabloid (Equiv.swap 1 2) ∈ spechtSpace := Submodule.subset_span ⟨_,rfl⟩
      simpa [polytabloid_formula, show (Equiv.swap (1:Fin 3) 2) 0=0 by decide] using h
    have h2 : basisVector 2-basisVector 0 ∈ spechtSpace := by
      have h : polytabloid (1:G) ∈ spechtSpace := Submodule.subset_span ⟨_,rfl⟩
      simpa [polytabloid_formula] using h
    rw [vector_decomposition v hv]
    exact spechtSpace.add_mem (spechtSpace.smul_mem _ h1) (spechtSpace.smul_mem _ h2)

theorem ambient_sum (g : G) (v : V) : coordSum (ambient g v)=coordSum v := by
  revert g v
  decide

def specht : Subrepresentation ambient where
  toSubmodule := spechtSpace
  apply_mem_toSubmodule g v hv := by
    rw [specht_eq_augmentation] at hv ⊢
    change coordSum (ambient g v)=0
    rw [ambient_sum]
    exact hv

abbrev S := specht.toSubmodule

def spechtRepresentation : Representation K G S := specht.toRepresentation

def augmentationSubrep : Subrepresentation ambient where
  toSubmodule := augmentation
  apply_mem_toSubmodule g v hv := by
    change coordSum (ambient g v)=0
    rw [ambient_sum]
    exact hv

def augmentationRepresentation := augmentationSubrep.toRepresentation

def spechtAugmentationEquiv : S ≃ₗ[K] augmentation where
  toFun v := ⟨v.1,by have h:=v.2; change v.1∈spechtSpace at h; rwa [specht_eq_augmentation] at h⟩
  invFun v := ⟨v.1,by change v.1∈spechtSpace; rw [specht_eq_augmentation];exact v.2⟩
  left_inv v := rfl
  right_inv v := rfl
  map_add' v w := rfl
  map_smul' a v := rfl

theorem spechtAugmentationEquiv_intertwines (g : G) (v : S) :
    spechtAugmentationEquiv (spechtRepresentation g v)=
      augmentationRepresentation g (spechtAugmentationEquiv v) := rfl

theorem spechtRepresentation_apply (g : G) (v : S) (i : Fin 3) :
    (spechtRepresentation g v).1 i=v.1 (g⁻¹ i) := rfl

theorem specht_vector_sum (v : S) : coordSum v.1=0 := by
  have h := v.2
  change v.1 ∈ spechtSpace at h
  rw [specht_eq_augmentation] at h
  exact h

def constantLine : Subrepresentation spechtRepresentation where
  toSubmodule :=
    { carrier := {v | ∀ i, v.1 i=v.1 0}
      zero_mem' := fun _ => rfl
      add_mem' := by
        intro v w hv hw i
        change v.1 i+w.1 i=v.1 0+w.1 0
        rw [hv i,hw i]
      smul_mem' := by
        intro a v hv i
        change a*v.1 i=a*v.1 0
        rw [hv i] }
  apply_mem_toSubmodule g v hv i := by
    change v.1 (g⁻¹ i)=v.1 (g⁻¹ 0)
    exact (hv _).trans (hv _).symm

def witnessVector : S := ⟨polytabloid 1,Submodule.subset_span ⟨1,rfl⟩⟩

theorem witness_not_constant : witnessVector ∉ constantLine := by
  intro h
  have hh := h 1
  norm_num [witnessVector,polytabloid_formula,basisVector,Pi.single_apply] at hh
  have h1 : (1:Fin 3) ≠ 2 := by decide
  have h0 : (0:Fin 3) ≠ 2 := by decide
  simp only [h1,h0,ite_false] at hh
  exact (by decide : (0:K) ≠ -1) hh

theorem constantLine_ne_top : constantLine ≠ ⊤ := by
  intro h
  apply witness_not_constant
  rw [h]
  trivial

def onesVector : S := ⟨fun _ => 1,by
  change (fun _ : Fin 3 => (1:K)) ∈ spechtSpace
  rw [specht_eq_augmentation]
  change coordSum (fun _ => 1)=0
  decide⟩

theorem onesVector_mem : onesVector ∈ constantLine := fun _ => rfl

theorem onesVector_ne_zero : onesVector ≠ 0 := by
  intro h
  have hh := congrArg (fun v : S => v.1 0) h
  exact (by decide : (1:K) ≠ 0) hh

theorem constantLine_ne_bot : constantLine ≠ ⊥ := by
  intro h
  have hh := onesVector_mem
  rw [h] at hh
  exact onesVector_ne_zero hh

def cycle : G := Equiv.swap 0 1 * Equiv.swap 1 2

theorem delta_constant_coordinates (v : V) (h : coordSum v=0) (i : Fin 3) :
    (ambient cycle v-v) i=(ambient cycle v-v) 0 := by
  revert v i
  decide

theorem cycle_fixed_constant (v : V) (h : ambient cycle v=v) (i : Fin 3) : v i=v 0 := by
  revert v i
  decide

theorem delta_mem_constantLine (v : S) : spechtRepresentation cycle v-v ∈ constantLine := by
  intro i
  exact delta_constant_coordinates v.1 (specht_vector_sum v) i

theorem fixed_mem_constantLine (v : S) (h : spechtRepresentation cycle v=v) : v ∈ constantLine := by
  intro i
  have hh : ambient cycle v.1=v.1 := congrArg Subtype.val h
  exact cycle_fixed_constant v.1 hh i

theorem constantLine_has_no_complement (W : Subrepresentation spechtRepresentation) :
    ¬IsCompl constantLine W := by
  intro h
  have hWle : W ≤ constantLine := by
    intro v hv
    have hdW : spechtRepresentation cycle v-v ∈ W :=
      W.toSubmodule.sub_mem (W.apply_mem_toSubmodule cycle hv) hv
    have hd : spechtRepresentation cycle v-v=0 := by
      have hm : spechtRepresentation cycle v-v ∈ constantLine ⊓ W := ⟨delta_mem_constantLine v,hdW⟩
      rw [h.inf_eq_bot] at hm
      exact hm
    exact fixed_mem_constantLine v (sub_eq_zero.mp hd)
  have hW : W=⊥ := by
    apply le_antisymm _ bot_le
    intro v hv
    have hm : v ∈ constantLine ⊓ W := ⟨hWle hv,hv⟩
    rw [h.inf_eq_bot] at hm
    exact hm
  apply constantLine_ne_top
  simpa [hW] using h.sup_eq_top

theorem specht_not_semisimple :
    ¬Representation.IsSemisimpleRepresentation (k := K) (G := G) (V := S) spechtRepresentation := by
  intro h
  let _ := h
  obtain ⟨W,hW⟩ := exists_isCompl constantLine
  exact constantLine_has_no_complement W hW

theorem specht_group_algebra_not_semisimple :
    ¬IsSemisimpleModule (MonoidAlgebra K G) spechtRepresentation.asModule := by
  intro h
  exact specht_not_semisimple
    ((Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule _).mpr h)

abbrev Cell := ℕ × ℕ

def Adjacent (a b : Cell) : Prop :=
  (a.1=b.1 ∧ (a.2+1=b.2 ∨ b.2+1=a.2)) ∨
    (a.2=b.2 ∧ (a.1+1=b.1 ∨ b.1+1=a.1))

def CellsConnected (c : Finset Cell) : Prop :=
  c.Nonempty ∧ ∀ a ∈ c, ∀ b ∈ c,
    Relation.ReflTransGen (fun x y => x ∈ c ∧ y ∈ c ∧ Adjacent x y) a b

def NoSquare (c : Finset Cell) : Prop := ∀ i j,
  ¬((i,j) ∈ c ∧ (i+1,j) ∈ c ∧ (i,j+1) ∈ c ∧ (i+1,j+1) ∈ c)

def RimRemoval (p : ℕ) (lam μ : YoungDiagram) : Prop :=
  0<p ∧ μ≤lam ∧ (lam.cells\μ.cells).card=p ∧
    CellsConnected (lam.cells\μ.cells) ∧ NoSquare (lam.cells\μ.cells)

theorem shape_to_corner (a : Cell) (ha : a ∈ shape.cells) :
    Relation.ReflTransGen
      (fun x y => x ∈ shape.cells ∧ y ∈ shape.cells ∧ Adjacent x y) a (0,0) := by
  rw [shape_cells] at ha
  simp only [Finset.mem_insert,Finset.mem_singleton] at ha
  rcases ha with rfl | rfl | rfl
  · exact .refl
  · exact .single (by simp [shape_cells,Adjacent])
  · exact .single (by simp [shape_cells,Adjacent])

theorem corner_to_shape (a : Cell) (ha : a ∈ shape.cells) :
    Relation.ReflTransGen
      (fun x y => x ∈ shape.cells ∧ y ∈ shape.cells ∧ Adjacent x y) (0,0) a := by
  rw [shape_cells] at ha
  simp only [Finset.mem_insert,Finset.mem_singleton] at ha
  rcases ha with rfl | rfl | rfl
  · exact .refl
  · exact .single (by simp [shape_cells,Adjacent])
  · exact .single (by simp [shape_cells,Adjacent])

theorem shape_connected : CellsConnected shape.cells := by
  refine ⟨⟨(0,0),by simp [shape_cells]⟩,?_⟩
  intro a ha b hb
  exact (shape_to_corner a ha).trans (corner_to_shape b hb)

theorem shape_noSquare : NoSquare shape.cells := by
  intro i j h
  have hh := h.2.2.2
  have : (i+1)+(j+1)≤1 := (shape_mem (i+1) (j+1)).mp hh
  omega

theorem shape_rimRemoval : RimRemoval 3 shape ⊥ := by
  refine ⟨by decide,bot_le,?_,?_,?_⟩
  · simpa using shape_card
  · simpa using shape_connected
  · simpa using shape_noSquare

theorem removal_card {p : ℕ} {lam μ : YoungDiagram} (h : RimRemoval p lam μ) :
    μ.card+p=lam.card := by
  have hs : μ.cells ⊆ lam.cells := h.2.1
  have hc := Finset.card_sdiff_add_card_eq_card hs
  rw [h.2.2.1] at hc
  simpa [Nat.add_comm] using hc

inductive RemovalChain (p : ℕ) : YoungDiagram → ℕ → YoungDiagram → Prop
  | nil (lam : YoungDiagram) : RemovalChain p lam 0 lam
  | cons {lam μ ν : YoungDiagram} {k : ℕ} :
      RimRemoval p lam μ → RemovalChain p μ k ν → RemovalChain p lam (k+1) ν

theorem chain_card {p k : ℕ} {lam μ : YoungDiagram} (h : RemovalChain p lam k μ) :
    μ.card+k*p=lam.card := by
  induction h with
  | nil => simp
  | @cons lam ν μ k h hchain ih =>
    rw [Nat.add_mul,Nat.one_mul,← Nat.add_assoc,ih]
    exact removal_card h

def IsPCore (p : ℕ) (μ : YoungDiagram) : Prop := ¬∃ ν, RimRemoval p μ ν

def IsPCoreOf (p : ℕ) (lam μ : YoungDiagram) : Prop :=
  IsPCore p μ ∧ ∃ k, RemovalChain p lam k μ

theorem empty_isCore (p : ℕ) : IsPCore p ⊥ := by
  rintro ⟨ν,h⟩
  have hc := removal_card h
  have hp := h.1
  have hz : (⊥:YoungDiagram).card=0 := rfl
  omega

theorem shape_chain_length {k : ℕ} {μ : YoungDiagram} (h : RemovalChain 3 shape k μ) : k≤1 := by
  have hc := chain_card h
  rw [shape_card] at hc
  omega

theorem diagram_eq_empty {μ : YoungDiagram} (h : μ.card=0) : μ=⊥ := by
  apply YoungDiagram.ext
  exact Finset.card_eq_zero.mp h

theorem shape_core_unique {μ : YoungDiagram} (h : IsPCoreOf 3 shape μ) : μ=⊥ := by
  obtain ⟨hcore,k,hchain⟩ := h
  have hk := shape_chain_length hchain
  by_cases hz : k=0
  · subst k
    cases hchain
    exact False.elim (hcore ⟨⊥,shape_rimRemoval⟩)
  · have h1 : k=1 := by omega
    have hc := chain_card hchain
    rw [shape_card,h1] at hc
    apply diagram_eq_empty
    omega

theorem shape_core_exists : ∃ μ, IsPCoreOf 3 shape μ :=
  ⟨⊥,empty_isCore 3,1,.cons shape_rimRemoval (.nil ⊥)⟩

theorem terminal_shape_chain_length {μ : YoungDiagram} {k : ℕ}
    (hc : IsPCore 3 μ) (h : RemovalChain 3 shape k μ) : k=1 := by
  have he := shape_core_unique ⟨hc,k,h⟩
  have hn := chain_card h
  rw [he,shape_card] at hn
  change 0+k*3=3 at hn
  omega

def threeCore : YoungDiagram := Classical.choose shape_core_exists

theorem threeCore_eq_empty : threeCore=⊥ :=
  shape_core_unique (Classical.choose_spec shape_core_exists)

open scoped Classical in
def rimHookWeight (p : ℕ) (lam : YoungDiagram) : ℕ :=
  Nat.findGreatest (fun k => ∃ μ, RemovalChain p lam k μ) lam.card

theorem shape_weight_one : rimHookWeight 3 shape=1 := by
  classical
  unfold rimHookWeight
  apply Nat.findGreatest_eq_iff.mpr
  refine ⟨by rw [shape_card];decide,fun _ => ⟨⊥,.cons shape_rimRemoval (.nil ⊥)⟩,?_⟩
  intro n hn _ hh
  obtain ⟨μ,hμ⟩ := hh
  have := shape_chain_length hμ
  omega

def IsPRestricted (p : ℕ) (lam : YoungDiagram) : Prop :=
  ∀ i, lam.rowLen i-lam.rowLen (i+1)<p

theorem shape_row_zero : shape.rowLen 0=2 := by
  rw [YoungDiagram.rowLen_eq_card]
  simp [YoungDiagram.row,shape_cells]
  decide

theorem shape_row_one : shape.rowLen 1=1 := by
  rw [YoungDiagram.rowLen_eq_card]
  simp [YoungDiagram.row,shape_cells]
  decide

theorem shape_row_large (i : ℕ) (hi : 2 ≤ i) : shape.rowLen i=0 := by
  rw [YoungDiagram.rowLen_eq_card]
  have h0 : 0 ≠ i := by omega
  have h1 : 1 ≠ i := by omega
  simp [YoungDiagram.row,shape_cells,h0,h1]

theorem shape_restricted : IsPRestricted 3 shape := by
  intro i
  rcases i with _ | (_ | i)
  · norm_num [shape_row_zero,shape_row_one]
  · rw [shape_row_one,shape_row_large 2 (by omega)]
    decide
  · rw [shape_row_large (i+2) (by omega),shape_row_large (i+2+1) (by omega)]
    decide

theorem shape_weight_bound : 2*rimHookWeight 3 shape≤3 := by
  rw [shape_weight_one]
  decide

theorem printed_counterexample :
    Nat.Prime 3 ∧ IsPRestricted 3 shape ∧ threeCore=⊥ ∧
    2*rimHookWeight 3 shape≤3 ∧ shape.card<16 ∧
    ¬Representation.IsSemisimpleRepresentation (k:=K) (G:=G) (V:=S) spechtRepresentation := by
  exact ⟨by decide,shape_restricted,threeCore_eq_empty,shape_weight_bound,
    by rw [shape_card];decide,specht_not_semisimple⟩

end TLMC1761
