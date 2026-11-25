/-
  OrbitSperner/SymmetricActions.lean
  Core Lean 4.19.0 formalization of:
  1. The canonical S_n-action on B_n, exact orbit characterization (|x| = |y|),
     quotient isomorphism B_n / S_n ≅ C_{n+1}, orbit-antichain width = 1,
     and invariant-antichain width = C(n, ⌊n/2⌋) (zero deficit).
  2. Universal Dichotomy Theorem for arbitrary subgroups H ≤ S_n acting on B_n:
     every nontrivial permutation subgroup forces an exponential orbit-Sperner deficit
     2 * |F| ≤ C(n, ⌊n/2⌋) + C(n-1, ⌊(n-1)/2⌋).
-/
import OrbitSperner.BooleanSperner

namespace OrbitSperner

/-- Action of a permutation `σ : Perm n` on a subset indicator `x : BVec n`. -/
def actPerm {n : Nat} (σ : Perm n) (x : BVec n) : BVec n :=
  fun i => x (σ.invFun i)

theorem actPerm_id {n : Nat} (x : BVec n) : actPerm (Perm.id n) x = x := rfl

theorem actPerm_comp {n : Nat} (σ τ : Perm n) (x : BVec n) :
    actPerm (σ.comp τ) x = actPerm σ (actPerm τ x) := rfl

theorem actPerm_inv_left {n : Nat} (σ : Perm n) (x : BVec n) :
    actPerm σ.inv (actPerm σ x) = x := by
  funext i
  unfold actPerm Perm.inv
  dsimp
  rw [σ.left_inv]

theorem actPerm_inv_right {n : Nat} (σ : Perm n) (x : BVec n) :
    actPerm σ (actPerm σ.inv x) = x := by
  funext i
  unfold actPerm Perm.inv
  dsimp
  rw [σ.right_inv]

theorem actPerm_injective {n : Nat} (σ : Perm n) :
    ∀ ⦃x y : BVec n⦄, actPerm σ x = actPerm σ y → x = y := by
  intro x y h
  have h' := congrArg (actPerm σ.inv) h
  rw [actPerm_inv_left, actPerm_inv_left] at h'
  exact h'

theorem actPerm_subsetLe {n : Nat} (σ : Perm n) {x y : BVec n}
    (h : subsetLe x y) : subsetLe (actPerm σ x) (actPerm σ y) :=
  fun i hi => h (σ.invFun i) hi

/-- Index lookup in a list containing `x`, returning a `Fin l.length`. -/
def memIndex {α : Type} [DecidableEq α] : (l : List α) → (x : α) → x ∈ l → Fin l.length
  | [], _, hx => nomatch hx
  | a :: as, x, hx =>
    if h : x = a then
      ⟨0, by simp⟩
    else
      have hx' : x ∈ as := by
        rcases List.mem_cons.mp hx with rfl | hm
        · exact False.elim (h rfl)
        · exact hm
      let idx := memIndex as x hx'
      ⟨idx.val + 1, by simp⟩

theorem memIndex_injective {α : Type} [DecidableEq α] :
    ∀ (l : List α) {x y : α} (hx : x ∈ l) (hy : y ∈ l),
      memIndex l x hx = memIndex l y hy → x = y
  | [], _, _, hx, _, _ => nomatch hx
  | a :: as, x, y, hx, hy, heq => by
    unfold memIndex at heq
    by_cases hxa : x = a <;> by_cases hya : y = a
    · rw [hxa, hya]
    · simp [hxa, hya] at heq
    · simp [hxa, hya] at heq
    · simp [hxa, hya] at heq
      have hx' : x ∈ as := by rcases List.mem_cons.mp hx with rfl | hm; exact False.elim (hxa rfl); exact hm
      have hy' : y ∈ as := by rcases List.mem_cons.mp hy with rfl | hm; exact False.elim (hya rfl); exact hm
      exact memIndex_injective as hx' hy' (Fin.ext heq)

theorem memIndex_congr {α : Type} [DecidableEq α] (l : List α) {x y : α}
    (hx : x ∈ l) (hy : y ∈ l) (heq : x = y) :
    memIndex l x hx = memIndex l y hy := by
  subst heq
  rfl

/-- `List.get l i` with `Nodup l` gives an inverse to `memIndex`. -/
theorem memIndex_get_of_nodup {α : Type} [DecidableEq α] :
    ∀ (l : List α) (_hn : l.Nodup) (i : Fin l.length),
      memIndex l (l.get i) (List.get_mem l i) = i
  | [], _, i => Fin.elim0 i
  | a :: as, List.Pairwise.cons _ _, ⟨0, _⟩ => by
    simp [memIndex]
  | a :: as, List.Pairwise.cons ha has, ⟨k + 1, hk⟩ => by
    have hk' : k < as.length := by simp at hk; omega
    let i' : Fin as.length := ⟨k, hk'⟩
    have hget : (a :: as).get ⟨k + 1, hk⟩ = as.get i' := rfl
    have hmem : as.get i' ∈ as := List.get_mem as i'
    have hne : as.get i' ≠ a := fun heq => ha a (heq ▸ hmem) rfl
    have ih := memIndex_get_of_nodup as has i'
    apply Fin.ext
    unfold memIndex
    simp only [hget, hne, ↓reduceDIte]
    have hv : (memIndex as (as.get i') _).val = i'.val := congrArg Fin.val ih
    dsimp [i'] at hv ⊢
    omega

/-- Every `actPerm σ` has positive period at every `x : BVec n`. -/
theorem exists_pos_period_actPerm {n : Nat} (σ : Perm n) (x : BVec n) :
    ∃ m : Nat, 0 < m ∧ iterFun (actPerm σ) m x = x := by
  let U := allBVec n
  have hn : U.Nodup := nodup_allBVec n
  let gIdx : Fin U.length → Fin U.length :=
    fun i => memIndex U (actPerm σ (U.get i)) (mem_allBVec _)
  have hinj : ∀ u v : Fin U.length, gIdx u = gIdx v → u = v := by
    intro u v heq
    have h1 := memIndex_injective U (mem_allBVec (actPerm σ (U.get u)))
      (mem_allBVec (actPerm σ (U.get v))) heq
    have h2 : U.get u = U.get v := actPerm_injective σ h1
    have h3 : memIndex U (U.get u) (List.get_mem U u) =
        memIndex U (U.get v) (List.get_mem U v) := memIndex_congr U _ _ h2
    rw [memIndex_get_of_nodup U hn u, memIndex_get_of_nodup U hn v] at h3
    exact h3
  let xIdx := memIndex U x (mem_allBVec x)
  have hiter : ∀ k : Nat, ∀ y : BVec n,
      memIndex U (iterFun (actPerm σ) k y) (mem_allBVec _) =
        iterFun gIdx k (memIndex U y (mem_allBVec y)) := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ k ih =>
      intro y
      simp only [iterFun]
      rw [← ih y]
      let z := iterFun (actPerm σ) k y
      let zIdx := memIndex U z (mem_allBVec z)
      have hget : U.get zIdx = z := by
        have hm := memIndex_get_of_nodup U hn zIdx
        exact memIndex_injective U (List.get_mem U zIdx) (mem_allBVec z) hm
      dsimp [gIdx]
      exact memIndex_congr U _ _ (congrArg (actPerm σ) hget.symm)
  rcases exists_pos_period_fin gIdx hinj xIdx with ⟨m, hm, hper⟩
  refine ⟨m, hm, ?_⟩
  have hidx_eq : memIndex U (iterFun (actPerm σ) m x) (mem_allBVec _) =
      memIndex U x (mem_allBVec x) := by
    rw [hiter m x]
    exact hper
  exact memIndex_injective U _ _ hidx_eq

/-- The canonical group action of `S_n` (`Perm n`) on the Boolean lattice `B_n`. -/
def snPosetAction (n : Nat) : PosetGroupAction (booleanPoset n) (Perm n) where
  one := Perm.id n
  mul := Perm.comp
  inv := Perm.inv
  act := actPerm
  act_one := actPerm_id
  act_mul := actPerm_comp
  act_inv_left := actPerm_inv_left
  act_inv_right := actPerm_inv_right
  act_le := fun σ _ _ h => actPerm_subsetLe σ h
  finite_period := exists_pos_period_actPerm

/-! ### Weight Invariance under `Perm n` -/

theorem finSum_point_update : ∀ {n : Nat} (f : Fin n → Nat) (i₀ : Fin n) (v : Nat),
    finSum n (fun i => if i = i₀ then v else f i) + f i₀ = finSum n f + v
  | 0, _, i₀, _ => Fin.elim0 i₀
  | n + 1, f, i₀, v => by
    unfold finSum
    by_cases hlt : i₀.val < n
    · let j₀ : Fin n := ⟨i₀.val, hlt⟩
      have hcast : j₀.castSucc = i₀ := Fin.ext rfl
      have hlast_ne : Fin.last n ≠ i₀ := by
        intro heq
        have hv : (Fin.last n).val = i₀.val := congrArg Fin.val heq
        have hlv : (Fin.last n).val = n := rfl
        omega
      have hfun : (fun i : Fin n => if i.castSucc = i₀ then v else f i.castSucc) =
          (fun i : Fin n => if i = j₀ then v else f i.castSucc) := by
        funext i
        by_cases hij : i = j₀
        · subst hij; simp [hcast]
        · have hne : i.castSucc ≠ i₀ := by
            intro heq
            apply hij
            exact Fin.ext (by
              have hv1 : (i.castSucc).val = i₀.val := congrArg Fin.val heq
              exact hv1)
          simp [hij, hne]
      rw [hfun]
      simp only [hlast_ne, ↓reduceIte]
      have ih := finSum_point_update (fun i : Fin n => f i.castSucc) j₀ v
      rw [hcast] at ih
      omega
    · have hi₀ : i₀ = Fin.last n := Fin.ext (by
        have hilt : i₀.val < n + 1 := i₀.isLt
        have hlv : (Fin.last n).val = n := rfl
        omega)
      subst hi₀
      have hfun : (fun i : Fin n => if i.castSucc = Fin.last n then v else f i.castSucc) =
          (fun i : Fin n => f i.castSucc) := by
        funext i
        have hne : i.castSucc ≠ Fin.last n := by
          intro heq
          have hv : (i.castSucc).val = (Fin.last n).val := congrArg Fin.val heq
          have hilt : i.val < n := i.isLt
          have hcs : (i.castSucc).val = i.val := rfl
          have hlv : (Fin.last n).val = n := rfl
          omega
        simp [hne]
      rw [hfun]
      simp only [↓reduceIte]
      omega

/-- Lift `σ₀ : Perm n` to `Perm (n + 1)` fixing `Fin.last n`. -/
def liftPermLast {n : Nat} (σ₀ : Perm n) : Perm (n + 1) where
  toFun := fun i => if h : i.val < n then (σ₀.toFun ⟨i.val, h⟩).castSucc else Fin.last n
  invFun := fun i => if h : i.val < n then (σ₀.invFun ⟨i.val, h⟩).castSucc else Fin.last n
  left_inv := by
    intro i
    by_cases h : i.val < n
    · simp only [h, ↓reduceDIte]
      have h2 : ((σ₀.toFun ⟨i.val, h⟩).castSucc).val < n := (σ₀.toFun ⟨i.val, h⟩).isLt
      simp only [h2, ↓reduceDIte]
      have h3 : (⟨((σ₀.toFun ⟨i.val, h⟩).castSucc).val, h2⟩ : Fin n) = σ₀.toFun ⟨i.val, h⟩ :=
        Fin.ext rfl
      rw [h3, σ₀.left_inv]
      exact Fin.ext rfl
    · simp only [h, ↓reduceDIte]
      have hlv : ¬ ((Fin.last n).val < n) := by
        have hv : (Fin.last n).val = n := rfl
        omega
      simp only [hlv, ↓reduceDIte]
      exact Fin.ext (by
        have hilt : i.val < n + 1 := i.isLt
        have hv : (Fin.last n).val = n := rfl
        omega)
  right_inv := by
    intro i
    by_cases h : i.val < n
    · simp only [h, ↓reduceDIte]
      have h2 : ((σ₀.invFun ⟨i.val, h⟩).castSucc).val < n := (σ₀.invFun ⟨i.val, h⟩).isLt
      simp only [h2, ↓reduceDIte]
      have h3 : (⟨((σ₀.invFun ⟨i.val, h⟩).castSucc).val, h2⟩ : Fin n) = σ₀.invFun ⟨i.val, h⟩ :=
        Fin.ext rfl
      rw [h3, σ₀.right_inv]
      exact Fin.ext rfl
    · simp only [h, ↓reduceDIte]
      have hlv : ¬ ((Fin.last n).val < n) := by
        have hv : (Fin.last n).val = n := rfl
        omega
      simp only [hlv, ↓reduceDIte]
      exact Fin.ext (by
        have hilt : i.val < n + 1 := i.isLt
        have hv : (Fin.last n).val = n := rfl
        omega)

/-- Restrict `σ : Perm (n + 1)` fixing `Fin.last n` to `Perm n`. -/
def restrictPermLast {n : Nat} (σ : Perm (n + 1)) (hfix : σ.toFun (Fin.last n) = Fin.last n) :
    Perm n := by
  have hinv_fix : σ.invFun (Fin.last n) = Fin.last n := by
    have h := congrArg σ.invFun hfix
    rw [σ.left_inv] at h
    exact h.symm
  have hto_lt : ∀ i : Fin n, (σ.toFun i.castSucc).val < n := by
    intro i
    have hilt : (σ.toFun i.castSucc).val < n + 1 := (σ.toFun i.castSucc).isLt
    have hne : σ.toFun i.castSucc ≠ Fin.last n := by
      intro heq
      rw [← hfix] at heq
      have hij := σ.injective heq
      have hv : (i.castSucc).val = (Fin.last n).val := congrArg Fin.val hij
      have h1 : i.val < n := i.isLt
      have h2 : (i.castSucc).val = i.val := rfl
      have h3 : (Fin.last n).val = n := rfl
      omega
    have hnev : (σ.toFun i.castSucc).val ≠ n := fun hv => hne (Fin.ext hv)
    omega
  have hinv_lt : ∀ i : Fin n, (σ.invFun i.castSucc).val < n := by
    intro i
    have hilt : (σ.invFun i.castSucc).val < n + 1 := (σ.invFun i.castSucc).isLt
    have hne : σ.invFun i.castSucc ≠ Fin.last n := by
      intro heq
      rw [← hinv_fix] at heq
      have hij := σ.inv.injective heq
      have hv : (i.castSucc).val = (Fin.last n).val := congrArg Fin.val hij
      have h1 : i.val < n := i.isLt
      have h2 : (i.castSucc).val = i.val := rfl
      have h3 : (Fin.last n).val = n := rfl
      omega
    have hnev : (σ.invFun i.castSucc).val ≠ n := fun hv => hne (Fin.ext hv)
    omega
  exact {
    toFun := fun i => ⟨(σ.toFun i.castSucc).val, hto_lt i⟩
    invFun := fun i => ⟨(σ.invFun i.castSucc).val, hinv_lt i⟩
    left_inv := fun i => by
      have hc : (⟨(σ.toFun i.castSucc).val, hto_lt i⟩ : Fin n).castSucc = σ.toFun i.castSucc :=
        Fin.ext rfl
      have h1 : σ.invFun (⟨(σ.toFun i.castSucc).val, hto_lt i⟩ : Fin n).castSucc = i.castSucc := by
        rw [hc, σ.left_inv]
      have hv : (σ.invFun (⟨(σ.toFun i.castSucc).val, hto_lt i⟩ : Fin n).castSucc).val = i.val :=
        congrArg Fin.val h1
      exact Fin.ext hv
    right_inv := fun i => by
      have hc : (⟨(σ.invFun i.castSucc).val, hinv_lt i⟩ : Fin n).castSucc = σ.invFun i.castSucc :=
        Fin.ext rfl
      have h1 : σ.toFun (⟨(σ.invFun i.castSucc).val, hinv_lt i⟩ : Fin n).castSucc = i.castSucc := by
        rw [hc, σ.right_inv]
      have hv : (σ.toFun (⟨(σ.invFun i.castSucc).val, hinv_lt i⟩ : Fin n).castSucc).val = i.val :=
        congrArg Fin.val h1
      exact Fin.ext hv
  }

/-- Every permutation `σ : Perm n` preserves subset cardinality `weight`. -/
theorem weight_actPerm : ∀ {n : Nat} (σ : Perm n) (x : BVec n),
    weight (actPerm σ x) = weight x
  | 0, _, _ => rfl
  | n + 1, σ, x => by
    let a := σ.invFun (Fin.last n)
    have hto_a : σ.toFun a = Fin.last n := σ.right_inv (Fin.last n)
    by_cases ha : a.val < n
    · let i₀ : Fin n := ⟨a.val, ha⟩
      have hia : i₀.castSucc = a := Fin.ext rfl
      let τ := Perm.swap a (Fin.last n)
      let σ₁ := σ.comp τ
      have hfix : σ₁.toFun (Fin.last n) = Fin.last n := by
        unfold σ₁ Perm.comp τ Perm.swap
        dsimp
        have hne : Fin.last n ≠ a := by
          intro heq
          have hv : (Fin.last n).val = a.val := congrArg Fin.val heq
          have hlv : (Fin.last n).val = n := rfl
          omega
        simp [hne, hto_a]
      have hcomp : σ₁.comp τ = σ := by
        apply Perm.ext
        intro i
        unfold σ₁ Perm.comp τ Perm.swap
        dsimp
        by_cases h1 : i = a
        · subst h1
          have hba : Fin.last n ≠ a := fun heq => by
            have hv : (Fin.last n).val = a.val := congrArg Fin.val heq
            have hlv : (Fin.last n).val = n := rfl
            omega
          simp [hba]
        · by_cases h2 : i = Fin.last n
          · subst h2; simp
          · simp [h1, h2]
      rw [← hcomp, actPerm_comp]
      let σ₀ := restrictPermLast σ₁ hfix
      have hσ₁_eq : ∀ y : BVec (n + 1), weight (actPerm σ₁ y) = weight y := by
        intro y
        change finSum n (fun i => if actPerm σ₁ y i.castSucc then 1 else 0) +
            (if actPerm σ₁ y (Fin.last n) then 1 else 0) =
          finSum n (fun i => if bvecInit y i then 1 else 0) + (if y (Fin.last n) then 1 else 0)
        have hinit : (fun i : Fin n => if actPerm σ₁ y i.castSucc then 1 else 0) =
            (fun i : Fin n => if actPerm σ₀ (bvecInit y) i then 1 else 0) := by
          funext i
          unfold actPerm σ₀ restrictPermLast bvecInit
          dsimp
        have hlast_inv : σ₁.invFun (Fin.last n) = Fin.last n := by
          have h := congrArg σ₁.invFun hfix
          rw [σ₁.left_inv] at h
          exact h.symm
        rw [hinit]
        have ih := weight_actPerm σ₀ (bvecInit y)
        unfold weight at ih
        rw [ih]
        unfold actPerm
        rw [hlast_inv]
      rw [hσ₁_eq (actPerm τ x)]
      change finSum n (fun i => if actPerm τ x i.castSucc then 1 else 0) +
          (if actPerm τ x (Fin.last n) then 1 else 0) =
        finSum n (fun i => if x i.castSucc then 1 else 0) + (if x (Fin.last n) then 1 else 0)
      have hτ_last : actPerm τ x (Fin.last n) = x i₀.castSucc := by
        unfold actPerm τ Perm.swap
        dsimp
        have hne : Fin.last n ≠ a := fun heq => by
          have hv : (Fin.last n).val = a.val := congrArg Fin.val heq
          have hlv : (Fin.last n).val = n := rfl
          omega
        simp [hne, hia]
      have hτ_init : (fun i : Fin n => if actPerm τ x i.castSucc then 1 else 0) =
          (fun i : Fin n => if i = i₀ then (if x (Fin.last n) then 1 else 0) else (if x i.castSucc then 1 else 0)) := by
        funext i
        unfold actPerm τ Perm.swap
        dsimp
        by_cases hii : i = i₀
        · subst hii
          simp [hia]
        · have hne1 : i.castSucc ≠ a := by
            intro heq
            rw [← hia] at heq
            have hv : (i.castSucc).val = (i₀.castSucc).val := congrArg Fin.val heq
            exact hii (Fin.ext hv)
          have hne2 : i.castSucc ≠ Fin.last n := by
            intro heq
            have hv : (i.castSucc).val = (Fin.last n).val := congrArg Fin.val heq
            have h1 : i.val < n := i.isLt
            have h2 : (i.castSucc).val = i.val := rfl
            have h3 : (Fin.last n).val = n := rfl
            omega
          simp [hii, hne1, hne2]
      rw [hτ_init, hτ_last]
      exact finSum_point_update (fun i : Fin n => if x i.castSucc then 1 else 0)
        i₀ (if x (Fin.last n) then 1 else 0)
    · have halast : a = Fin.last n := Fin.ext (by
        have halt : a.val < n + 1 := a.isLt
        have hlv : (Fin.last n).val = n := rfl
        omega)
      have hfix : σ.toFun (Fin.last n) = Fin.last n := by
        have h := hto_a
        rw [halast] at h
        exact h
      let σ₀ := restrictPermLast σ hfix
      change finSum n (fun i => if actPerm σ x i.castSucc then 1 else 0) +
          (if actPerm σ x (Fin.last n) then 1 else 0) =
        finSum n (fun i => if bvecInit x i then 1 else 0) + (if x (Fin.last n) then 1 else 0)
      have hinit : (fun i : Fin n => if actPerm σ x i.castSucc then 1 else 0) =
          (fun i : Fin n => if actPerm σ₀ (bvecInit x) i then 1 else 0) := by
        funext i
        unfold actPerm σ₀ restrictPermLast bvecInit
        dsimp
      rw [hinit]
      have ih := weight_actPerm σ₀ (bvecInit x)
      unfold weight at ih
      rw [ih]
      unfold actPerm
      have hinv_last : σ.invFun (Fin.last n) = Fin.last n := halast
      rw [hinv_last]

/-! ### Exact `S_n`-Orbit and Quotient Characterization on `B_n` -/

theorem exists_true_of_weight_pos : ∀ {n : Nat} {x : BVec n},
    0 < weight x → ∃ i : Fin n, x i = true
  | 0, x, hw => by unfold weight finSum at hw; omega
  | n + 1, x, hw => by
    unfold weight finSum at hw
    cases hl : x (Fin.last n) with
    | true => exact ⟨Fin.last n, hl⟩
    | false =>
      simp only [hl, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hw
      rcases exists_true_of_weight_pos (x := bvecInit x) hw with ⟨i, hi⟩
      exact ⟨i.castSucc, hi⟩

theorem actPerm_liftPermLast {n : Nat} (σ₀ : Perm n) (b : Bool) (x : BVec n) :
    actPerm (liftPermLast σ₀) (extendBVec b x) = extendBVec b (actPerm σ₀ x) := by
  funext i
  unfold actPerm liftPermLast extendBVec
  dsimp
  by_cases h : i.val < n
  · simp only [h, ↓reduceDIte]
    have h2 : ((σ₀.invFun ⟨i.val, h⟩).castSucc).val < n := (σ₀.invFun ⟨i.val, h⟩).isLt
    simp only [h2, ↓reduceDIte]
    rfl
  · simp only [h, ↓reduceDIte]
    have hlv : ¬ ((Fin.last n).val < n) := by
      have hv : (Fin.last n).val = n := rfl
      omega
    simp only [hlv, ↓reduceDIte]

/-- Transitivity of `S_n` on subsets of equal cardinality:
    if `weight x = weight y`, there exists `σ : Perm n` with `actPerm σ x = y`. -/
theorem exists_perm_of_weight_eq : ∀ {n : Nat} {x y : BVec n},
    weight x = weight y → ∃ σ : Perm n, actPerm σ x = y
  | 0, x, y, _ => ⟨Perm.id 0, funext (fun i => Fin.elim0 i)⟩
  | n + 1, x, y, hw => by
    have liftStep : ∀ {u v : BVec (n + 1)},
        bvecLast u = bvecLast v → weight u = weight v →
        (∀ {u₀ v₀ : BVec n}, weight u₀ = weight v₀ → ∃ σ₀ : Perm n, actPerm σ₀ u₀ = v₀) →
        ∃ σ : Perm (n + 1), actPerm σ u = v := by
      intro u v hlast hwu ih_fn
      have hu_eta := extendBVec_eta u
      have hv_eta := extendBVec_eta v
      have hw_init : weight (bvecInit u) = weight (bvecInit v) := by
        have h1 : weight (extendBVec (bvecLast u) (bvecInit u)) = weight u := congrArg weight hu_eta
        have h2 : weight (extendBVec (bvecLast v) (bvecInit v)) = weight v := congrArg weight hv_eta
        cases hbl : bvecLast u <;> rw [hbl] at hlast h1 <;> rw [← hlast] at h2
        · rw [weight_extend_false] at h1 h2; omega
        · rw [weight_extend_true] at h1 h2; omega
      rcases ih_fn hw_init with ⟨σ₀, hσ₀⟩
      refine ⟨liftPermLast σ₀, ?_⟩
      rw [← hu_eta, ← hv_eta, hlast, actPerm_liftPermLast, hσ₀]
    cases hx : bvecLast x <;> cases hy : bvecLast y
    · exact liftStep (hx.trans hy.symm) hw (fun h => exists_perm_of_weight_eq h)
    · -- `bvecLast x = false`, `bvecLast y = true`: swap a `true` coordinate of `x` into `Fin.last n`
      have hwx : weight (bvecInit x) = weight y := by
        have h1 := congrArg weight (extendBVec_eta x)
        rw [hx, weight_extend_false] at h1
        omega
      have hy_pos : 0 < weight y := by
        have h2 := congrArg weight (extendBVec_eta y)
        rw [hy, weight_extend_true] at h2
        omega
      rcases exists_true_of_weight_pos (x := bvecInit x) (by omega) with ⟨i₀, hi₀⟩
      let τ := Perm.swap i₀.castSucc (Fin.last n)
      let x' := actPerm τ x
      have hx'_last : bvecLast x' = true := by
        unfold bvecLast x' actPerm τ Perm.swap
        dsimp
        have hne : Fin.last n ≠ i₀.castSucc := by
          intro heq
          have hv : (Fin.last n).val = (i₀.castSucc).val := congrArg Fin.val heq
          have h1 : i₀.val < n := i₀.isLt
          have h2 : (i₀.castSucc).val = i₀.val := rfl
          have h3 : (Fin.last n).val = n := rfl
          omega
        simp [hne]
        exact hi₀
      have hx'_w : weight x' = weight y := by
        dsimp [x']
        rw [weight_actPerm, hw]
      rcases liftStep (hx'_last.trans hy.symm) hx'_w (fun h => exists_perm_of_weight_eq h) with ⟨σ₁, hσ₁⟩
      exact ⟨σ₁.comp τ, by rw [actPerm_comp]; exact hσ₁⟩
    · -- `bvecLast x = true`, `bvecLast y = false`: symmetric
      have hwy : weight (bvecInit y) = weight x := by
        have h1 := congrArg weight (extendBVec_eta y)
        rw [hy, weight_extend_false] at h1
        omega
      have hx_pos : 0 < weight x := by
        have h2 := congrArg weight (extendBVec_eta x)
        rw [hx, weight_extend_true] at h2
        omega
      rcases exists_true_of_weight_pos (x := bvecInit y) (by omega) with ⟨i₀, hi₀⟩
      let τ := Perm.swap i₀.castSucc (Fin.last n)
      let y' := actPerm τ y
      have hy'_last : bvecLast y' = true := by
        unfold bvecLast y' actPerm τ Perm.swap
        dsimp
        have hne : Fin.last n ≠ i₀.castSucc := by
          intro heq
          have hv : (Fin.last n).val = (i₀.castSucc).val := congrArg Fin.val heq
          have h1 : i₀.val < n := i₀.isLt
          have h2 : (i₀.castSucc).val = i₀.val := rfl
          have h3 : (Fin.last n).val = n := rfl
          omega
        simp [hne]
        exact hi₀
      have hy'_w : weight x = weight y' := by
        dsimp [y']
        rw [weight_actPerm, hw]
      rcases liftStep (hx.trans hy'_last.symm) hy'_w (fun h => exists_perm_of_weight_eq h) with ⟨σ₁, hσ₁⟩
      refine ⟨τ.inv.comp σ₁, ?_⟩
      rw [actPerm_comp, hσ₁]
      exact actPerm_inv_left τ y
    · exact liftStep (hx.trans hy.symm) hw (fun h => exists_perm_of_weight_eq h)

/-- **`S_n`-Orbit Characterization on `B_n`**:
    Two subsets lie in the same `S_n`-orbit if and only if they have the same cardinality. -/
theorem sn_orbitEq_iff_weight_eq {n : Nat} (x y : BVec n) :
    (snPosetAction n).OrbitEq x y ↔ weight x = weight y := by
  constructor
  · rintro ⟨σ, rfl⟩
    exact (weight_actPerm σ x).symm
  · exact exists_perm_of_weight_eq

theorem weight_le_dim : ∀ {n : Nat} (x : BVec n), weight x ≤ n
  | 0, _ => Nat.le_refl 0
  | n + 1, x => by
    have h := congrArg weight (extendBVec_eta x)
    have ih := weight_le_dim (bvecInit x)
    cases hbl : bvecLast x <;> rw [hbl] at h
    · rw [weight_extend_false] at h; omega
    · rw [weight_extend_true] at h; omega

theorem exists_superset_of_weight_le : ∀ {n : Nat} (x : BVec n) (k : Nat),
    weight x ≤ k → k ≤ n → ∃ z : BVec n, subsetLe x z ∧ weight z = k
  | 0, x, k, hlo, hhi => by
    have hk : k = 0 := by omega
    subst hk
    exact ⟨x, fun _ h => h, rfl⟩
  | n + 1, x, k, hlo, hhi => by
    have heta := extendBVec_eta x
    have hw_eta := congrArg weight heta
    cases hbl : bvecLast x with
    | true =>
      rw [hbl, weight_extend_true] at hw_eta
      have hk_pos : 1 ≤ k := by omega
      rcases exists_superset_of_weight_le (bvecInit x) (k - 1) (by omega) (by omega) with ⟨z₀, hzle, hzw⟩
      refine ⟨extendBVec true z₀, ?_, ?_⟩
      · rw [← heta, hbl]
        exact subsetLe_extend (fun h => h) hzle
      · rw [weight_extend_true, hzw]
        omega
    | false =>
      rw [hbl, weight_extend_false] at hw_eta
      if hk_le_n : k ≤ n then
        rcases exists_superset_of_weight_le (bvecInit x) k (by omega) hk_le_n with ⟨z₀, hzle, hzw⟩
        refine ⟨extendBVec false z₀, ?_, ?_⟩
        · rw [← heta, hbl]
          exact subsetLe_extend (fun h => h) hzle
        · rw [weight_extend_false, hzw]
      else
        have hk_eq : k = n + 1 := by omega
        subst hk_eq
        rcases exists_superset_of_weight_le (bvecInit x) n
          (weight_le_dim (bvecInit x)) (Nat.le_refl n) with ⟨z₀, hzle, hzw⟩
        refine ⟨extendBVec true z₀, ?_, ?_⟩
        · rw [← heta, hbl]
          exact subsetLe_extend (fun h => nomatch h) hzle
        · rw [weight_extend_true, hzw]

/-- **Quotient Poset Isomorphism `B_n / S_n ≅ C_{n+1}`**:
    `[x]_{S_n} ≤ [y]_{S_n}` in `B_n / S_n` if and only if `weight x ≤ weight y`. -/
theorem bn_quotient_sn_iff_le {n : Nat} (x y : BVec n) :
    (snPosetAction n).OrbitLe x y ↔ weight x ≤ weight y := by
  constructor
  · rintro ⟨σ, hle⟩
    dsimp [snPosetAction, booleanPoset] at hle
    have hw := weight_le_of_subsetLe hle
    rw [weight_actPerm] at hw
    exact hw
  · intro hw
    rcases exists_superset_of_weight_le x (weight y) hw (weight_le_dim y) with ⟨z, hxz, hwz⟩
    rcases exists_perm_of_weight_eq hwz.symm with ⟨σ, hσ⟩
    refine ⟨σ, ?_⟩
    dsimp [snPosetAction, booleanPoset]
    rw [hσ]
    exact hxz

/-- **Exact `S_n`-Orbit Antichain Width = 1**:
    Every list of pairwise incomparable `S_n`-orbits in `B_n / S_n` has length at most `1`. -/
theorem bn_sn_orbit_antichain_le_one {n : Nat} {reps : List (BVec n)}
    (hpw : List.Pairwise
      (fun x y => ¬ (snPosetAction n).OrbitLe x y ∧ ¬ (snPosetAction n).OrbitLe y x) reps) :
    reps.length ≤ 1 := by
  cases reps with
  | nil => simp
  | cons r₁ rest =>
    cases rest with
    | nil => simp
    | cons r₂ tail =>
      cases hpw with
      | cons hr₁ _ =>
        have hinc := hr₁ r₂ (List.Mem.head tail)
        rw [bn_quotient_sn_iff_le, bn_quotient_sn_iff_le] at hinc
        omega

/-- Singleton `[falseBVec n]` is a valid `1`-element orbit antichain in `B_n / S_n`. -/
theorem bn_sn_orbit_antichain_achieved (n : Nat) :
    List.Pairwise
      (fun x y => ¬ (snPosetAction n).OrbitLe x y ∧ ¬ (snPosetAction n).OrbitLe y x)
      [falseBVec n] ∧ ([falseBVec n]).length = 1 :=
  ⟨List.Pairwise.cons (fun _ h => nomatch h) List.Pairwise.nil, rfl⟩

/-- **`S_n`-Invariance of Middle Layer**:
    `midLayer n` is an `S_n`-invariant antichain of exact size `spernerNum n = C(n, ⌊n/2⌋)`. -/
theorem midLayer_sn_invariant (n : Nat) :
    (snPosetAction n).IsInvariantPred (fun x => midLayer n x = true) := by
  intro σ x hx
  unfold midLayer at hx ⊢
  change (weight (actPerm σ x) == n / 2) = true
  rw [weight_actPerm]
  exact hx

/-! ### Universal Dichotomy Theorem for Arbitrary Permutation Subgroups `H ≤ S_n` -/

/-- A subgroup of `Perm n` (`S_n`). -/
structure PermSubgroup (n : Nat) where
  mem : Perm n → Prop
  id_mem : mem (Perm.id n)
  comp_mem : ∀ {σ τ}, mem σ → mem τ → mem (σ.comp τ)
  inv_mem : ∀ {σ}, mem σ → mem σ.inv

/-- Quotient relation on `H`-orbits in `B_n`. -/
def OrbitLeSub {n : Nat} (H : PermSubgroup n) (x y : BVec n) : Prop :=
  ∃ σ : Perm n, H.mem σ ∧ subsetLe x (actPerm σ y)

/-- Two representatives are incomparable in `B_n / H`. -/
def OrbitIncompSub {n : Nat} (H : PermSubgroup n) (x y : BVec n) : Prop :=
  ¬ OrbitLeSub H x y ∧ ¬ OrbitLeSub H y x

/-- Every `H ≤ S_n` leaves `midLayer n` invariant, so the maximum `H`-invariant antichain
    size in `B_n` is identically `spernerNum n` (zero invariant-antichain deficit). -/
theorem midLayer_subgroup_invariant {n : Nat} (H : PermSubgroup n) :
    (∀ σ, H.mem σ → ∀ x, midLayer n x = true → midLayer n (actPerm σ x) = true) ∧
    (booleanPoset n).IsAntichainPred (fun x => midLayer n x = true) ∧
    setCard (midLayer n) = spernerNum n :=
  ⟨fun σ _ x hx => midLayer_sn_invariant n σ x hx,
   midLayer_isAntichain n,
   midLayer_card_eq_spernerNum n⟩

/-- Projection `BVec (m + 1) → BVec m` deleting coordinate `b`. -/
def projSkip {m : Nat} (b : Fin (m + 1)) (x : BVec (m + 1)) : BVec m :=
  fun i => x (skipIdx b i)

theorem subsetLe_iff_projSkip_of_eq_coords {m : Nat} {a b : Fin (m + 1)} (hab : a ≠ b)
    {x y : BVec (m + 1)} (hx : x a = x b) (hy : y a = y b) :
    subsetLe x y ↔ subsetLe (projSkip b x) (projSkip b y) := by
  constructor
  · intro hxy i hi
    exact hxy (skipIdx b i) hi
  · intro hproj k hk
    if hkb : k = b then
      subst hkb
      let ia : Fin m := unskipIdx k a hab
      have hskip : skipIdx k ia = a := skipIdx_unskipIdx k a hab
      have hxa : projSkip k x ia = true := by
        unfold projSkip
        rw [hskip, hx]
        exact hk
      have hya : projSkip k y ia = true := hproj ia hxa
      unfold projSkip at hya
      rw [hskip, hy] at hya
      exact hya
    else
      let ik : Fin m := unskipIdx b k hkb
      have hskip : skipIdx b ik = k := skipIdx_unskipIdx b k hkb
      have hxk : projSkip b x ik = true := by
        unfold projSkip
        rw [hskip]
        exact hk
      have hyk := hproj ik hxk
      unfold projSkip at hyk
      rw [hskip] at hyk
      exact hyk

theorem pairwise_filter {α : Type} {R : α → α → Prop} (P : α → Bool) :
    ∀ {l : List α}, List.Pairwise R l → List.Pairwise R (l.filter P)
  | [], _ => List.Pairwise.nil
  | a :: as, List.Pairwise.cons ha has => by
    simp only [List.filter]
    cases P a with
    | false => exact pairwise_filter P has
    | true =>
      apply List.Pairwise.cons
      · intro b hb
        exact ha b (List.mem_filter.mp hb).1
      · exact pairwise_filter P has

theorem length_filter_pos_neg {α : Type} (P : α → Bool) :
    ∀ l : List α, l.length = (l.filter P).length + (l.filter (fun x => !P x)).length
  | [] => rfl
  | a :: as => by
    simp only [List.filter]
    have ih := length_filter_pos_neg P as
    cases P a <;> simp only [Bool.not_true, Bool.not_false, List.length] <;> omega

theorem pairwise_append_iff_custom {α : Type} {R : α → α → Prop} :
    ∀ {l₁ l₂ : List α}, List.Pairwise R l₁ → List.Pairwise R l₂ →
      (∀ x ∈ l₁, ∀ y ∈ l₂, R x y) → List.Pairwise R (l₁ ++ l₂)
  | [], _, _, h₂, _ => h₂
  | a :: as, l₂, List.Pairwise.cons ha has, h₂, hcross => by
    apply List.Pairwise.cons
    · intro b hb
      rcases List.mem_append.mp hb with hbas | hbl₂
      · exact ha b hbas
      · exact hcross a (List.Mem.head as) b hbl₂
    · exact pairwise_append_iff_custom has h₂ (fun x hx => hcross x (List.Mem.tail a hx))

theorem pairwise_map_of_pairwise {α β : Type} {R : α → α → Prop} {Q : β → β → Prop}
    (f : α → β) (himp : ∀ ⦃u v⦄, R u v → Q (f u) (f v)) :
    ∀ {l : List α}, List.Pairwise R l → List.Pairwise Q (l.map f)
  | [], _ => List.Pairwise.nil
  | _ :: _, List.Pairwise.cons ha has => by
    apply List.Pairwise.cons
    · intro b hb
      rcases List.mem_map.mp hb with ⟨a', ha', rfl⟩
      exact himp (ha a' ha')
    · exact pairwise_map_of_pairwise f himp has

/-- Helper: if `x` and `y` are `H`-orbit-incomparable, then any `u` in `H · x` and `v` in `H · y`
    are incomparable in `B_n`. -/
theorem incomp_of_orbitIncompSub {n : Nat} {H : PermSubgroup n} {x y u v : BVec n}
    (hinc : OrbitIncompSub H x y)
    {σ₁ σ₂ : Perm n} (hσ₁ : H.mem σ₁) (hσ₂ : H.mem σ₂)
    (hu : u = actPerm σ₁ x) (hv : v = actPerm σ₂ y) :
    (booleanPoset n).Incomp u v := by
  subst hu hv
  constructor
  · intro hle
    apply hinc.1
    refine ⟨σ₁.inv.comp σ₂, H.comp_mem (H.inv_mem hσ₁) hσ₂, ?_⟩
    rw [actPerm_comp]
    have h' := actPerm_subsetLe σ₁.inv hle
    rw [actPerm_inv_left] at h'
    exact h'
  · intro hge
    apply hinc.2
    refine ⟨σ₂.inv.comp σ₁, H.comp_mem (H.inv_mem hσ₂) hσ₁, ?_⟩
    rw [actPerm_comp]
    have h' := actPerm_subsetLe σ₂.inv hge
    rw [actPerm_inv_left] at h'
    exact h'

/-- **Universal Nontrivial Permutation Subgroup Bound**:
    For ANY subgroup `H ≤ Perm n` containing at least one non-identity permutation
    (`σ ∈ H` with `σ(a) ≠ a`), EVERY `H`-orbit antichain `reps` in `B_n / H` satisfies:
      `2 * reps.length ≤ spernerNum n + spernerNum (n - 1)`. -/
theorem nontrivial_subgroup_orbit_antichain_bound {n : Nat} (H : PermSubgroup n)
    {σ : Perm n} (hσ : H.mem σ) {a : Fin n} (ha : σ.toFun a ≠ a)
    {reps : List (BVec n)} (hpw : List.Pairwise (OrbitIncompSub H) reps) :
    2 * reps.length ≤ spernerNum n + spernerNum (n - 1) := by
  cases n with
  | zero => exact Fin.elim0 a
  | succ m =>
    let b : Fin (m + 1) := σ.toFun a
    have hab : a ≠ b := fun heq => ha heq.symm
    let isFix : BVec (m + 1) → Bool := fun r => decide (actPerm σ r = r)
    let rFix := reps.filter isFix
    let rMov := reps.filter (fun r => !isFix r)
    have hlen_split : reps.length = rFix.length + rMov.length := length_filter_pos_neg isFix reps
    -- 1. Bound `rFix.length ≤ spernerNum m` via `projSkip b` into `B_m`
    have hfix_coords : ∀ r ∈ rFix, r a = r b := by
      intro r hr
      have hmem := (List.mem_filter.mp hr).2
      have heq : actPerm σ r = r := of_decide_eq_true hmem
      have hval := congrFun heq b
      unfold actPerm at hval
      have hinvb : σ.invFun b = a := σ.left_inv a
      rw [hinvb] at hval
      exact hval
    have hpw_fix_orb : List.Pairwise (OrbitIncompSub H) rFix := pairwise_filter isFix hpw
    have hpw_proj : List.Pairwise (fun u v => (booleanPoset m).Incomp u v)
        (rFix.map (projSkip b)) := by
      -- Prove by induction on `rFix` carrying `hfix_coords` and `hpw_fix_orb`
      suffices ∀ (L : List (BVec (m + 1))),
          (∀ r ∈ L, r a = r b) → List.Pairwise (OrbitIncompSub H) L →
          List.Pairwise (fun u v => (booleanPoset m).Incomp u v) (L.map (projSkip b)) by
        exact this rFix hfix_coords hpw_fix_orb
      intro L hcoords hpwL
      induction L with
      | nil => exact List.Pairwise.nil
      | cons x xs ih =>
        cases hpwL with
        | cons hx hxs =>
          apply List.Pairwise.cons
          · intro v hv
            rcases List.mem_map.mp hv with ⟨y, hy, rfl⟩
            have hinc_bn : (booleanPoset (m + 1)).Incomp x y :=
              incomp_of_orbitIncompSub (hx y hy) H.id_mem H.id_mem rfl rfl
            have hxa := hcoords x (List.Mem.head xs)
            have hya := hcoords y (List.Mem.tail x hy)
            constructor
            · intro hle
              exact hinc_bn.1 ((subsetLe_iff_projSkip_of_eq_coords hab hxa hya).mpr hle)
            · intro hge
              exact hinc_bn.2 ((subsetLe_iff_projSkip_of_eq_coords hab hya hxa).mpr hge)
          · exact ih (fun r hr => hcoords r (List.Mem.tail x hr)) hxs
    have hbound_fix : rFix.length ≤ spernerNum m := by
      have h := sperner_theorem_list hpw_proj
      rw [List.length_map] at h
      exact h
    -- 2. Bound `rFix.length + 2 * rMov.length ≤ spernerNum (m + 1)` via `expanded` in `B_{m+1}`
    let expanded : List (BVec (m + 1)) := rFix ++ (rMov ++ rMov.map (actPerm σ))
    -- Disjointness/incomparability between distinct representatives in `reps`
    have hsym_pw : ∀ {L : List (BVec (m + 1))},
        List.Pairwise (OrbitIncompSub H) L →
        ∀ x ∈ L, ∀ y ∈ L, x ≠ y → OrbitIncompSub H x y := by
      intro L hp x hx y hy hxy
      induction L with
      | nil => nomatch hx
      | cons hd tl ih =>
        cases hp with
        | cons hhd htl =>
          rcases List.mem_cons.mp hx with rfl | hx' <;>
            rcases List.mem_cons.mp hy with rfl | hy'
          · exact False.elim (hxy rfl)
          · exact hhd y hy'
          · exact ⟨(hhd x hx').2, (hhd x hx').1⟩
          · exact ih htl hx' hy'
    have hdistinct_orb : ∀ {x y : BVec (m + 1)},
        isFix x = true → (!isFix y) = true → x ∈ reps → y ∈ reps → OrbitIncompSub H x y := by
      intro x y hfx hfy hmx hmy
      have hne : x ≠ y := by
        intro heq; subst heq; rw [hfx] at hfy; cases hfy
      exact hsym_pw hpw x hmx y hmy hne
    have hpw_mov_orb : List.Pairwise (OrbitIncompSub H) rMov :=
      pairwise_filter (fun r => !isFix r) hpw
    have hpw_rFix_bn : List.Pairwise (fun u v => (booleanPoset (m + 1)).Incomp u v) rFix := by
      have hm := pairwise_map_of_pairwise (f := id)
        (fun _ _ h => incomp_of_orbitIncompSub h H.id_mem H.id_mem rfl rfl) hpw_fix_orb
      rw [List.map_id] at hm
      exact hm
    have hpw_rMov_bn : List.Pairwise (fun u v => (booleanPoset (m + 1)).Incomp u v) rMov := by
      have hm := pairwise_map_of_pairwise (f := id)
        (fun _ _ h => incomp_of_orbitIncompSub h H.id_mem H.id_mem rfl rfl) hpw_mov_orb
      rw [List.map_id] at hm
      exact hm
    have hpw_rMov_act_bn : List.Pairwise (fun u v => (booleanPoset (m + 1)).Incomp u v)
        (rMov.map (actPerm σ)) :=
      pairwise_map_of_pairwise (actPerm σ)
        (fun _ _ h => incomp_of_orbitIncompSub h hσ hσ rfl rfl) hpw_mov_orb
    -- Cross incomparability between `rMov` and `rMov.map (actPerm σ)`
    have hmov_cross : ∀ u ∈ rMov, ∀ v ∈ rMov.map (actPerm σ),
        (booleanPoset (m + 1)).Incomp u v := by
      intro u hu v hv
      rcases List.mem_map.mp hv with ⟨w, hw, rfl⟩
      by_cases huw : u = w
      · subst huw
        have hnotfix : (!isFix u) = true := (List.mem_filter.mp hu).2
        have hne_act : actPerm σ u ≠ u := by
          intro heq
          have hf : isFix u = true := decide_eq_true heq
          rw [hf] at hnotfix
          cases hnotfix
        constructor
        · intro hle
          have horb1 : (snPosetAction (m + 1)).OrbitEq u (actPerm σ u) := ⟨σ, rfl⟩
          have heq := (snPosetAction (m + 1)).orbit_isAntichain horb1 hle
          exact hne_act heq.symm
        · intro hge
          have horb2 : (snPosetAction (m + 1)).OrbitEq (actPerm σ u) u :=
            ⟨σ.inv, actPerm_inv_left σ u⟩
          have heq := (snPosetAction (m + 1)).orbit_isAntichain horb2 hge
          exact hne_act heq
      · have hinc : OrbitIncompSub H u w := hsym_pw hpw_mov_orb u hu w hw huw
        exact incomp_of_orbitIncompSub hinc H.id_mem hσ rfl rfl
    have hpw_mov_both : List.Pairwise (fun u v => (booleanPoset (m + 1)).Incomp u v)
        (rMov ++ rMov.map (actPerm σ)) :=
      pairwise_append_iff_custom hpw_rMov_bn hpw_rMov_act_bn hmov_cross
    have hfix_cross : ∀ u ∈ rFix, ∀ v ∈ rMov ++ rMov.map (actPerm σ),
        (booleanPoset (m + 1)).Incomp u v := by
      intro u hu v hv
      have hu_filt := List.mem_filter.mp hu
      rcases List.mem_append.mp hv with hv_mov | hv_act
      · have hv_filt := List.mem_filter.mp hv_mov
        have hinc := hdistinct_orb hu_filt.2 hv_filt.2 hu_filt.1 hv_filt.1
        exact incomp_of_orbitIncompSub hinc H.id_mem H.id_mem rfl rfl
      · rcases List.mem_map.mp hv_act with ⟨w, hw_mov, rfl⟩
        have hw_filt := List.mem_filter.mp hw_mov
        have hinc := hdistinct_orb hu_filt.2 hw_filt.2 hu_filt.1 hw_filt.1
        exact incomp_of_orbitIncompSub hinc H.id_mem hσ rfl rfl
    have hpw_expanded : List.Pairwise (fun u v => (booleanPoset (m + 1)).Incomp u v) expanded :=
      pairwise_append_iff_custom hpw_rFix_bn hpw_mov_both hfix_cross
    have hbound_exp : expanded.length ≤ spernerNum (m + 1) :=
      sperner_theorem_list hpw_expanded
    have hlen_exp : expanded.length = rFix.length + 2 * rMov.length := by
      dsimp [expanded]
      simp only [List.length_append, List.length_map]
      omega
    have hsub : m + 1 - 1 = m := by omega
    rw [hsub]
    omega

end OrbitSperner
