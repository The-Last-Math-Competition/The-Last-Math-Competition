import ThreeCore

namespace TLMC3322.Triangle
open ThreePoly

abbrev Free2 := Poly × Poly
abbrev Free3 := Poly × Poly × Poly

def zero2 : Free2 := (zero,zero)
def zero3 : Free3 := (zero,zero,zero)
def add2 (v w : Free2) : Free2 := (add v.1 w.1,add v.2 w.2)
def add3 (v w : Free3) : Free3 :=
  (add v.1 w.1,add v.2.1 w.2.1,add v.2.2 w.2.2)

def differential1 (v : Free3) : Poly :=
  add (add (xMul (yMul v.1)) (xMul (zMul v.2.1))) (yMul (zMul v.2.2))

def differential2 (v : Free2) : Free3 :=
  (zMul (add v.1 v.2), yMul v.1, xMul v.2)

def InIdeal (p : Poly) : Prop := ∃ v : Free3, p = differential1 v

@[simp] theorem differential1_zero : differential1 zero3 = zero := by
  simp [differential1,zero3]
@[simp] theorem differential2_zero : differential2 zero2 = zero3 := by
  simp [differential2,zero2,zero3]

theorem differential1_add (v w : Free3) :
    differential1 (add3 v w) = add (differential1 v) (differential1 w) := by
  apply Poly.ext
  intro i j k
  simp only [differential1,add3,xMul_add,yMul_add,zMul_add,add_coeff]
  generalize (xMul (yMul v.1)).coeff i j k = a
  generalize (xMul (zMul v.2.1)).coeff i j k = b
  generalize (yMul (zMul v.2.2)).coeff i j k = c
  generalize (xMul (yMul w.1)).coeff i j k = d
  generalize (xMul (zMul w.2.1)).coeff i j k = e
  generalize (yMul (zMul w.2.2)).coeff i j k = f
  revert a b c d e f; decide

theorem differential2_add (v w : Free2) :
    differential2 (add2 v w) = add3 (differential2 v) (differential2 w) := by
  apply Prod.ext
  · apply Poly.ext
    intro i j k
    cases k with
    | zero => rfl
    | succ k =>
      change ((v.1.coeff i j k ^^ w.1.coeff i j k) ^^
        (v.2.coeff i j k ^^ w.2.coeff i j k)) =
        ((v.1.coeff i j k ^^ v.2.coeff i j k) ^^
        (w.1.coeff i j k ^^ w.2.coeff i j k))
      generalize v.1.coeff i j k = a; generalize v.2.coeff i j k = b
      generalize w.1.coeff i j k = c; generalize w.2.coeff i j k = d
      revert a b c d; decide
  · exact Prod.ext (yMul_add _ _) (xMul_add _ _)

theorem composition_zero (v : Free2) : differential1 (differential2 v) = zero := by
  apply Poly.ext
  intro i j k
  cases i <;> cases j <;> cases k <;> simp [differential1,differential2]
  have hb : ∀ a b : Bool, a = (b ^^ (a ^^ b)) := by decide
  exact hb _ _

theorem differential2_injective {v w : Free2}
    (h : differential2 v = differential2 w) : v = w := by
  apply Prod.ext
  · exact yMul_injective (congrArg (fun u : Free3 => u.2.1) h)
  · exact xMul_injective (congrArg (fun u : Free3 => u.2.2) h)

/-- Direct coefficient proof, for arbitrary finite-support polynomials. -/
theorem kernel_exact (v : Free3) :
    differential1 v = zero ↔ ∃ u : Free2, differential2 u = v := by
  constructor
  · intro hv
    have hc : ∀ j k, v.2.2.coeff 0 j k = false := by
      intro j k
      have h := congrArg (fun p : Poly => p.coeff 0 (j+1) (k+1)) hv
      simpa [differential1] using h
    let c' := dropX v.2.2
    have hec : xMul c' = v.2.2 := dropX_cancel v.2.2 hc
    have he : add (add (yMul v.1) (zMul v.2.1)) (yMul (zMul c')) = zero := by
      apply xMul_injective
      rw [xMul_zero, xMul_add, xMul_add]
      rw [xMul_yMul (zMul c'), xMul_zMul c', hec]
      exact hv
    have hb : ∀ i k, v.2.1.coeff i 0 k = false := by
      intro i k
      have h := congrArg (fun p : Poly => p.coeff i 0 (k+1)) he
      simpa using h
    let b' := dropY v.2.1
    have heb : yMul b' = v.2.1 := dropY_cancel v.2.1 hb
    have hea : zMul (add b' c') = v.1 := by
      apply Poly.ext
      intro i j k
      have h := congrArg (fun p : Poly => p.coeff i (j+1) k) he
      rw [← heb] at h
      cases k with
      | zero =>
        simpa using h.symm
      | succ k =>
        simp only [add_coeff,yMul_coeff_succ,zMul_coeff_succ] at h ⊢
        have bool_identity : ∀ a b c : Bool, ((a ^^ b) ^^ c) = false → (b ^^ c) = a := by decide
        exact bool_identity _ _ _ h
    exact ⟨(b',c'), Prod.ext hea (Prod.ext heb hec)⟩
  · rintro ⟨u,rfl⟩
    exact composition_zero u

theorem ideal_zero : InIdeal zero := ⟨zero3,differential1_zero.symm⟩
theorem ideal_add {p q : Poly} (hp : InIdeal p) (hq : InIdeal q) : InIdeal (add p q) := by
  obtain ⟨v,rfl⟩ := hp
  obtain ⟨w,rfl⟩ := hq
  exact ⟨add3 v w,(differential1_add v w).symm⟩

end TLMC3322.Triangle
