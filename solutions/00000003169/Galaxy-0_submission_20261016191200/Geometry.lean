import Algebra
open Lean.Grind Std
namespace TLMC3169
section Geometry
variable {R : Type} [Field R] [LE R] [LT R] [LawfulOrderLT R] [IsLinearOrder R] [OrderedRing R]
def Triangle (k x y : R) : Prop := 0 ≤ x ∧ 0 ≤ y ∧ x+y ≤ k
-- Convex combinations of the actual exponent supports of f and g.
def NewtonF (x y : R) : Prop := ∃ a b c : R,
  0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a+b+c=1 ∧ x=b ∧ y=c
def NewtonG (x y : R) : Prop := ∃ a b c d e f g : R,
  0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ d ∧ 0 ≤ e ∧ 0 ≤ f ∧ 0 ≤ g ∧
  a+b+c+d+e+f+g=1 ∧ x=b+3*d+2*e+f ∧ y=c+e+2*f+3*g
-- Generic convex hull of a finite exponent support, by nonnegative weights.
def ConvexHullSupport (p : List Exponent) (x y : R) : Prop := ∃ w : Exponent → R,
  (∀ v, v ∈ p → 0 ≤ w v) ∧
  (p.map w).foldr (·+·) 0=1 ∧
  (p.map (fun v => w v * @NatCast.natCast R (Semiring.natCast (α := R)) v.1)).foldr (·+·) 0=x ∧
  (p.map (fun v => w v * @NatCast.natCast R (Semiring.natCast (α := R)) v.2)).foldr (·+·) 0=y
theorem support_f_hull (x y : R) : ConvexHullSupport (support fPoly) x y ↔ NewtonF x y := by
  constructor
  · rintro ⟨w,hw,hs,hx,hy⟩
    have ha := hw (0,0) (by simp [f_support])
    have hb := hw (1,0) (by simp [f_support])
    have hc := hw (0,1) (by simp [f_support])
    simp only [f_support,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil] at hs hx hy
    refine ⟨w (0,0),w (1,0),w (0,1),ha,hb,hc,?_,?_,?_⟩ <;> grind
  · rintro ⟨a,b,c,ha,hb,hc,hs,hx,hy⟩
    refine ⟨(fun v => match v with | (0,0) => a | (1,0) => b | _ => c),?_,?_,?_,?_⟩
    · intro v hv
      simp only [f_support,List.mem_cons,List.not_mem_nil,or_false] at hv
      rcases hv with rfl | rfl | rfl <;> assumption
    all_goals simp only [f_support,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil]; grind
theorem support_g_hull (x y : R) : ConvexHullSupport (support gPoly) x y ↔ NewtonG x y := by
  constructor
  · rintro ⟨w,hw,hs,hx,hy⟩
    have ha := hw (0,0) (by simp [g_support])
    have hb := hw (1,0) (by simp [g_support])
    have hc := hw (0,1) (by simp [g_support])
    have hd := hw (3,0) (by simp [g_support])
    have he := hw (2,1) (by simp [g_support])
    have hf := hw (1,2) (by simp [g_support])
    have hg := hw (0,3) (by simp [g_support])
    simp only [g_support,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil] at hs hx hy
    refine ⟨w (0,0),w (1,0),w (0,1),w (3,0),w (2,1),w (1,2),w (0,3),ha,hb,hc,hd,he,hf,hg,?_,?_,?_⟩ <;> grind
  · rintro ⟨a,b,c,d,e,f,g,ha,hb,hc,hd,he,hf,hg,hs,hx,hy⟩
    refine ⟨(fun v => match v with | (0,0) => a | (1,0) => b | (0,1) => c | (3,0) => d | (2,1) => e | (1,2) => f | _ => g),?_,?_,?_,?_⟩
    · intro v hv
      simp only [g_support,List.mem_cons,List.not_mem_nil,or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
    all_goals simp only [g_support,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil]; grind
theorem newtonF_triangle (x y : R) : NewtonF x y ↔ Triangle 1 x y := by
  constructor
  · rintro ⟨a,b,c,ha,hb,hc,hs,hx,hy⟩
    unfold Triangle
    grind
  · rintro ⟨hx,hy,hxy⟩
    refine ⟨1-x-y,x,y,?_,hx,hy,?_,rfl,rfl⟩ <;> grind
theorem newtonG_triangle (x y : R) : NewtonG x y ↔ Triangle 3 x y := by
  constructor
  · rintro ⟨a,b,c,d,e,f,g,ha,hb,hc,hd,he,hf,hg,hs,hx,hy⟩
    unfold Triangle
    grind
  · rintro ⟨hx,hy,hxy⟩
    refine ⟨1-x/3-y/3,0,0,x/3,0,0,y/3,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> grind
-- A literal Minkowski sum: coordinates are sums of points in the two sets.
def Minkowski (P Q : R → R → Prop) (x y : R) : Prop :=
  ∃ a b c d : R, P a b ∧ Q c d ∧ x=a+c ∧ y=b+d
theorem minkowski_newton (x y : R) : Minkowski NewtonF NewtonG x y ↔ Triangle 4 x y := by
  constructor
  · rintro ⟨a,b,c,d,hp,hq,hx,hy⟩
    have hp' := (newtonF_triangle a b).mp hp
    have hq' := (newtonG_triangle c d).mp hq
    unfold Triangle at *
    grind
  · rintro ⟨hx,hy,hxy⟩
    refine ⟨x/4,y/4,3*x/4,3*y/4,?_,?_,?_,?_⟩
    · apply (newtonF_triangle _ _).mpr
      unfold Triangle
      grind
    · apply (newtonG_triangle _ _).mpr
      unfold Triangle
      grind
    · grind
    · grind
theorem actual_newton_minkowski (x y : R) :
  Minkowski (ConvexHullSupport (support fPoly)) (ConvexHullSupport (support gPoly)) x y ↔ Triangle 4 x y := by
  simp only [Minkowski,support_f_hull,support_g_hull]
  exact minkowski_newton x y
-- Determinant (twice signed area) for an oriented triangle.
def twiceArea (a b c : R × R) : R :=
  (b.1-a.1)*(c.2-a.2)-(b.2-a.2)*(c.1-a.1)
def triangleArea (k : R) : R := twiceArea (0,0) (k,0) (0,k) / 2
omit [LE R] [LT R] [LawfulOrderLT R] [IsLinearOrder R] [OrderedRing R] in
theorem triangle_area_formula (k : R) : triangleArea k = k*k/2 := by
  unfold triangleArea twiceArea
  grind
theorem mixed_area_values :
  triangleArea (4:R)-triangleArea (1:R)-triangleArea (3:R)=3 ∧
  (triangleArea (4:R)-triangleArea (1:R)-triangleArea (3:R))/2=3/2 := by
  simp only [triangle_area_formula]
  grind
theorem both_mixed_values_differ_from_one :
  triangleArea (4:R)-triangleArea (1:R)-triangleArea (3:R) ≠ 1 ∧
  (triangleArea (4:R)-triangleArea (1:R)-triangleArea (3:R))/2 ≠ 1 := by
  have := mixed_area_values (R := R)
  grind
end Geometry
end TLMC3169
