import Coordinate4846
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.List
import Mathlib.Data.List.Range
import Mathlib.Data.Finset.Lattice.Fold

set_option maxRecDepth 4096
namespace Coordinate4846

inductive GLetter where
  | xp | xm | yp | ym | zp | zm | ap | am | bp | bm
  deriving DecidableEq
inductive HLetter where
  | ap | am | bp | bm
  deriving DecidableEq
instance : Fintype GLetter where
  elems := {.xp,.xm,.yp,.ym,.zp,.zm,.ap,.am,.bp,.bm}
  complete := by intro x; cases x <;> simp
instance : Fintype HLetter where
  elems := {.ap,.am,.bp,.bm}
  complete := by intro x; cases x <;> simp
def gletter : GLetter → G
  | .xp => X 1 | .xm => X (-1) | .yp => Y 1 | .ym => Y (-1)
  | .zp => Z 1 | .zm => Z (-1) | .ap => A 1 | .am => A (-1)
  | .bp => B 1 | .bm => B (-1)
def hletter : HLetter → G
  | .ap => A 1 | .am => A (-1) | .bp => B 1 | .bm => B (-1)
def ginvert : GLetter → GLetter
  | .xp => .xm | .xm => .xp | .yp => .ym | .ym => .yp
  | .zp => .zm | .zm => .zp | .ap => .am | .am => .ap
  | .bp => .bm | .bm => .bp
def hinvert : HLetter → HLetter
  | .ap => .am | .am => .ap | .bp => .bm | .bm => .bp
theorem ginvert_eval (l : GLetter) : gletter (ginvert l) = (gletter l)⁻¹ := by
  cases l <;> ext <;> simp [inv_def,ginvert,gletter,inverse,X,Y,Z,A,B]
theorem hinvert_eval (l : HLetter) : hletter (hinvert l) = (hletter l)⁻¹ := by
  cases l <;> ext <;> simp [inv_def,hinvert,hletter,inverse,A,B]
def eval {α : Type*} (f : α → G) (w : List α) : G := (w.map f).prod
@[simp] theorem eval_nil {α} (f : α → G) : eval f [] = 1 := rfl
@[simp] theorem eval_cons {α} (f : α → G) (x : α) (w : List α) :
  eval f (x::w) = f x * eval f w := rfl
@[simp] theorem eval_append {α} (f : α → G) (u v : List α) :
  eval f (u++v) = eval f u * eval f v := by simp [eval,List.prod_append]
def invWord {α} (i : α → α) (w : List α) : List α := (w.reverse.map i)
@[simp] theorem invWord_length {α} (i : α → α) (w : List α) :
  (invWord i w).length = w.length := by simp [invWord]
theorem invWord_eval {α} (f : α → G) (i : α → α)
  (hi : ∀ x, f (i x) = (f x)⁻¹) (w : List α) :
  eval f (invWord i w) = (eval f w)⁻¹ := by
  induction w with
  | nil => simp [invWord]
  | cons x w ih =>
    simp only [invWord,List.reverse_cons,List.map_append,List.map_cons,List.map_nil]
    change eval f (invWord i w ++ [i x]) = (f x * eval f w)⁻¹
    rw [eval_append,ih]
    simp [hi,mul_inv_rev]
def commWord {α} (i : α → α) (u v : List α) : List α :=
  u++v++invWord i u++invWord i v
theorem commWord_eval {α} (f : α → G) (i : α → α)
  (hi : ∀ x, f (i x) = (f x)⁻¹) (u v : List α) :
  eval f (commWord i u v) = comm (eval f u) (eval f v) := by
  simp only [commWord,eval_append,invWord_eval f i hi,comm]
@[simp] theorem commWord_length {α} (i : α → α) (u v : List α) :
  (commWord i u v).length = 2*u.length+2*v.length := by
  simp [commWord]; omega

def intWord {α} (pos neg : α) : ℤ → List α
  | .ofNat n => List.replicate n pos
  | .negSucc n => List.replicate (n+1) neg
@[simp] theorem intWord_length {α} (pos neg : α) (z : ℤ) :
  (intWord pos neg z).length = z.natAbs := by cases z <;> simp [intWord]
theorem replicate_param {α} (f : α → G) (F : ℤ → G)
  (hzero : F 0 = 1) (hadd : ∀ x y, F (x+y) = F x * F y)
  (l : α) (k : ℤ) (hl : f l = F k) (n : ℕ) :
  eval f (List.replicate n l) = F ((n:ℤ)*k) := by
  induction n with
  | zero => simpa using hzero.symm
  | succ n ih =>
    change f l * eval f (List.replicate n l) = F (((n+1:ℕ):ℤ)*k)
    rw [hl,ih,←hadd]
    congr 1
    push_cast
    ring
theorem intWord_eval {α} (f : α → G) (F : ℤ → G)
  (hzero : F 0 = 1) (hadd : ∀ x y, F (x+y) = F x * F y)
  (pos neg : α) (hp : f pos = F 1) (hm : f neg = F (-1)) (z : ℤ) :
  eval f (intWord pos neg z) = F z := by
  cases z with
  | ofNat n => simpa [intWord] using replicate_param f F hzero hadd pos 1 hp n
  | negSucc n =>
    simpa [intWord,Int.negSucc_eq] using replicate_param f F hzero hadd neg (-1) hm (n+1)

theorem X_zero : X 0 = 1 := rfl
theorem Y_zero : Y 0 = 1 := rfl
theorem Z_zero : Z 0 = 1 := rfl
theorem A_zero : A 0 = 1 := rfl
theorem B_zero : B 0 = 1 := rfl
theorem X_add (x y : ℤ) : X (x+y) = X x * X y := by ext <;> simp [mul_def,product,X]
theorem Y_add (x y : ℤ) : Y (x+y) = Y x * Y y := by ext <;> simp [mul_def,product,Y]
theorem Z_add (x y : ℤ) : Z (x+y) = Z x * Z y := by ext <;> simp [mul_def,product,Z]
theorem A_add (x y : ℤ) : A (x+y) = A x * A y := by ext <;> simp [mul_def,product,A]
theorem B_add (x y : ℤ) : B (x+y) = B x * B y := by ext <;> simp [mul_def,product,B]

def xword := intWord GLetter.xp GLetter.xm
def yword := intWord GLetter.yp GLetter.ym
def zword := intWord GLetter.zp GLetter.zm
def aword := intWord GLetter.ap GLetter.am
def bword := intWord GLetter.bp GLetter.bm
def haword := intWord HLetter.ap HLetter.am
def hbword := intWord HLetter.bp HLetter.bm
@[simp] theorem xword_eval (z : ℤ) : eval gletter (xword z) = X z :=
  intWord_eval gletter X X_zero X_add _ _ rfl rfl z
@[simp] theorem yword_eval (z : ℤ) : eval gletter (yword z) = Y z :=
  intWord_eval gletter Y Y_zero Y_add _ _ rfl rfl z
@[simp] theorem zword_eval (z : ℤ) : eval gletter (zword z) = Z z :=
  intWord_eval gletter Z Z_zero Z_add _ _ rfl rfl z
@[simp] theorem aword_eval (z : ℤ) : eval gletter (aword z) = A z :=
  intWord_eval gletter A A_zero A_add _ _ rfl rfl z
@[simp] theorem bword_eval (z : ℤ) : eval gletter (bword z) = B z :=
  intWord_eval gletter B B_zero B_add _ _ rfl rfl z
@[simp] theorem haword_eval (z : ℤ) : eval hletter (haword z) = A z :=
  intWord_eval hletter A A_zero A_add _ _ rfl rfl z
@[simp] theorem hbword_eval (z : ℤ) : eval hletter (hbword z) = B z :=
  intWord_eval hletter B B_zero B_add _ _ rfl rfl z
def pword (z : ℤ) := commWord ginvert (xword z) (yword 1)
def qword (z : ℤ) := commWord ginvert (yword z) (zword 1)
def cword (z : ℤ) := commWord ginvert (aword z) (bword 1)
def hcword (z : ℤ) := commWord hinvert (haword z) (hbword 1)
@[simp] theorem pword_eval (z : ℤ) : eval gletter (pword z) = P z := by
  simp [pword,commWord_eval gletter ginvert ginvert_eval,comm_XY]
@[simp] theorem qword_eval (z : ℤ) : eval gletter (qword z) = Q z := by
  simp [qword,commWord_eval gletter ginvert ginvert_eval,comm_YZ]
@[simp] theorem cword_eval (z : ℤ) : eval gletter (cword z) = C z := by
  simp [cword,commWord_eval gletter ginvert ginvert_eval,comm_AB]
@[simp] theorem hcword_eval (z : ℤ) : eval hletter (hcword z) = C z := by
  simp [hcword,commWord_eval hletter hinvert hinvert_eval,comm_AB]
def normalWord (u : G) :=
  xword u.p ++ yword u.q ++ zword u.r ++ pword (u.s-u.p*u.q) ++
  qword (u.t-u.q*u.r) ++ aword u.a ++ bword u.b ++ cword (u.c-u.p*u.t-u.a*u.b)
def hnormalWord (u : G) := haword u.a ++ hbword u.b ++ hcword (u.c-u.a*u.b)
theorem normalWord_eval (u : G) : eval gletter (normalWord u) = u := by
  simpa only [normalWord,eval_append,xword_eval,yword_eval,zword_eval,pword_eval,qword_eval,
    aword_eval,bword_eval,cword_eval] using normalForm u
theorem hnormalWord_eval (u : G) (hu : u ∈ H) : eval hletter (hnormalWord u) = u := by
  simpa only [hnormalWord,eval_append,haword_eval,hbword_eval,hcword_eval] using H_normalForm u hu
theorem ambient_generation : ∀ u : G, ∃ w : List GLetter, eval gletter w = u :=
  fun u => ⟨normalWord u,normalWord_eval u⟩
theorem intrinsic_generation : ∀ u : G, u ∈ H → ∃ w : List HLetter, eval hletter w = u :=
  fun u hu => ⟨hnormalWord u,hnormalWord_eval u hu⟩
theorem hletter_mem (l : HLetter) : hletter l ∈ H := by cases l <;> simp [hletter,A,B]
theorem eval_h_mem (w : List HLetter) : eval hletter w ∈ H := by
  induction w with
  | nil => exact H.one_mem
  | cons x w ih => exact H.mul_mem (hletter_mem x) ih

end Coordinate4846
