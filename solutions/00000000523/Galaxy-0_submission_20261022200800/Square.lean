import Std
namespace TLMC523Square
/-- A list represents a finite sum of Laurent monomials over F₂. Repetition cancels. -/
def coeff : List Int → Int → Bool
| [], _ => false
| a::as, k => decide (a=k) ^^ coeff as k
/-- Coefficient of a monomial times a finite Laurent sum. -/
def row (a : Int) : List Int → Int → Bool
| [], _ => false
| b::bs, k => decide (a+b=k) ^^ row a bs k
/-- The ordinary finite convolution product, coefficient by coefficient. -/
def conv : List Int → List Int → Int → Bool
| [], _, _ => false
| a::as, bs, k => row a bs k ^^ conv as bs k

theorem conv_nil (as : List Int) (k : Int) : conv as [] k = false := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [conv,row,ih]

theorem conv_cons (as : List Int) (b : Int) (bs : List Int) (k : Int) :
    conv as (b::bs) k = (row b as k ^^ conv as bs k) := by
  induction as with
  | nil => simp [conv,row]
  | cons a as ih =>
    simp only [conv,row,ih,Int.add_comm a b]
    cases decide (b+a=k) <;> cases row a bs k <;> cases row b as k <;> cases conv as bs k <;> decide

theorem conv_comm (as bs : List Int) (k : Int) : conv as bs k = conv bs as k := by
  induction as with
  | nil => simp [conv,conv_nil]
  | cons a as ih => rw [conv,conv_cons,ih]

theorem convolution_square (as : List Int) (k : Int) :
    conv as as k = coeff (as.map (fun a => 2*a)) k := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    simp only [conv,row,conv_cons,List.map_cons,coeff]
    rw [ih]
    have h : a+a = 2*a := by omega
    rw [h]
    cases decide (2*a=k) <;> cases row a as k <;> cases coeff (as.map (fun a => 2*a)) k <;> decide

theorem doubled_coeff (as : List Int) (k : Int) :
    coeff (as.map (fun a => 2*a)) k =
      (if k % 2 = 0 then coeff as (k/2) else false) := by
  induction as with
  | nil => simp [coeff]
  | cons a as ih =>
    simp only [List.map_cons,coeff,ih]
    split <;> rename_i h
    · have he : 2*a=k ↔ a=k/2 := by omega
      simp [he]
    · have he : ¬ 2*a=k := by omega
      simp [he]

theorem square_frobenius (as : List Int) (k : Int) :
    conv as as k = (if k % 2 = 0 then coeff as (k/2) else false) := by
  rw [convolution_square,doubled_coeff]

def mulList (as bs : List Int) : List Int := as.flatMap (fun a => bs.map (fun b => a+b))

theorem coeff_append (as bs : List Int) (k : Int) :
    coeff (as++bs) k = (coeff as k ^^ coeff bs k) := by
  induction as with
  | nil => simp [coeff]
  | cons a as ih => simp [coeff,ih]

theorem coeff_map_add (a : Int) (bs : List Int) (k : Int) :
    coeff (bs.map (fun b => a+b)) k = row a bs k := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [coeff,row,ih]

theorem coeff_mulList (as bs : List Int) (k : Int) :
    coeff (mulList as bs) k = conv as bs k := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [mulList,List.flatMap_cons,coeff_append,coeff_map_add,conv,← ih]
end TLMC523Square
