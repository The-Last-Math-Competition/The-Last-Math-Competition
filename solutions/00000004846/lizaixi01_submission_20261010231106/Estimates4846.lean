import Lengths4846
import Mathlib.Data.Nat.Sqrt

set_option maxHeartbeats 2000000

namespace Coordinate4846
theorem abs_one_add (z : ℤ) : (1+z).natAbs ≤ z.natAbs+1 := by
  simpa only [Int.natAbs_one,add_comm] using Int.natAbs_add_le 1 z
theorem abs_neg_one_add (z : ℤ) : (-1+z).natAbs ≤ z.natAbs+1 := by
  simpa only [Int.natAbs_neg,Int.natAbs_one,add_comm] using Int.natAbs_add_le (-1) z
def AmbientBounds (u : G) (n : ℕ) : Prop :=
  u.p.natAbs ≤ n ∧ u.q.natAbs ≤ n ∧ u.r.natAbs ≤ n ∧
  u.a.natAbs ≤ n ∧ u.b.natAbs ≤ n ∧ u.s.natAbs ≤ n^2 ∧
  u.t.natAbs ≤ n^2 ∧ u.c.natAbs ≤ 2*n^3
theorem ambient_step (l : GLetter) (u : G) :
  (gletter l*u).p.natAbs ≤ u.p.natAbs+1 ∧
  (gletter l*u).q.natAbs ≤ u.q.natAbs+1 ∧
  (gletter l*u).r.natAbs ≤ u.r.natAbs+1 ∧
  (gletter l*u).a.natAbs ≤ u.a.natAbs+1 ∧
  (gletter l*u).b.natAbs ≤ u.b.natAbs+1 ∧
  (gletter l*u).s.natAbs ≤ u.s.natAbs+u.q.natAbs ∧
  (gletter l*u).t.natAbs ≤ u.t.natAbs+u.r.natAbs ∧
  (gletter l*u).c.natAbs ≤ u.c.natAbs+u.t.natAbs+u.b.natAbs := by
  cases l <;> simp [mul_def,product,gletter,X,Y,Z,A,B]
  all_goals repeat' apply And.intro
  all_goals first
    | omega
    | exact abs_one_add _
    | exact abs_neg_one_add _
    | (apply le_trans (Int.natAbs_add_le _ _); try simp only [Int.natAbs_neg,Int.natAbs_one]; omega)
theorem ambient_bounds (w : List GLetter) : AmbientBounds (eval gletter w) w.length := by
  induction w with
  | nil => simp [AmbientBounds,one_def,unit]
  | cons l w ih =>
    rcases ih with ⟨hp,hq,hr,ha,hb,hs,ht,hc⟩
    rcases ambient_step l (eval gletter w) with ⟨hP,hQ,hR,hA,hB,hS,hT,hC⟩
    change AmbientBounds (gletter l * eval gletter w) (w.length+1)
    refine ⟨by omega,by omega,by omega,by omega,by omega,?_,?_,?_⟩
    · nlinarith
    · nlinarith
    · nlinarith
def IntrinsicBounds (u : G) (n : ℕ) : Prop :=
  u.a.natAbs ≤ n ∧ u.b.natAbs ≤ n ∧ u.c.natAbs ≤ n^2
theorem intrinsic_step (l : HLetter) (u : G) :
  (hletter l*u).a.natAbs ≤ u.a.natAbs+1 ∧
  (hletter l*u).b.natAbs ≤ u.b.natAbs+1 ∧
  (hletter l*u).c.natAbs ≤ u.c.natAbs+u.b.natAbs := by
  cases l <;> simp [mul_def,product,hletter,A,B]
  all_goals repeat' apply And.intro
  all_goals first
    | omega
    | exact abs_one_add _
    | exact abs_neg_one_add _
    | (apply le_trans (Int.natAbs_add_le _ _); try simp only [Int.natAbs_neg,Int.natAbs_one]; omega)
theorem intrinsic_bounds (w : List HLetter) : IntrinsicBounds (eval hletter w) w.length := by
  induction w with
  | nil => simp [IntrinsicBounds,one_def,unit]
  | cons l w ih =>
    rcases ih with ⟨ha,hb,hc⟩
    rcases intrinsic_step l (eval hletter w) with ⟨hA,hB,hC⟩
    change IntrinsicBounds (hletter l * eval hletter w) (w.length+1)
    refine ⟨by omega,by omega,?_⟩
    nlinarith
theorem ambient_minimum_bounds (u : G) : AmbientBounds u (gLength u) := by
  rcases gLength_spec u with ⟨w,hlen,heval⟩
  simpa only [hlen,heval] using ambient_bounds w
theorem intrinsic_minimum_bounds (u : G) (hu : u ∈ H) : IntrinsicBounds u (hLength u) := by
  rcases hLength_spec u hu with ⟨w,hlen,heval⟩
  simpa only [hlen,heval] using intrinsic_bounds w
theorem central_intrinsic_lower (k : ℤ) : k.natAbs ≤ (hLength (C k))^2 := by
  exact (intrinsic_minimum_bounds (C k) (C_mem k)).2.2
def nestedWord (m : ℕ) : List GLetter :=
  commWord ginvert (commWord ginvert (xword (m:ℤ)) (yword (m:ℤ))) (zword (m:ℤ))
theorem nestedWord_eval (m : ℕ) : eval gletter (nestedWord m) = C ((m:ℤ)^3) := by
  simp only [nestedWord,commWord_eval gletter ginvert ginvert_eval,xword_eval,yword_eval,zword_eval]
  exact nested_comm _
theorem nestedWord_length (m : ℕ) : (nestedWord m).length = 10*m := by
  simp only [nestedWord,commWord_length,xword,yword,zword,intWord_length,Int.natAbs_natCast]
  ring
theorem central_ambient_upper (m : ℕ) : gLength (C ((m:ℤ)^3)) ≤ 10*m := by
  have h := wordLength_le gletter (nestedWord m)
  simpa only [gLength,nestedWord_eval,nestedWord_length] using h
theorem distortion_cubic_lower (m : ℕ) : m^3 ≤ (distortion (10*m))^2 := by
  have hi := central_intrinsic_lower ((m:ℤ)^3)
  have hd := le_distortion (C ((m:ℤ)^3)) (C_mem _) (10*m) (central_ambient_upper m)
  have hs := Nat.pow_le_pow_left hd 2
  simpa only [Int.natAbs_pow,Int.natAbs_natCast] using hi.trans hs

end Coordinate4846
