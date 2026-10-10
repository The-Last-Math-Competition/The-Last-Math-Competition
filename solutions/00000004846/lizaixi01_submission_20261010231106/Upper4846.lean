import Estimates4846

set_option maxHeartbeats 1000000
namespace Coordinate4846
theorem C_add (x y : ℤ) : C (x+y) = C x * C y := by
  ext <;> simp [mul_def,product,C]
theorem C_inverse (x : ℤ) : (C x)⁻¹ = C (-x) := by
  ext <;> simp [inv_def,inverse,C]
def positiveCentralWord (M : ℕ) : List HLetter :=
  commWord hinvert (haword (M.sqrt:ℤ)) (hbword ((M/M.sqrt:ℕ):ℤ)) ++
  commWord hinvert (haword ((M%M.sqrt:ℕ):ℤ)) (hbword 1)
theorem positiveCentralWord_eval (M : ℕ) :
  eval hletter (positiveCentralWord M) = C (M:ℤ) := by
  simp only [positiveCentralWord,eval_append,commWord_eval hletter hinvert hinvert_eval,
    haword_eval,hbword_eval,comm_AB,mul_one]
  rw [←C_add]
  congr 1
  exact_mod_cast Nat.div_add_mod M M.sqrt
theorem positiveCentralWord_length (M : ℕ) :
  (positiveCentralWord M).length ≤ 6*M.sqrt+6 := by
  simp only [positiveCentralWord,List.length_append,commWord_length,haword,hbword,
    intWord_length,Int.natAbs_natCast,Int.natAbs_one]
  by_cases hM : M=0
  · subst M; norm_num
  · have hu : 0 < M.sqrt := Nat.sqrt_pos.mpr (Nat.pos_of_ne_zero hM)
    have hMs := Nat.sqrt_le_add M
    have hv : M/M.sqrt ≤ M.sqrt+2 := by
      apply Nat.le_of_lt_succ
      apply (Nat.div_lt_iff_lt_mul hu).mpr
      nlinarith
    have hr := Nat.mod_lt M hu
    omega
def shortCentralWord : ℤ → List HLetter
  | .ofNat M => positiveCentralWord M
  | .negSucc n => invWord hinvert (positiveCentralWord (n+1))
theorem shortCentralWord_eval (d : ℤ) : eval hletter (shortCentralWord d) = C d := by
  cases d with
  | ofNat M => exact positiveCentralWord_eval M
  | negSucc n =>
    simp only [shortCentralWord,invWord_eval hletter hinvert hinvert_eval,
      positiveCentralWord_eval,C_inverse]
    congr 1
theorem shortCentralWord_length (d : ℤ) :
  (shortCentralWord d).length ≤ 6*d.natAbs.sqrt+6 := by
  cases d with
  | ofNat M => exact positiveCentralWord_length M
  | negSucc n =>
    simpa only [shortCentralWord,invWord_length,Int.natAbs_negSucc] using positiveCentralWord_length (n+1)
theorem intrinsic_constructive_upper (u : G) (hu : u ∈ H) :
  hLength u ≤ u.a.natAbs+u.b.natAbs+6*(u.c-u.a*u.b).natAbs.sqrt+6 := by
  let w := haword u.a ++ hbword u.b ++ shortCentralWord (u.c-u.a*u.b)
  have he : eval hletter w = u := by
    simpa only [w,eval_append,haword_eval,hbword_eval,shortCentralWord_eval] using H_normalForm u hu
  have hl := wordLength_le hletter w
  rw [he] at hl
  have hc := shortCentralWord_length (u.c-u.a*u.b)
  simp only [w,List.length_append,haword,hbword,intWord_length] at hl
  change wordLength hletter u ≤ _
  omega
theorem square_sum_three (x y z : ℕ) :
  (x+y+z)^2 ≤ 3*(x^2+y^2+z^2) := by
  have h : ((x:ℤ)+y+z)^2 ≤ 3*((x:ℤ)^2+(y:ℤ)^2+(z:ℤ)^2) := by
    nlinarith [sq_nonneg ((x:ℤ)-y),sq_nonneg ((x:ℤ)-z),sq_nonneg ((y:ℤ)-z)]
  exact_mod_cast h
theorem radius_coordinate_bounds (u : G) (n : ℕ) (hg : gLength u ≤ n) :
  u.a.natAbs ≤ n ∧ u.b.natAbs ≤ n ∧ u.c.natAbs ≤ 2*n^3 := by
  rcases ambient_minimum_bounds u with ⟨hp,hq,hr,ha,hb,hs,ht,hc⟩
  exact ⟨ha.trans hg,hb.trans hg,hc.trans (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hg 3))⟩
theorem correction_coordinate_bound (u : G) (n : ℕ) (hn : 1≤n) (hg : gLength u ≤ n) :
  (u.c-u.a*u.b).natAbs ≤ 3*n^3 := by
  rcases radius_coordinate_bounds u n hg with ⟨ha,hb,hc⟩
  have hd := Int.natAbs_add_le u.c (-(u.a*u.b))
  simp only [Int.natAbs_neg,Int.natAbs_mul,←sub_eq_add_neg] at hd
  have hab := Nat.mul_le_mul ha hb
  have hnn : n^2 ≤ n^3 := by
    have h := Nat.mul_le_mul_left (n^2) hn
    simpa only [mul_one,pow_succ] using h
  nlinarith
theorem actual_intrinsic_upper_square (u : G) (hu : u ∈ H)
  (n : ℕ) (hn : 1≤n) (hg : gLength u ≤ n) : (hLength u)^2 ≤ 500*n^3 := by
  rcases radius_coordinate_bounds u n hg with ⟨ha,hb,hc⟩
  have hcorr := correction_coordinate_bound u n hn hg
  have hsqrt := Nat.sqrt_le' (u.c-u.a*u.b).natAbs
  have hup := intrinsic_constructive_upper u hu
  have hlen : hLength u ≤ 2*n+6*(u.c-u.a*u.b).natAbs.sqrt+6 := by omega
  have hsq := Nat.pow_le_pow_left hlen 2
  have hthree := square_sum_three (2*n) (6*(u.c-u.a*u.b).natAbs.sqrt) 6
  have hnn : n^2 ≤ n^3 := by
    have h := Nat.mul_le_mul_left (n^2) hn
    simpa only [mul_one,pow_succ] using h
  have hone : 1≤n^3 := by exact Nat.one_le_pow 3 n hn
  nlinarith
theorem distortion_upper_square (n : ℕ) (hn : 1≤n) :
  (distortion n)^2 ≤ 500*n^3 := by
  obtain ⟨u,hu,hg,he⟩ := distortion_attained n
  rw [←he]
  exact actual_intrinsic_upper_square u hu n hn hg

end Coordinate4846
