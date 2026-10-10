import Upper4846

set_option maxHeartbeats 1000000
namespace Coordinate4846
/-- Standard coarse comparison, including a permitted additive linear term. -/
def CoarseLE (f g : ℕ → ℕ) : Prop :=
  ∃ C : ℕ, 1≤C ∧ ∀ n : ℕ, f n ≤ C * g (C*n+C)+C*n+C
def CoarseEquivalent (f g : ℕ → ℕ) : Prop := CoarseLE f g ∧ CoarseLE g f
/-- The canonical integer rounding of the polynomial growth function n^(3/2). -/
def threeHalves (n : ℕ) : ℕ := Nat.sqrt (n^3)
theorem threeHalves_characterization (n : ℕ) :
  (threeHalves n)^2 ≤ n^3 ∧ n^3 < (threeHalves n+1)^2 := by
  exact ⟨Nat.sqrt_le' _,by simpa only [threeHalves,pow_two] using Nat.lt_succ_sqrt (n^3)⟩
theorem threeHalves_mono : Monotone threeHalves := by
  intro m n hmn
  exact Nat.sqrt_le_sqrt (Nat.pow_le_pow_left hmn 3)
theorem hLength_identity : hLength (1:G)=0 := by
  have h := wordLength_le hletter ([] : List HLetter)
  simpa only [eval_nil,List.length_nil,hLength,Nat.le_zero] using h
theorem gLength_zero_iff (u : G) : gLength u=0 ↔ u=1 := by
  constructor
  · intro h
    rcases gLength_spec u with ⟨w,hw,he⟩
    have : w=[] := List.length_eq_zero_iff.mp (hw.trans h)
    subst w
    exact he.symm
  · rintro rfl
    have h := wordLength_le gletter ([] : List GLetter)
    simpa only [eval_nil,List.length_nil,gLength,Nat.le_zero] using h
theorem distortion_zero : distortion 0=0 := by
  apply Nat.le_zero.mp
  apply distortion_le
  intro u hu hg
  have he := (gLength_zero_iff u).mp (Nat.le_zero.mp hg)
  subst u
  simp [hLength_identity]
theorem distortion_upper_rounded (n : ℕ) : distortion n ≤ 23*(threeHalves n+1) := by
  by_cases hn : n=0
  · subst n; simp [distortion_zero]
  · have hb := distortion_upper_square n (Nat.pos_of_ne_zero hn)
    have hs := (threeHalves_characterization n).2
    have htarget : (distortion n)^2 < (23*(threeHalves n+1))^2 := by nlinarith
    nlinarith
theorem threeHalves_le_distortion (m : ℕ) : threeHalves m ≤ distortion (10*m) := by
  have h := Nat.sqrt_le_sqrt (distortion_cubic_lower m)
  simpa only [threeHalves,Nat.sqrt_eq'] using h
theorem distortion_lower_all_radii (n : ℕ) : threeHalves (n/10) ≤ distortion n := by
  have h := threeHalves_le_distortion (n/10)
  exact h.trans (distortion_mono (Nat.mul_div_le n 10))
theorem distortion_equiv_threeHalves : CoarseEquivalent distortion threeHalves := by
  constructor
  · refine ⟨23,by omega,?_⟩
    intro n
    have hu := distortion_upper_rounded n
    have hs : threeHalves n ≤ threeHalves (23*n+23) := threeHalves_mono (by omega)
    nlinarith
  · refine ⟨10,by omega,?_⟩
    intro n
    have h := (threeHalves_le_distortion n).trans (distortion_mono (show 10*n≤10*n+10 by omega))
    omega
theorem linear_le_mul (a b m : ℕ) (hm : 1≤m) : a*m+b ≤ (a+b)*m := by
  have h := Nat.mul_le_mul_left b hm
  nlinarith
theorem comparison_linear_bound (C m : ℕ) (hm : 1≤m) :
  C*(C*(10*m)+C)+C*(10*m)+C ≤ (11*C^2+11*C)*m := by
  have h := linear_le_mul (10*C^2+10*C) (C^2+C) m hm
  nlinarith
theorem distortion_not_coarse_linear : ¬ CoarseLE distortion (fun n => n) := by
  rintro ⟨C,hC,h⟩
  let D := 11*C^2+11*C
  let m := D^2+1
  have hm : 1≤m := by dsimp [m]; omega
  have hd : distortion (10*m) ≤ D*m := (h (10*m)).trans (comparison_linear_bound C m hm)
  have hh := (distortion_cubic_lower m).trans (Nat.pow_le_pow_left hd 2)
  have he1 : m^3 = m*m^2 := by ring
  have he2 : (D*m)^2 = D^2*m^2 := by ring
  have hp : m*m^2 ≤ D^2*m^2 := by simpa only [he1,he2] using hh
  have hm2 : 0<m^2 := by nlinarith
  have hsmall := Nat.le_of_mul_le_mul_right hp hm2
  dsimp [m] at hsmall
  omega
theorem comparison_rhs_square_bound (C n : ℕ) (hC : 1≤C) (hn : 1≤n) :
  (C*distortion (C*n+C)+C*n+C)^2 ≤ (12000*C^5+6*C^2)*n^3 := by
  have harg : C*n+C ≤ 2*C*n := by
    have h := linear_le_mul C C n hn
    nlinarith
  have hpos : 1≤C*n+C := by omega
  have hD := distortion_upper_square (C*n+C) hpos
  have hd : C^2*(distortion (C*n+C))^2 ≤ 4000*C^5*n^3 := calc
    _ ≤ C^2*(500*(C*n+C)^3) := Nat.mul_le_mul_left _ hD
    _ ≤ C^2*(500*(2*C*n)^3) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left 500 (Nat.pow_le_pow_left harg 3))
    _ = _ := by ring
  have hnn : n^2 ≤ n^3 := Nat.pow_le_pow_right hn (by omega)
  have hone : 1≤n^3 := Nat.one_le_pow 3 n hn
  have hsecond : (C*n)^2 ≤ C^2*n^3 := by
    simpa only [mul_pow] using Nat.mul_le_mul_left (C^2) hnn
  have hthird : C^2 ≤ C^2*n^3 := by
    simpa only [mul_one] using Nat.mul_le_mul_left (C^2) hone
  calc
    _ ≤ 3*((C*distortion (C*n+C))^2+(C*n)^2+C^2) := square_sum_three _ _ _
    _ ≤ 3*(4000*C^5*n^3+C^2*n^3+C^2*n^3) := by
      apply Nat.mul_le_mul_left
      apply Nat.add_le_add
      · apply Nat.add_le_add
        · simpa only [mul_pow] using hd
        · exact hsecond
      · exact hthird
    _ = _ := by ring
theorem power_not_coarse_distortion (k : ℕ) (hk : 2≤k) :
  ¬ CoarseLE (fun n => n^k) distortion := by
  rintro ⟨C,hC,h⟩
  let K := 12000*C^5+6*C^2
  let n := K+1
  have hn : 1≤n := by dsimp [n]; omega
  have hpow : n^2≤n^k := Nat.pow_le_pow_right hn hk
  have hlin := hpow.trans (h n)
  have hs := (Nat.pow_le_pow_left hlin 2).trans (comparison_rhs_square_bound C n hC hn)
  have he : (n^2)^2=n*n^3 := by ring
  have hp : n*n^3 ≤ K*n^3 := by simpa only [he] using hs
  have hn3 : 0<n^3 := Nat.pow_pos hn
  have hsmall := Nat.le_of_mul_le_mul_right hp hn3
  dsimp [n] at hsmall
  omega
theorem integer_exclusion : ∀ k : ℕ, 0<k → ¬ CoarseEquivalent distortion (fun n => n^k) := by
  intro k hk h
  by_cases hk1 : k=1
  · subst k
    exact distortion_not_coarse_linear (by simpa only [pow_one] using h.1)
  · exact power_not_coarse_distortion k (by omega) h.2

/-- Source-faithful counterexample to the integer-only polynomial spectrum conjunct. -/
theorem original4846_counterexample :
  Function.Injective inclusion ∧ inclusion.range=H ∧
  (∀ u : G, ∃ w : List GLetter, eval gletter w=u) ∧
  (∀ u : G, u∈H → ∃ w : List HLetter, eval hletter w=u) ∧
  (∀ n : ℕ, ∃ u : G, u∈H ∧ gLength u≤n ∧ hLength u=distortion n) ∧
  CoarseEquivalent distortion threeHalves ∧
  (∀ k : ℕ, 0<k → ¬ CoarseEquivalent distortion (fun n => n^k)) := by
  exact ⟨inclusion_injective,inclusion_range,ambient_generation,intrinsic_generation,
    distortion_attained,distortion_equiv_threeHalves,integer_exclusion⟩

end Coordinate4846
