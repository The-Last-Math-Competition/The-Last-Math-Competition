import Words4846

namespace Coordinate4846
def Represents {α} (f : α → G) (u : G) (n : ℕ) : Prop :=
  ∃ w : List α, w.length = n ∧ eval f w = u
noncomputable def wordLength {α} (f : α → G) (u : G) : ℕ := by
  classical
  exact if h : ∃ n, Represents f u n then Nat.find h else 0
theorem represents_exists {α} (f : α → G) (u : G)
  (h : ∃ w : List α, eval f w = u) : ∃ n, Represents f u n := by
  rcases h with ⟨w,hw⟩; exact ⟨w.length,w,rfl,hw⟩
theorem wordLength_spec {α} (f : α → G) (u : G)
  (h : ∃ w : List α, eval f w = u) : Represents f u (wordLength f u) := by
  classical
  have hx := represents_exists f u h
  simpa only [wordLength,dif_pos hx] using Nat.find_spec hx
theorem wordLength_le {α} (f : α → G) (w : List α) :
  wordLength f (eval f w) ≤ w.length := by
  classical
  have hx : ∃ n, Represents f (eval f w) n := ⟨w.length,w,rfl,rfl⟩
  simpa only [wordLength,dif_pos hx] using Nat.find_min' hx ⟨w,rfl,rfl⟩
theorem wordLength_le_iff {α} (f : α → G) (u : G)
  (h : ∃ w : List α, eval f w = u) (n : ℕ) :
  wordLength f u ≤ n ↔ ∃ w : List α, w.length ≤ n ∧ eval f w = u := by
  constructor
  · intro hn
    rcases wordLength_spec f u h with ⟨w,hlen,heval⟩
    exact ⟨w,hlen ▸ hn,heval⟩
  · rintro ⟨w,hw,rfl⟩; exact (wordLength_le f w).trans hw
noncomputable def gLength := wordLength gletter
noncomputable def hLength := wordLength hletter
theorem gLength_spec (u : G) : Represents gletter u (gLength u) :=
  wordLength_spec gletter u (ambient_generation u)
theorem hLength_spec (u : G) (hu : u ∈ H) : Represents hletter u (hLength u) :=
  wordLength_spec hletter u (intrinsic_generation u hu)
theorem gLength_le_iff (u : G) (n : ℕ) :
  gLength u ≤ n ↔ ∃ w : List GLetter, w.length ≤ n ∧ eval gletter w = u :=
  wordLength_le_iff gletter u (ambient_generation u) n
theorem hLength_le_iff (u : G) (hu : u ∈ H) (n : ℕ) :
  hLength u ≤ n ↔ ∃ w : List HLetter, w.length ≤ n ∧ eval hletter w = u :=
  wordLength_le_iff hletter u (intrinsic_generation u hu) n

def wordsUpTo (α : Type*) [Fintype α] [DecidableEq α] : ℕ → Finset (List α)
  | 0 => {[]}
  | n+1 => {[]} ∪ Finset.univ.biUnion (fun a => (wordsUpTo α n).image (List.cons a))
theorem mem_wordsUpTo (α : Type*) [Fintype α] [DecidableEq α] (w : List α) (n : ℕ) :
  w ∈ wordsUpTo α n ↔ w.length ≤ n := by
  induction n generalizing w with
  | zero => cases w <;> simp [wordsUpTo]
  | succ n ih =>
    cases w with
    | nil => simp [wordsUpTo]
    | cons x w =>
      constructor
      · intro hw
        simp only [wordsUpTo,Finset.mem_union,Finset.mem_singleton,Finset.mem_biUnion,
          Finset.mem_image] at hw
        rcases hw with hnil | ⟨a,ha,v,hv,heq⟩
        · cases hnil
        · injection heq with hax hvw
          subst a
          subst v
          have hlen := (ih w).mp hv
          simpa using Nat.succ_le_succ hlen
      · intro hw
        have hlen : w.length ≤ n := by simpa using hw
        apply Finset.mem_union.mpr
        right
        apply Finset.mem_biUnion.mpr
        exact ⟨x,Finset.mem_univ _,Finset.mem_image.mpr ⟨w,(ih w).mpr hlen,rfl⟩⟩
def gball (n : ℕ) : Finset G := (wordsUpTo GLetter n).image (eval gletter)
theorem mem_gball (u : G) (n : ℕ) : u ∈ gball n ↔ gLength u ≤ n := by
  rw [gLength_le_iff]
  simp only [gball,Finset.mem_image,mem_wordsUpTo]
noncomputable def hball (n : ℕ) : Finset G := by
  classical
  exact (gball n).filter (fun u => u ∈ H)
theorem mem_hball (u : G) (n : ℕ) : u ∈ hball n ↔ gLength u ≤ n ∧ u ∈ H := by
  classical
  simp only [hball,Finset.mem_filter,mem_gball]
theorem identity_mem_hball (n : ℕ) : (1:G) ∈ hball n := by
  rw [mem_hball]
  constructor
  · exact (gLength_le_iff 1 n).mpr ⟨[],Nat.zero_le _,rfl⟩
  · exact H.one_mem
noncomputable def distortion (n : ℕ) : ℕ := (hball n).sup hLength
theorem distortion_attained (n : ℕ) :
  ∃ u : G, u ∈ H ∧ gLength u ≤ n ∧ hLength u = distortion n := by
  obtain ⟨u,hu,heq⟩ := Finset.exists_mem_eq_sup (hball n) ⟨1,identity_mem_hball n⟩ hLength
  exact ⟨u,((mem_hball u n).mp hu).2,((mem_hball u n).mp hu).1,heq.symm⟩
theorem le_distortion (u : G) (hu : u ∈ H) (n : ℕ) (hg : gLength u ≤ n) :
  hLength u ≤ distortion n := Finset.le_sup ((mem_hball u n).mpr ⟨hg,hu⟩)
theorem distortion_le (n N : ℕ)
  (h : ∀ u : G, u ∈ H → gLength u ≤ n → hLength u ≤ N) : distortion n ≤ N :=
  Finset.sup_le fun u hu => h u ((mem_hball u n).mp hu).2 ((mem_hball u n).mp hu).1
theorem distortion_mono : Monotone distortion := by
  intro m n hmn
  apply distortion_le
  intro u hu hg
  exact le_distortion u hu n (hg.trans hmn)

end Coordinate4846
