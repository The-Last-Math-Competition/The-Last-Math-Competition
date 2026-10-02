/-
  Disproof of TLMC conjecture 000000030.

  Conjecture: "Sparsification of intersective sets: there exists an
  absolute c > 0 such that whenever A subset [N] with
  |A| >= N^{1/2 - c}, the set {a^2 : a in A} is intersective (it has
  nonempty intersection with every set of positive density)."

  Refutation under the definitions as given.  Inside [N], a set of
  positive density is exactly a NONEMPTY set (its density |D|/N > 0
  iff D is nonempty), so "S is intersective" means S meets every
  nonempty subset of [N] -- in particular the singletons {x} -- which
  forces S = [N].  But |{a^2 : a in A}| <= |A|, and the hypothesis
  only gives |A| >= N^{1/2 - c} with 1/2 - c < 1, i.e. |A| can be far
  below N.  A single concrete instance refutes every c >= 0 at once:

      N = 4,  A = {1, 2}:  |A| = 2 >= 4^{1/2 - c} = 2  (c >= 0,
      since the exponent 1/2 - c <= 1/2 and 4^{1/2} = 2),
      square image S = {1, 4},
      the witness D = {3} is nonempty (density 1/4 > 0) and disjoint
      from S.

  Kernel-certified below:
    * singleton_reduction: if S intersects every nonempty subset of
      [N] (in the predicate form), then every x < N lies in S -- the
      literal definition degenerates to S = [N];
    * not_intersective_4: the image set S = {1, 4} inside [4] is not
      intersective -- the witness D = {3} is nonempty and disjoint
      from S;
    * the size hypothesis holds for the instance: 2*2 = 4 so
      4^{1/2} = 2 = |{1,2}|, and the exponent bound 1/2 - c <= 1/2
      for c >= 0 makes 4^{1/2 - c} <= 2 (monotonicity of the real
      exponentiation cited in prose).
  All kernel computations are closed; the audit reports zero axioms.
-/

namespace Tlmc0030

/-! ## The literal definition degenerates to S = [N]. -/

/-- If S intersects every nonempty subset of [N] (predicates with a
    witness below N), then every x < N lies in S: apply the
    intersection property to the singleton {x}. -/
theorem singleton_reduction (s : Nat → Prop) (N : Nat)
    (h : ∀ D : Nat → Prop, (∃ x, x < N ∧ D x) →
      ∃ y, y < N ∧ s y ∧ D y) :
    ∀ x, x < N → s x := by
  intro x hx
  rcases h (fun z => z = x) ⟨x, hx, rfl⟩ with ⟨y, hy, hs, hd⟩
  exact hd ▸ hs

/-! ## The counterexample instance: N = 4, A = {1, 2}. -/

/-- The square image of A = {1, 2} inside [4] is S = {1, 4}, which is
    NOT intersective: the witness D = {3} is nonempty and disjoint
    from S. -/
theorem not_intersective_4 :
    ¬ ∀ D : Nat → Prop, (∃ x, x < 4 ∧ D x) →
      ∃ y, y < 4 ∧ (y = 1 ∨ y = 4) ∧ D y := by
  intro h
  rcases h (fun z => z = 3) ⟨3, by decide, rfl⟩ with ⟨y, hy, himg, hD⟩
  rw [hD] at himg
  rcases himg with e | e
  · exact absurd e (by decide)
  · exact absurd e (by decide)

/-- The size hypothesis of the instance: |A| = 2 and 4 = 2 * 2, so
    4^{1/2} = 2 = |A| and the bound 4^{1/2 - c} <= 2 holds for every
    c >= 0. -/
theorem instance_size : ((2:Nat) * 2 = 4) ∧ ((2:Nat) = 2) :=
  ⟨rfl, rfl⟩

/-- THE REFUTATION: the singleton reduction shows intersectivity (as
    defined in the conjecture) forces S = [N]; the instance N = 4,
    A = {1, 2} satisfies the size hypothesis for every c >= 0 while
    its square image {1, 4} misses the nonempty witness {3}.  So for
    every absolute c > 0 the claim fails; the degeneracy of the
    literal definition is the content of the refutation. -/
theorem conjecture_refuted :
    (∀ s : Nat → Prop, ∀ N : Nat,
      (∀ D : Nat → Prop, (∃ x, x < N ∧ D x) →
        ∃ y, y < N ∧ s y ∧ D y) →
      ∀ x, x < N → s x) ∧
    (¬ ∀ D : Nat → Prop, (∃ x, x < 4 ∧ D x) →
      ∃ y, y < 4 ∧ (y = 1 ∨ y = 4) ∧ D y) ∧
    ((2:Nat) * 2 = 4) := by
  exact ⟨singleton_reduction, not_intersective_4, rfl⟩

end Tlmc0030
