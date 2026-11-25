namespace Conjecture00000001291

/-- Strict chain `x₀ ≺ x₁ ≺ ⋯ ≺ xₘ` whose elements all satisfy domain predicate `P`. -/
inductive IsStrictChainIn {α : Type} (P : α → Prop) (lt : α → α → Prop) : List α → Prop where
  | singleton {x : α} : P x → IsStrictChainIn P lt [x]
  | cons {x y : α} {ys : List α} :
      P x → lt x y → IsStrictChainIn P lt (y :: ys) → IsStrictChainIn P lt (x :: y :: ys)

/-- Existence of a strict chain of height `k` (`k` strict steps, `k + 1` elements) inside `P`. -/
def HasChainOfHeight {α : Type} (P : α → Prop) (lt : α → α → Prop) (k : Nat) : Prop :=
  ∃ xs : List α, xs.length = k + 1 ∧ IsStrictChainIn P lt xs

/-- Existence of a strict chain of vertex cardinality `m` (`m` elements) inside `P`. -/
def HasChainOfCard {α : Type} (P : α → Prop) (lt : α → α → Prop) (m : Nat) : Prop :=
  ∃ xs : List α, xs.length = m ∧ IsStrictChainIn P lt xs

/-- Poset height of `(P, lt)` is at most `n`: every strict chain in `P` has at most `n` steps. -/
def PosetHeightAtMost {α : Type} (P : α → Prop) (lt : α → α → Prop) (n : Nat) : Prop :=
  ∀ k : Nat, HasChainOfHeight P lt k → k ≤ n

/-- Poset vertex-height (chain cardinality) of `(P, lt)` is at most `n`. -/
def PosetCardHeightAtMost {α : Type} (P : α → Prop) (lt : α → α → Prop) (n : Nat) : Prop :=
  ∀ m : Nat, HasChainOfCard P lt m → m ≤ n

theorem not_posetHeightAtMost_of_chain {α : Type} {P : α → Prop} {lt : α → α → Prop}
    {k n : Nat} (hchain : HasChainOfHeight P lt k) (hgt : n < k) :
    ¬ PosetHeightAtMost P lt n := by
  intro hle
  have := hle k hchain
  omega

theorem not_posetCardHeightAtMost_of_chain {α : Type} {P : α → Prop} {lt : α → α → Prop}
    {k n : Nat} (hchain : HasChainOfHeight P lt k) (hgt : n < k + 1) :
    ¬ PosetCardHeightAtMost P lt n := by
  intro hle
  rcases hchain with ⟨xs, hlen, hsc⟩
  have := hle (k + 1) ⟨xs, hlen, hsc⟩
  omega

/-- Any strict chain in a subset of `{0, 1, ..., n}` under `<` has height at most `n`. -/
theorem strictChain_nat_bound {n : Nat} {P : Nat → Prop} (hP : ∀ x, P x → x ≤ n) :
    ∀ {xs : List Nat}, IsStrictChainIn P (· < ·) xs →
      ∀ x, xs.head? = some x → x + (xs.length - 1) ≤ n
  | [x], .singleton hx, y, hhead => by
    injection hhead with heq
    subst heq
    simp
    exact hP x hx
  | x :: y :: ys, .cons _ hxy htail, z, hhead => by
    injection hhead with heq
    subst heq
    have ih := strictChain_nat_bound hP htail y rfl
    simp at ih ⊢
    omega

theorem nat_posetHeightAtMost {P : Nat → Prop} {n : Nat} (hP : ∀ x, P x → x ≤ n) :
    PosetHeightAtMost P (· < ·) n := by
  intro k ⟨xs, hlen, hsc⟩
  cases xs with
  | nil => simp at hlen
  | cons x rest =>
    have hb := strictChain_nat_bound hP hsc x rfl
    omega

end Conjecture00000001291
