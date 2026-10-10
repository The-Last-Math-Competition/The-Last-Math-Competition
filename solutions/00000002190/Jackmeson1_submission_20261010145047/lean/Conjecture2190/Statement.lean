import Mathlib

/-! Formal statement for Conjecture2190: definitions only, ending in `Claim`. Split verbatim from the marked block of `Basic.lean`. -/

-- STATEMENT BEGIN
namespace C2190
open Filter Topology

/-- Cyclic successor `i + 1` on the vertex set `Fin (2k+1)` of the odd cycle `C_{2k+1}`. -/
def nxt (k : ℕ) (i : Fin (2 * k + 1)) : Fin (2 * k + 1) :=
  ⟨(i.val + 1) % (2 * k + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩

/-- "C_{2k+1}": the (undirected) cycle graph on `Fin (2k+1)`. -/
def Adj (k : ℕ) (i j : Fin (2 * k + 1)) : Prop := j = nxt k i ∨ i = nxt k j

/-- An orientation of the cycle `C_{2k+1}`: arcs only along cycle edges, and each cycle edge
`{i, i+1}` carries exactly one of its two directions. -/
def IsOrientation (k : ℕ) (E : Fin (2 * k + 1) → Fin (2 * k + 1) → Prop) : Prop :=
  (∀ i j, E i j → Adj k i j) ∧ ∀ i, Xor (E i (nxt k i)) (E (nxt k i) i)

/-- Sperner code in `G^n` (G a digraph with arc relation `E`): for every ordered pair of
distinct codewords `x, y` some coordinate has an arc `x i -> y i`. -/
def SpernerCode {α : Type} {n : ℕ} (E : α → α → Prop) (S : Finset (Fin n → α)) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ∃ i, E (x i) (y i)

/-- Zero-error (Shannon) code in the strong power of `C_{2k+1}`: distinct codewords are
distinguishable, i.e. some coordinate has two different non-adjacent letters. -/
def ShannonCode (k : ℕ) {n : ℕ} (S : Finset (Fin n → Fin (2 * k + 1))) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ∃ i, x i ≠ y i ∧ ¬ Adj k (x i) (y i)

/-- Largest size of a code of length `n`. -/
noncomputable def maxCode {α : Type} [Fintype α] {n : ℕ} (P : Finset (Fin n → α) → Prop) : ℕ :=
  by classical exact ((Finset.univ : Finset (Finset (Fin n → α))).filter P).sup Finset.card

/-- "capacity = c" in the unit `u`: `u (M_n ^ (1/n)) -> c`, where `M_n` is the largest code
size.  `u = id` is exponential units, `u = logb 2` bits, `u = log` nats. -/
def Reading (u : ℝ → ℝ) (M : ℕ → ℕ) (c : ℝ) : Prop :=
  Tendsto (fun n : ℕ => u ((M n : ℝ) ^ ((1 : ℝ) / n))) atTop (𝓝 c)

/-- "The Sperner capacity of C_{2k+1} equals cos(pi/(2k+1))" for all `k ≥ 1`, for some
orientation of the cycle, in unit `u`. -/
def ConjSperner (u : ℝ → ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∃ E, IsOrientation k E ∧
    Reading u (fun n => maxCode (SpernerCode (n := n) E)) (Real.cos (Real.pi / (2 * k + 1)))

/-- Same claim for the undirected zero-error (Shannon) capacity of `C_{2k+1}`. -/
def ConjShannon (u : ℝ → ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    Reading u (fun n => maxCode (ShannonCode k (n := n))) (Real.cos (Real.pi / (2 * k + 1)))

/-- What this package proves: the conjecture fails in exponential units, bits and nats,
for the Sperner (any orientation) and the undirected Shannon capacity. -/
def Claim : Prop :=
  (¬ ConjSperner id ∧ ¬ ConjSperner (Real.logb 2) ∧ ¬ ConjSperner Real.log) ∧
  (¬ ConjShannon id ∧ ¬ ConjShannon (Real.logb 2) ∧ ¬ ConjShannon Real.log)

end C2190
-- STATEMENT END
