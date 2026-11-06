# Conjecture 00000000317 — clause ↔ Lean mapping

File: `Disproof.lean` (namespace `Freiman`). Compiled with Lean 4.33.1 / Mathlib v4.33.1 via
`cd /Users/nihao/Projects/tlmc-work/template && lake env lean .../Disproof.lean` — no errors, no warnings.

Axioms of every printed theorem: `[propext, Classical.choice, Quot.sound]`.

## Official statement

> Definition: Freiman's constant c_F is the largest value for which (2√2, c_F) ∩ M = ∅.
> Conjecture: c_F itself belongs to L but not to M (an endpoint asymmetry of the spectra), and
> among the first 20 partial quotients of c_F the digit 1 appears exactly 8 times.

## Mapping

| Statement piece | Lean object | Notes |
|---|---|---|
| Freiman's constant `c_F` | `freimanConstant : ℝ := (2221564096 + 283748 * Real.sqrt 462) / 491993569` | Standard closed form (Freiman 1975) of the right end point of the maximal gap `(2√2, c_F)` of the Markov spectrum, ≈ 4.5278295661. The spectral characterisation is **not** formalised; the closed form is taken as the definition. |
| "partial quotients of `c_F`" | `cfState x n` (Gauss-map orbit: `cfState x 0 = x`, `cfState x (n+1) = 1 / Int.fract (cfState x n)`), `pq x n := ⌊cfState x n⌋ : ℤ` | The standard regular-continued-fraction recursion; `pq x n` is `a_n` in `x = [a_0; a_1, a_2, …]`. Self-contained, not via Mathlib's `GenContFract.of`. |
| "the first 20 partial quotients" | `Finset.range 20` with `pq freimanConstant n` (reading `a_0 … a_19`) | Primary reading. |
| same, alternative indexing | `Finset.range 20` with `pq freimanConstant (n + 1)` (reading `a_1 … a_20`) | Covered by the primed theorems so that either convention is refuted. |
| "the digit 1 appears exactly 8 times" | `((Finset.range 20).filter (fun n => pq freimanConstant n = 1)).card = 8` | Refuted: `count_ones_first20` proves the count is `5`; `count_ones_1_to_20` proves the shifted count is `6`. |
| "c_F ∈ L and c_F ∉ M" | abstract `InLNotM : Prop` (universally quantified parameter of the main theorems) | Left abstract on purpose: the conjunction is refuted through the second clause alone, so no formalisation of the Lagrange/Markov spectra is needed. (Mathematically this clause is also false, since `L ⊆ M`, but this is not used.) |
| Conjecture (conjunction) | `conjecture_00000000317_fails (InLNotM : Prop) : ¬ (InLNotM ∧ ((Finset.range 20).filter (fun n => pq freimanConstant n = 1)).card = 8)` | Main theorem. |
| Conjecture, shifted indexing | `conjecture_00000000317_fails' (InLNotM : Prop) : ¬ (InLNotM ∧ ((Finset.range 20).filter (fun n => pq freimanConstant (n + 1) = 1)).card = 8)` | Variant main theorem. |

## Proof architecture

* `sq_sqrt462 : √462 ^ 2 = 462`; `sqrt462_gt`, `sqrt462_lt`: rational bracketing of `√462` to 12
  decimal places, each proved from a single integer square comparison via `Real.lt_sqrt` /
  `Real.sqrt_lt'` and `norm_num`.
* `floor_of_bounds`: `⌊(p + r√462)/s⌋ = a` from `a·s ≤ p + r√462 < (a+1)·s`, `s > 0`.
* `gauss_step`: if `cfState x n = (p + r√462)/s` and `⌊cfState x n⌋ = a`, then
  `cfState x (n+1) = (P + R√462)/S` whenever `g·P = s(p − a s)`, `g·R = −s r`,
  `g·S = (p − a s)² − 462 r²` with `g, S ≠ 0` (rationalising `1/((p − a s + r√462)/s)`; the
  factor `g` cancels a gcd so the integers stay small). Proved with `field_simp`, `div_eq_div_iff`
  and `linear_combination`.
* `state_0 … state_20`, `pq_0 … pq_20`: 21 exact tails and 21 partial quotients, each a one-line
  application of the two lemmas with `norm_num` / `linarith` side goals. The integer data
  (`p, r, s, a, g, P, R, S` per step) were generated and cross-checked against sympy's
  `continued_fraction_iterator` by `check.py`.
* Counting: `Finset.card_filter` + `Finset.sum_range_succ` + the `pq_k` values + `norm_num`.

Partial quotients established: `[4; 1, 1, 8, 2, 14, 2, 2, 1, 12, 117, 1, 1, 7, 16, 35, 6, 2, 7, 2, 1]`.
Digit 1 among `a_0..a_19`: positions 1, 2, 8, 11, 12 (5 times); among `a_1..a_20`: 6 times.

## Reading choices a reviewer could question

1. **Closed form as definition.** `c_F` is defined by its algebraic closed form, not by the
   spectral property "(2√2, c_F) ∩ M = ∅ maximal". Deriving the closed form from the Markov
   spectrum is a deep theorem (Freiman 1975) and out of scope; the closed form is the universally
   cited value.
2. **First clause abstracted.** The L/M membership clause is an arbitrary proposition. The
   theorem `¬ (InLNotM ∧ count = 8)` holds for every `InLNotM`, so the conjunction is refuted
   regardless of how that clause would be formalised.
3. **Indexing of "first 20 partial quotients".** Both `a_0..a_19` (count 5) and `a_1..a_20`
   (count 6) are covered; in neither case is the count 8. If one counted `a_0..a_20` (21
   quotients) the count would be 6, still not 8.
4. **Own definition of partial quotients** rather than Mathlib's `GenContFract.of`; the recursion
   is the textbook Gauss-map definition and is documented in the docstrings.
