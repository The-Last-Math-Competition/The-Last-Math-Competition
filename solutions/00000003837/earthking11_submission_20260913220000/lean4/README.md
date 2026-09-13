# Lean 4 formalisation — disproof of conjecture `00000003837`

Core Lean only (`import Std`), no Mathlib, no `sorry`. The project pins
`lean-toolchain` to `leanprover/lean4:v4.33.1` and defines the library `Main`
inside the package `tlmc3837` in `lakefile.toml`.

## Build and audit

```sh
lake build
lake env lean Check.lean
```

`Check.lean` prints `#print axioms` for every theorem so a reviewer can confirm
the absence of `sorryAx` and of Mathlib dependencies.

## What is formalised

The refutation lives at `λ = ω₁` in type `A₁`. The crystal `B(ω₁)` is
represented as `B1 := Fin 2`, with:

- `f1`, `e1 : B1 → Option B1`, the lowering and raising operators
  (`f1 0 = some 1`, `f1 1 = none`, and dually for `e1`);
- `wt : B1 → Int`, the weight `1 - 2·j`, so the two elements have weights
  `+1` and `-1`;
- `star : B1 → B1`, the swap `j ↦ 1 - j`, the unique arrow-reversing involution;
- `fixedCount σ`, the number of elements `x` with `σ x = x`, computed over the
  list `List.finRange 2` (note: `Finset` is **not** in `import Std`, but
  `List.finRange` is).

| Theorem | Statement | Role |
|:--------|:----------|:-----|
| `B1_card` | `(List.finRange 2).length = 2` | `B(ω₁)` has two elements |
| `f1_top` | `f1 0 = some 1 ∧ f1 1 = none` | one lowering arrow |
| `e1_bottom` | `e1 1 = some 0 ∧ e1 0 = none` | one raising arrow |
| `star_involutive` | `∀ j, star (star j) = j` | `*` is an involution |
| `star_reverses_f` | `∀ j, f1 (star j) = (e1 j).map star` | `*` reverses the lowering arrow |
| `star_reverses_e` | `∀ j, e1 (star j) = (f1 j).map star` | `*` reverses the raising arrow |
| `wt_star` | `∀ j, wt (star j) = - wt j` | `*` negates weights |
| `star_apply` | `star 0 = 1 ∧ star 1 = 0` | `*` is the swap |
| `star_fixedCount` | `fixedCount star = 0` | **no** fixed point |
| `star_even` | `fixedCount star % 2 = 0` | **even**, contradicting "always odd" |
| `star_lt_three` | `fixedCount star < 3` | contradicting "at least 3" |
| `conjecture_00000003837_false` | `fixedCount star = 0 ∧ fixedCount star % 2 = 0 ∧ fixedCount star < 3` | packaged disproof |
| `star_conjecture_false` | `fixedCount star % 2 = 0 ∧ fixedCount star < 3` | the two failing clauses |
| `fixedCount_eq` | closed form `(if σ 0 = 0 then 1 else 0) + (if σ 1 = 1 then 1 else 0)` | counting lemma |
| `involution_fixedCount_even` | every involution of `B1` has even fixed count | **no involution can rescue the parity claim** |
| `involution_fixedCount_lt_three` | every involution of `B1` has `< 3` fixed points | second clause fails for every convention |
| `arrow_reversing_involution_eq_star` | any arrow-reversing involution equals `star` | the star is forced |
| `no_weight_preserving_arrow_reversal` | no involutive arrow reversal preserves weights | the weight convention cannot be tweaked |

## Proof strategy

- **The crystal is one arrow.** `f1_top` and `e1_bottom` are finite checks
  closed by `decide`.
- **The star is an involution reversing the arrow and negating weights.**
  `star_involutive`, `star_reverses_f`, `star_reverses_e`, `wt_star`, and
  `star_apply` are all closed by `decide` on the two-element type.
- **No fixed points.** `star_apply` shows `star` swaps `0` and `1`, so neither
  is fixed; `star_fixedCount` evaluates the filtered `List.finRange 2` and
  yields `0`. Hence `star_even` (`0 % 2 = 0`) and `star_lt_three` (`0 < 3`).
- **Robustness.** `fixedCount_eq` gives a closed form for any `σ : B1 → B1`.
  Case-splitting on the values `σ 0`, `σ 1 ∈ {0,1}` (`B1_eq_zero_or_one`) and
  using the involution law rules out the two possibilities that would give an
  odd count, proving `involution_fixedCount_even`; the remaining cases give
  `involution_fixedCount_lt_three`. `arrow_reversing_involution_eq_star` uses
  the arrow-reversal law at `0` to force `σ 0 = 1` and then the involution law
  to force `σ 1 = 0`, i.e. `σ = star`.
- **`λ = ω₁` satisfies `λ = -w₀λ`.** In type `A₁` the longest element
  `w₀ = s₁` acts on the weight lattice by `-1`, so `-w₀` acts as the identity
  and the condition `λ = -w₀λ` holds for every `λ`. The formalisation stays at
  the level of `B(ω₁)` and does not model the weight lattice action of `w₀`;
  this step is the trivial identity `-(-λ) = λ` recorded in the write-up.

## Faithfulness note

Core Lean cannot host general Kac–Moody crystal theory, so instead of a general
`B(λ)` a bespoke two-element `A₁` mini-crystal `B(ω₁)` is defined and axiomatised
by the data above. The adequacy of this mini-crystal for refuting the conjecture
rests on `arrow_reversing_involution_eq_star`: the arrow-reversing requirement
pins the star involution down *uniquely* to the swap, so every faithful
convention/definition of `*` on `B(ω₁)` agrees with the `star` formalised here.
The conclusion `fixedCount star = 0` is therefore convention-independent. In
addition `involution_fixedCount_even` and `involution_fixedCount_lt_three` show
that *any* involution of the two-element set (arrow-reversing or not) has an
even fixed count `< 3`, so the two failing clauses cannot be repaired by
redefining `*`.

The axiom audit reports only `propext` and `Quot.sound`; there is no `sorryAx`
and no `Lean.ofReduceBool`. `B1_card` depends on no axioms at all.

## Scope note

- Fully formalised: `B(ω₁)` is a single arrow, `star` is its unique
  arrow-reversing involution and negates weights, `star` has `0` fixed points
  (`fixedCount star = 0`), that count is even and `< 3`, and no involution
  whatsoever of `B(ω₁)` has an odd or `≥ 3` fixed count.
- Left informal: the general theory of `B(λ)` and the star involution for
  arbitrary dominant `λ`, and the action of `w₀` on the weight lattice. These
  are not needed: the conjecture is refuted by the single explicit `λ = ω₁`,
  and the uniqueness lemma makes the refutation independent of convention.
- The integer relation `0 < 3` and the parity lemma are reproduced
  independently by the dependency-free `../reproduce.py`.
