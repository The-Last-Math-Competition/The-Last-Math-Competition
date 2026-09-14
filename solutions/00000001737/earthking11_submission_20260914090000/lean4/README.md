# Lean 4 formalisation — disproof of conjecture `00000001737`

Core Lean only (`import Std`), no Mathlib, no `sorry`. The project pins
`lean-toolchain` to `leanprover/lean4:v4.33.1` and defines the library `Main` in
`lakefile.toml`.

## Build and audit

```sh
lake build
lake env lean Check.lean
```

`Check.lean` prints `#print axioms` for every theorem so a reviewer can confirm
the absence of `sorryAx` and of Mathlib dependencies.

## What is formalised

The conjecture claims the maximal number of `S`-integral points of
`P¹ ∖ {0,1,∞}` over two-element prime sets `S` is `12`. An `S`-integral point
is a rational `x` with `x` and `1 - x` both `S`-units (integrality at the whole
divisor `{0,1,∞}`). The formalisation exhibits **21 pairwise-distinct
`S`-integral points for `S = {2,3}`**, hence the maximum is at least `21 > 12`.

This is a **lower-bound witness**: it proves `max ≥ 21`, which already refutes
an upper bound of `12`. It does *not* compute the exact maximum over all `S`
(that needs the `S`-unit theorem / linear forms in logarithms).

### Encodings

- `Nat.Prime` and `Finset` are **not** available in `import Std`, and `Rat` is
  avoided because `decide` cannot reduce it (its normalisation is opaque).
- A rational is encoded as a pair `(p : Int, q : Nat)` with `q > 0`, meaning
  `p/q` in lowest terms; equality is tested by cross-multiplication
  `p₁ * q₂ = p₂ * q₁`, a closed `Int` identity `decide` can reduce.
- The integrality predicates are `Bool`-valued, and theorems are stated as
  `... = true`, because Decidable synthesis does not unfold a `def`-wrapped
  `Prop`; `List.all_eq_true` / `List.any_eq_true` convert the Boolean
  quantifiers to the `Membership` form used by the theorems.

```lean
/-- `n = 2^a * 3^b` for some `a, b ≤ n`. -/
def IsSmooth (n : Nat) : Bool :=
  (List.range (n + 1)).any fun a =>
    (List.range (n + 1)).any fun b => n == 2 ^ a * 3 ^ b

/-- `p/q` is a unit of `Z[1/2,1/3]`: `q > 0`, `p ≠ 0`, `|p|` and `q` smooth. -/
def SUnitRatB (p : Int) (q : Nat) : Bool :=
  decide (0 < q) && decide (p ≠ 0) && IsSmooth p.natAbs && IsSmooth q

/-- `p/q` is S-integral on `P¹ ∖ {0,1,∞}`: an S-unit, `≠ 1`, and `1 - p/q`
an S-unit. -/
def SIntegralB (p : Int) (q : Nat) : Bool :=
  SUnitRatB p q && decide (p ≠ (q : Int)) && IsSmooth ((q : Int) - p).natAbs
```

| Theorem | Statement | Role |
|:--------|:----------|:-----|
| `isSmooth_sound` | `IsSmooth n = true → ∃ a b, n = 2^a * 3^b` | faithfulness of the smoothness test |
| `isSmooth_one … isSmooth_nine`, `isSmooth_five`, `isSmooth_seven` | `IsSmooth` on concrete values | the test computes correctly |
| `not_isSmooth_five`, `not_isSmooth_seven` | `¬ IsSmooth 5 = true`, `¬ IsSmooth 7 = true` | the test really excludes non-`{2,3}`-smooth numbers |
| `sIntegral_sound` | passing `SIntegral` yields `q > 0`, `p ≠ 0`, `\|p\| = 2^a 3^b`, `q = 2^c 3^d`, `p ≠ q`, `\|q - p\| = 2^e 3^f` | **faithfulness**: the executable test is exactly the mathematical definition |
| `integralAll_eq`, `distinctAll_eq` | the two `Bool` checks over the 21-element list are `true` | computed by `decide` |
| `all_integral` | `∀ x ∈ pts, SIntegral x.1 x.2` | every listed point is S-integral |
| `all_distinct` | pairwise distinct via cross-multiplication | the 21 entries are 21 different rationals |
| `pts_length` | `pts.length = 21` | count |
| `twelve_lt_length` | `12 < pts.length` | the conjectured maximum is exceeded |
| `conjecture_00000001737_false` | `pts.length = 21 ∧ (all integral) ∧ (all distinct) ∧ 12 < pts.length` | **main theorem** |
| `more_than_twelve_points` | `∃ n > 12, ∃ pts, …` | packaged lower-bound witness |
| `not_max_le_twelve` | it is not the case that every such set has `≤ 12` elements | the conjecture's count bound is negated |

## Proof strategy

- **Soundness of `IsSmooth`.** Bounded `List.any` search; `List.any_eq_true`
  extracts the witnesses `a, b`, and `simpa` turns the `==` into `=`.
- **Soundness of `SIntegral`.** Unfold `SIntegralB` and `SUnitRatB` with
  `Bool.and_eq_true` to obtain each conjunct, then apply `isSmooth_sound` to the
  three `IsSmooth` hits.
- **`integralAll` / `distinctAll`.** Both are closed `Bool` computations over
  the explicit 21-element list; `decide` evaluates them (all comparisons are on
  `Nat`/`Int` via `==` and cross-multiplication, never on `Rat`).
- **`all_integral` / `all_distinct`.** `List.all_eq_true` turns the Boolean
  `all` into a `∀ ∈` statement; `distinctB` uses the `if x = y` branch so that
  `decide` sees a definitional `true` for the diagonal and a cross-multiplication
  inequality off the diagonal.
- **Main theorem.** Conjunction of the four facts, each discharged by `decide`
  or a previous lemma.
- **`not_max_le_twelve`.** Apply the putative bound to `pts` and `omega` the
  contradiction with `pts.length = 21`.

## Axiom audit

`lake env lean Check.lean` reports:

- concrete computations (`isSmooth_*`, `not_isSmooth_*`, `integralAll_eq`,
  `distinctAll_eq`, `pts_length`, `twelve_lt_length`): **no axioms**;
- `isSmooth_sound`, `sIntegral_sound`, `all_integral`, `all_distinct`,
  `conjecture_00000001737_false`, `more_than_twelve_points`,
  `not_max_le_twelve`: `propext`, `Quot.sound`.

No `sorryAx` appears for any theorem; no Mathlib is imported.

## Scope note

- The witness is concrete and fully checked: `pts` is an explicit list, and
  `decide` verifies both integrality and distinctness entry by entry. What is
  proved is `max ≥ 21 > 12`, i.e. the conjecture's numerical claim is false.
- The *upper* direction — that `21` is the maximum over all two-element prime
  sets, and the exact value for other `S` — is **not** formalised. It is
  substantiated numerically in `reproduce.py` (saturated enumeration for
  `p < q ≤ 23`, maximum `21` at `{2,3}`) and is the content of the `S`-unit
  theorem. The refutation does not need it.
- The `S`-unit equation's finiteness theorem (Mahler) and Evertse's bound are
  not formalised; they are cited in prose in `main.tex`. The Lean content is the
  explicit witness together with the faithfulness lemmas that connect it to the
  mathematical definition.

## Environment

Lean 4.33.1, Lake, no Mathlib. `lake build` needs no cache download and no
network access.
