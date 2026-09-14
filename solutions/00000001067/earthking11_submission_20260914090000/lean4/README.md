# Lean 4 formalisation — disproof of conjecture `00000001067`

Core Lean only (`import Std`), no Mathlib, no `sorry`. The project pins
`lean-toolchain` to `leanprover/lean4:v4.33.1` and defines the library `Main`
in `lakefile.toml` (no dependencies).

## Build and audit

```sh
lake build
lake env lean Check.lean
```

`Check.lean` prints `#print axioms` for every theorem so a reviewer can confirm
the absence of `sorryAx` and of the `native_decide` axiom `Lean.ofReduceBool`.

## What is formalised

The field is presented as `Fin 19` and all arithmetic is `Nat` arithmetic;
`Finset`, `Fintype`, `Multiset` and `ZMod` are **not** available under
`import Std`, so the definitions are self-contained.

```lean
abbrev F := Fin 19
def add (x y : F) : F := ⟨(x.val + y.val) % 19, Nat.mod_lt _ (by decide)⟩
def sub (a x : F) : F := ⟨(x.val + 19 - a.val) % 19, Nat.mod_lt _ (by decide)⟩

/-- The 15 unordered sums a+b (a <= b, repetition allowed) of a 5-tuple. -/
def sums (a b c d e : F) : List F := ...

/-- Strong Sidon: the 15 sums are pairwise distinct. -/
def sidon5 (a b c d e : F) : Bool := (sums a b c d e).Nodup
def sidon4 (a b c d : F) : Bool := (sums4 a b c d).Nodup
```

| Theorem | Statement | Role |
|:--------|:----------|:-----|
| `add_inj`, `add_inj_raw` | `x ↦ x + c` is injective on `F_19` | translation machinery |
| `step` | `add (sub a x) (sub a y) = add (add x y) (neg2 a)` | sums shift by `-2a` |
| `sub_self` | `sub a a = 0` | normalises the smallest element |
| `sub_pos`, `sub_lt` | `sub a` is positive and order-preserving on positives | orders the translated tuple |
| `sidon_translate` | strong Sidon is invariant under `x ↦ x − a` | the WLOG reduction |
| `no_sidon5_zero` | `∀ b c d e, 0 < b < c < d < e → sidon5 0 b c d e = false` | decidable core |
| `no_sidon5` | **no strictly increasing 5-tuple in `F_19` is strong Sidon** | main combinatorial theorem |
| `sidon4_witness` | `sidon4 0 1 3 7 = true` | the explicit witness $\{0,1,3,7\}$ |
| `count_obstruction` | `5 * 4 > 19 - 1` | difference-count obstruction to size 5 |
| `ceil_sqrt19` | `4^2 < 19 ∧ 19 ≤ 5^2` | `ceil(sqrt 19) = 5` |
| `conjecture_00000001067_false` | `(∃ sidon4) ∧ no_sidon5 ∧ ceil_sqrt19` | **the packaged refutation** |

Every 5-element subset of `F_19` can be listed in strictly increasing order, so
`no_sidon5` says exactly that the maximum size of a strong Sidon set in `F_19`
is at most 4; together with `sidon4_witness` the maximum is exactly 4. Since
`ceil(sqrt 19) = 5`, the filed exact clause "the `O(1)` term equals 0 for
`p ≡ 3 mod 4`" is false.

## Proof strategy

- **Translation invariance** (`sidon_translate`). Replacing each element `x` by
  `sub a x = x − a` shifts every sum by the constant `neg2 a = −2a`; the map
  `z ↦ add z (neg2 a)` is injective (`add_inj`), so distinctness of the sum
  multiset is preserved. This is the fully valid WLOG reduction sending the
  smallest element to `0`.
- **Decidable core** (`no_sidon5_zero`). With `a = 0` fixed, the statement
  ranges over `19 · 18 · 17 · 16` ordered tuples but collapses to a boolean
  `decide`; Lean checks it exhaustively.
- **Main theorem** (`no_sidon5`). Case-split on `sidon5 a b c d e`; in the
  `true` branch, translate by `−a`, use `sub_self` to get the `0`-anchored
  situation, and contradict `no_sidon5_zero`. The strict ordering is preserved
  by `sub_pos`/`sub_lt`.
- **Witness and counting** (`sidon4_witness`, `count_obstruction`,
  `ceil_sqrt19`) are closed `decide` evaluations.

## Axiom audit

`lake env lean Check.lean` prints (observed):

```
'Tlmc1067.add_inj' does not depend on any axioms
'Tlmc1067.add_inj_raw' does not depend on any axioms
'Tlmc1067.step' does not depend on any axioms
'Tlmc1067.sub_self' depends on axioms: [propext]
'Tlmc1067.sub_pos' depends on axioms: [propext]
'Tlmc1067.sub_lt' does not depend on any axioms
'Tlmc1067.sidon_translate' depends on axioms: [propext, Quot.sound]
'Tlmc1067.no_sidon5_zero' depends on axioms: [propext]
'Tlmc1067.no_sidon5' depends on axioms: [propext, Quot.sound]
'Tlmc1067.sidon4_witness' depends on axioms: [propext]
'Tlmc1067.count_obstruction' does not depend on any axioms
'Tlmc1067.ceil_sqrt19' does not depend on any axioms
'Tlmc1067.conjecture_00000001067_false' depends on axioms: [propext, Quot.sound]
```

No `sorryAx` appears for any theorem, and no `Lean.ofReduceBool` (the
`native_decide` axiom) either. The only axioms are the standard core axioms
`propext` and `Quot.sound`. `Quot.sound` enters through `List.Pairwise.map`
used in `sidon_translate`; `propext` through the `decide` machinery.

## Honest footprint and performance notes

- **No `native_decide`.** A `native_decide` variant of the whole development
  compiles in ~0.65 s but adds the axiom `Lean.ofReduceBool`. The submission
  convention here is to avoid that axiom, so the shipped version uses the
  axiom-free `decide` route. The cost is proving time: `lake build` takes about
  51 s (measured; `Main` alone is reported as ~51 s by Lake, 58 s of user time).
- **Why the WLOG reduction is needed.** A direct 5-variable `decide` over
  `Fin 19` exceeds 400 s. Fixing one element to `0` via translation invariance
  brings the decidable core to roughly 15 s, and the general theorem is a short
  symbolic reduction on top of it. `List.Pairwise.map` is the one place that
  pulls in `Quot.sound`; replacing it by a hand-rolled induction would give a
  strictly `propext`-only audit, at the cost of a longer proof. We document the
  footprint honestly rather than hide it.
- **Scope.** The statement is a finite, exact refutation: no `∀ p` quantifier
  is formalised, because the conjecture is refuted by a single prime
  (`p = 19`). The finite facts `no_sidon5` (universally quantified over all
  `a < b < c < d < e` in `F_19`) and `sidon4_witness` are symbolic/uniform, not
  a hand-checked list. The general inequality `k(k-1) ≤ p-1` is stated and
  proved in prose in `main.tex` and verified computationally in `reproduce.py`.

## Environment

Lean 4.33.1, Lake. No Mathlib, no cache download required.
