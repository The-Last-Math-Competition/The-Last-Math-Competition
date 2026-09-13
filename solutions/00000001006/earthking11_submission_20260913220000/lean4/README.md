# Lean 4 formalisation — disproof of conjecture `00000001006`

Core Lean only (`import Std`), no Mathlib, no `sorry`. The project pins
`lean-toolchain` to `leanprover/lean4:v4.33.1` and defines the library `Main`
(project name `tlmc1006`) in `lakefile.toml`.

## Build and audit

```sh
lake build
lake env lean Check.lean
```

`Check.lean` prints `#print axioms` for every theorem so a reviewer can confirm
the absence of `sorryAx` and of Mathlib dependencies.

## What is formalised

Points of `PG(4,2)` are modelled as `Point := Fin 5 → Bool`, encoded by the
natural number `enc x = Σ x_i 2^i` so that all finite computations are
decidable without any `DecidableEq` instance on function types (which core Lean
does not provide). The quadric, its points, its lines and `m`-ovoids are

```lean
def Q (x : Point) : Bool := x 0 != ((x 1 && x 2) != (x 3 && x 4))
def B (a b : Point) : Bool :=
  ((a 1 && b 2) != (a 2 && b 1)) != ((a 3 && b 4) != (a 4 && b 3))
def IsPoint (x : Point) : Bool := Nonzero x && !Q x
def IsLinePairE (a b : Nat) : Bool :=
  IsPointE a && IsPointE b && a != b && !B (mk a) (mk b)
def IsLineE (a b c : Nat) : Bool :=
  IsLinePairE a b && c == enc (addP (mk a) (mk b))   -- {a, b, a+b}
def IsMOvoid (m : Nat) (S : List Point) : Bool :=
  linesP.all fun L => hitP S L == m
```

| Theorem | Statement | Role |
|:--------|:----------|:-----|
| `pointsE_length` | `pointsE.length = 15` | `Q(4,2)` has 15 points |
| `pointsE_eq` | `pointsE = [2,4,…,30]` | the point list is explicit |
| `lines15_is_all_lines` | `allLinesE = lines15` | the 15 listed lines are exactly all lines (computed from the definitions) |
| `allLinesE_length` | `allLinesE.length = 15` | `Q(4,2)` has 15 lines |
| `lines15_size` | `lines15.all (·.length == 3) = true` | each line has `q+1 = 3` points |
| `linesP_shape` | `linesP.length = 15` and 3 points per line | the line list used below |
| `enc_mk_range` | `∀ n < 32, enc (mk n) = n` | encoding round-trip on all vectors |
| `mk_enc_points` | `∀ n ∈ pointsE, enc (mk n) = n` | encoding round-trip on the points |
| `O_card` | `O.length = 5` and all entries are points | `O` is an explicit 5-point set |
| `O_map_enc` | `O.map enc = [2,4,15,23,30]` | the coordinates of `O` |
| `O_is_ovoid` | `IsMOvoid 1 O = true` | every line meets `O` in exactly 1 point |
| `Ocomp_card` | `Ocomp.length = 10` and all entries are points | the complement has `q^2+q = 10` points |
| `Ocomp_map_enc` | `Ocomp.map enc = compE` | the coordinates of `O^c` |
| `Ocomp_is_2ovoid` | `IsMOvoid 2 Ocomp = true` | every line meets `O^c` in exactly 2 points |
| `O_and_Ocomp_partition` | `(O ++ Ocomp).length = 15` and `O^c` is disjoint from `O` | `O`, `O^c` partition the point set |
| `two_not_dvd_three` | `¬ (2 ∣ 3)` | `2 ∤ q+1` for `q = 2` |
| `two_ovoid_exists` | `∃ S, IsMOvoid 2 S = true` | a 2-ovoid exists |
| `conjecture_00000001006_false` | `(∃ S, IsMOvoid 2 S = true) ∧ ¬ (2 ∣ 3)` | packaged disproof |

The explicit ovoid is

```lean
def O : List Point := [mk 2, mk 4, mk 15, mk 23, mk 30]
-- vectors: (0,1,0,0,0), (0,0,1,0,0), (1,1,1,1,0), (1,1,1,0,1), (0,1,1,1,1)
```

and its complement is `Ocomp = compE.map mk` with
`compE = pointsE.filter (fun n => !OE.contains n)`.

## Proof strategy

- **Everything is a finite computation.** `allLinesE` is obtained by filtering
  the sorted triples of the 15 point encodings with `IsLineE`, i.e. directly
  from the definition of a generating line (`a`, `b` distinct points,
  `B(a,b) = 0`, `c = a+b`). The theorem `lines15_is_all_lines` proves by
  `decide` that this computed set equals the explicitly listed `lines15`, so the
  list is complete and contains no non-lines.
- **The line-hit predicate.** `hitP S L` counts the points of `L` that lie in
  `S`; membership uses `enc` (`memP S x = S.any (· enc == enc x)`), avoiding any
  need for `DecidableEq (Fin 5 → Bool)`. `IsMOvoid m S` is
  `linesP.all (· hitP S · == m)`, i.e. the definition of an `m`-ovoid.
- **The ovoid and its complement.** `O_is_ovoid` and `Ocomp_is_2ovoid` are
  closed by `decide` after unfolding the 15-line list, and
  `O_and_Ocomp_partition` records that the two lists partition the 15 points.
- **The arithmetic.** `two_not_dvd_three : ¬ (2 ∣ 3)` is closed by `decide`;
  the packaged `conjecture_00000001006_false` combines it with the existence of
  a 2-ovoid.
- **Encoding fidelity.** `enc_mk_range` and `mk_enc_points` verify by `decide`
  that `enc` is a bijection on the relevant finite sets, so the Nat-level
  computations faithfully represent the vector-level geometry.

## Scope note

- The formalisation is complete for the claimed counterexample: it verifies the
  full building (`15` points, the `15` lines), that the explicit `O` is a
  `1`-ovoid, that its complement `Ocomp` is a `2`-ovoid, that a `2`-ovoid
  exists, and that `2 ∤ 3`.
- Only the smallest case `q = 2` is formalised. The general observation that the
  complement of an ovoid in `Q(4,q)` is a `q`-ovoid (and `q ∤ q+1`) is stated
  informally in `README.md` and `main.tex`; it is not needed for the refutation
  and is not claimed as formalised here.
- `m`-ovoids are defined with respect to the lines of the computed line set,
  which `lines15_is_all_lines` certifies to be the complete line set of `Q(4,2)`
  in the stated vector model.

## Environment

Lean 4.33.1, Lake, no Mathlib, no cache download required. The axiom audit
reports no `sorryAx`; the finite facts depend at most on `propext` (from the
`decide` proofs of decidable equalities), and no axiom beyond that.
