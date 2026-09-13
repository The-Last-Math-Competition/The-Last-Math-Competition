# Lean 4 formalisation — disproof of conjecture `00000001682`

Core Lean only (`import Std`), no Mathlib, no `sorry`. The project pins
`lean-toolchain` to `leanprover/lean4:v4.33.1` and defines the library `Main` in
`lakefile.toml` (project name `tlmc1682`).

## Build and audit

```sh
lake build
lake env lean Check.lean
```

`Check.lean` prints `#print axioms` for every theorem so a reviewer can confirm
the absence of `sorryAx` and of Mathlib dependencies.

## What is formalised

**Model.** Vertices of `GP(11, 2)` are `Fin 2 × Fin 11`: the first coordinate is
the layer (`0` = outer vertex `u`, `1` = inner vertex `v`) and the second is the
index modulo `11`:

```lean
abbrev V (n : Nat) : Type := Fin 2 × Fin n
def gp (n k : Nat) : V n → V n → Bool   -- outer u_i—u_{i+1}, spoke u_i—v_i, inner v_i—v_{i+k}
def gp11 : V 11 → V 11 → Bool := gp 11 2
```

The adjacency relation is a decidable `Bool` predicate with all indices reduced
modulo `n`. A triangle is three pairwise adjacent vertices:

```lean
def isTriangle {n : Nat} (G : V n → V n → Bool) (x y z : V n) : Bool :=
  G x y && G y z && G z x
def Triangle {n : Nat} (G : V n → V n → Bool) (x y z : V n) : Prop :=
  isTriangle G x y z = true
```

Exhaustive triangle freeness is the `Bool` check

```lean
def triangleFreeCheck (n k : Nat) : Bool :=
  (List.finRange 2).all fun a => (List.finRange 2).all fun b =>
  (List.finRange 2).all fun c => (List.finRange n).all fun i =>
  (List.finRange n).all fun j => (List.finRange n).all fun z =>
    !(isTriangle (gp n k) (a, i) (b, j) (c, z))
```

and the number of (unordered) triangles is computed by exhaustive enumeration:

```lean
def triangleCount (n k : Nat) : Nat   -- over all C(2n, 3) vertex triples
```

**Cycles and pancyclicity.** A cycle is an injective closed walk encoded as a
list of pairwise distinct vertices whose cyclically consecutive pairs are
adjacent:

```lean
def ClosedFrom ...   -- consecutive adjacency + last-to-first closure
def ClosedCycle ...  -- a closed walk of length at least three
def IsCycle (G) (p) : Prop := p.Pairwise (· ≠ ·) ∧ 3 ≤ p.length ∧ ClosedCycle G p
def HasCycleOfLength (G) (L : Nat) : Prop :=
  ∃ p : List (V n), p.length = L ∧ IsCycle G p
def Pancyclic (G) : Prop :=
  ∀ L : Nat, 3 ≤ L → L ≤ 2 * n → HasCycleOfLength G L
```

| Theorem | Statement | Role |
|:--------|:----------|:-----|
| `gp11_triangleFreeCheck` | `triangleFreeCheck 11 2 = true` | closed `Bool` reduction over all `2·2·2·11·11·11` layer/index choices |
| `gp11_triangle_free` | for all `a b c : Fin 2`, `i j k : Fin 11`: `¬ Triangle (gp 11 2) (a,i) (b,j) (c,k)` | triangle-freeness, extracted from the `Bool` check |
| `gp11_no_triangle` | `∀ x y z : V 11, ¬ Triangle (gp 11 2) x y z` | component-free form |
| `gp11_triangle_count` | `triangleCount 11 2 = 0` | exhaustive enumeration of all `C(22,3) = 1540` triples |
| `gp6_triangle_count` | `triangleCount 6 2 = 2` | triangles occur only for `n = 6` among `n ≥ 4` |
| `gp12_triangle_count` | `triangleCount 12 2 = 0` | contrast: `12 ∤ 6` |
| `list_length_three` | any list of length `3` is `[x, y, z]` | list helper |
| `pancyclic_gp11_gives_3cycle` | `Pancyclic (gp 11 2) → HasCycleOfLength (gp 11 2) 3` | pancyclicity needs length 3 |
| `has3cycle_gp11_gives_triangle` | `HasCycleOfLength (gp 11 2) 3 → ∃ x y z, Triangle (gp 11 2) x y z` | a 3-cycle is a triangle |
| `gp11_no_3cycle` | `¬ HasCycleOfLength (gp 11 2) 3` | no 3-cycle |
| `gp11_not_pancyclic` | `¬ Pancyclic (gp 11 2)` | **main conclusion** |
| `conjecture_00000001682_false` | triangle-freeness `∧ ¬ Pancyclic (gp 11 2)` | packaged refutation |

## Proof strategy

* **Triangle-freeness by kernel reduction.** `gp11_triangleFreeCheck` is a
  closed `Bool` computation; `decide` reduces it to `true`. The propositions
  `¬ Triangle ...` are then read off with `List.all_eq_true` and
  `List.mem_finRange`. No case analysis by hand is needed: the kernel evaluates
  the adjacency predicate on every ordered triple.
* **Independent exhaustive count.** `triangleCount 11 2 = 0` enumerates the
  `C(22,3) = 1540` unordered triples only once (via the total index `ordIdx`),
  reproducing the brute-force count of `reproduce.py`.
* **From pancyclicity to a triangle.** `Pancyclic G` is unfolded at `L = 3`
  (`3 ≤ 3` and `3 ≤ 2·11` both hold), giving a closed walk of length `3`; any
  list of length three is `[x, y, z]` (`list_length_three`), whose
  `ClosedCycle` unfolds to `G x y = true`, `G y z = true`, `G z x = true`, i.e.
  `Triangle G x y z`. Contradiction with triangle-freeness yields
  `gp11_not_pancyclic`.
* **List rather than `Fin`-indexed cycles.** A `Fin L`-indexed closed walk needs
  an `OfNat (Fin L) 1` instance, which is unavailable for a variable `L` in core
  Lean. Encoding the walk as a list avoids that and keeps everything core-only.

## Axiom audit

`lake env lean Check.lean` reports no `sorryAx`. Typical output:

```text
'Tlmc1682.gp11_triangleFreeCheck' depends on axioms: [propext]
'Tlmc1682.gp11_triangle_free' depends on axioms: [propext, Quot.sound]
'Tlmc1682.gp11_no_triangle' depends on axioms: [propext, Quot.sound]
'Tlmc1682.gp11_triangle_count' depends on axioms: [propext]
'Tlmc1682.gp11_no_3cycle' depends on axioms: [propext, Quot.sound]
'Tlmc1682.gp11_not_pancyclic' depends on axioms: [propext, Quot.sound]
'Tlmc1682.conjecture_00000001682_false' depends on axioms: [propext, Quot.sound]
```

The only axioms are the core ones `propext` and `Quot.sound`; there is no
Mathlib dependency.

## Scope note

* The Lean development formalises **the concrete witness `G(11, 2)`** and the
  logical route pancyclic → 3-cycle → triangle → contradiction. This is enough
  to refute the conjecture's parenthetical claim `G(n,2) pancyclic for n ≥ 11`.
* The exhaustive search for cycle lengths `L = 3..2n`, and the table of missing
  lengths for `n = 5..16`, are carried out by `reproduce.py` (Python, standard
  library) and reported in `README.md` and `main.tex`. They are not replicated
  inside Lean, because the formal argument needs only the length-3 obstruction.
* The structural classification `GP(n,2)` has a triangle iff `n = 6` (for
  `n ≥ 4`) is proved in `main.tex` by hand and corroborated in Lean by
  `triangleCount 6 2 = 2` versus `triangleCount 11 2 = triangleCount 12 2 = 0`.

## Environment

Lean 4.33.1, Lake, `import Std` only, no Mathlib, no cache download required.
`set_option maxRecDepth 1000000` is set to allow the `decide`-based finite
reductions.
