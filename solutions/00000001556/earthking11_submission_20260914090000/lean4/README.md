# Lean 4 formalisation — disproof of conjecture `00000001556`

Core Lean only (`import Std`), no Mathlib, no `sorry`. The project pins
`lean-toolchain` to `leanprover/lean4:v4.33.1` and defines the library `Main` in
`lakefile.toml`.

The conjecture claims that the chromatic number of the lattice distance graph
`G(Z², D)` with `D = {1, 2, 4}` is `7`. It is false.

## Build and audit

```sh
lake build
lake env lean Check.lean
```

`Check.lean` prints `#print axioms` for every theorem so a reviewer can confirm
the absence of `sorryAx` and of Mathlib dependencies.

## What is formalised

The file writes three scalars, so `D` is a set of distances; lattice-colouring
work also states distance sets as **squared** norms. Both standard readings are
covered at once by taking `D` to be the union of their displacement sets.

```lean
/-- Union of the two plausible displacement sets for "D = {1,2,4}". -/
def D : List (Int × Int) :=
  [(1,0),(-1,0),(0,1),(0,-1),
   (1,1),(1,-1),(-1,1),(-1,-1),
   (2,0),(-2,0),(0,2),(0,-2),
   (4,0),(-4,0),(0,4),(0,-4)]

/-- The 5-colouring c(x,y) = (x + 2y) mod 5. -/
def color (p : Int × Int) : Int := (p.1 + 2 * p.2) % 5

/-- The 3-colouring c3(x,y) = (x + y) mod 3 (Euclidean reading). -/
def color3 (p : Int × Int) : Int := (p.1 + p.2) % 3
```

`D` contains the edge set of **both** readings:

- squared reading `Dsq`: `dx² + dy² ∈ {1,2,4}` (12 vectors);
- Euclidean reading `Deuc`: `dx² + dy² ∈ {1,4,16}` (12 axis vectors);
- the union has 16 vectors (the Euclidean reading adds `(±4,0)`, `(0,±4)`).

| Theorem | Statement | Role |
|:--------|:----------|:-----|
| `D_ok` | `D.all (fun e => (e.1 + 2*e.2) % 5 ≠ 0) = true` | all 16 residues nonzero, by `decide` |
| `color_shift_ne` | `∀ x y d, d ∈ D → color (x+d₁, y+d₂) ≠ color (x,y)` | **properness of the 5-colouring** (upper bound `χ ≤ 5`) |
| `adjacent_colors_ne` | adjacency form of the same statement | edge endpoints get distinct colours |
| `Deuc_ok` | `Deuc.all (fun e => (e.1 + e.2) % 3 ≠ 0) = true` | all 12 Euclidean residues nonzero, by `decide` |
| `color3_shift_ne` | `∀ x y d, d ∈ Deuc → color3 (x+d₁, y+d₂) ≠ color3 (x,y)` | properness of `c3` for the Euclidean reading (`χ ≤ 3`) |
| `C5_clique` | `C5.all (fun p => C5.all (fun q => pairAdj p q)) = true` | **5-clique** certificate (`χ ≥ 5` for the squared / union graph) |
| `C3_clique` | `C3.all (fun p => C3.all (fun q => pairAdj p q)) = true` | **3-clique** certificate (`χ ≥ 3` for the Euclidean graph) |

The clique certificates are Boolean `decide` computations:
`pairAdj p q := p == q || D.contains (q₁ - p₁, q₂ - p₂)`.

## Proof strategy

- **Residue computation** (`D_ok`, `Deuc_ok`). Kernel reduction of 16 (resp. 12)
  integer residue tests; these depend on no axioms.
- **Properness** (`color_shift_ne`). `List.all_eq_true` extracts
  `(d₁ + 2 d₂) % 5 ≠ 0` from `D_ok`; then `simp only [color]` reduces the goal
  to an arithmetic fact about `Int.emod`, closed by `omega`.
- **Cliques** (`C5_clique`, `C3_clique`). Kernel reduction of the pairwise
  adjacency test over the explicit point lists `C5` and `C3`.

Combining: `color_shift_ne` gives `χ(union) ≤ 5` and `C5_clique` gives
`χ(union) ≥ 5`, so `χ(union) = 5`; a fortiori `χ ≤ 5` for each of the two
readings. Since `5 < 7`, the conjectured value `7` is false under both standard
readings. For the squared reading the two bounds meet exactly at `5`; for the
Euclidean reading `color3_shift_ne` and `C3_clique` meet exactly at `3`.

## Axiom audit

`lake env lean Check.lean` reports:

- `D_ok`, `Deuc_ok`, `C5_clique`, `C3_clique`: **no axioms** (pure `decide`);
- `color_shift_ne`, `adjacent_colors_ne`, `color3_shift_ne`: `propext`,
  `Quot.sound`.

No `sorryAx` appears for any theorem.

## Scope note

- The properness theorem `color_shift_ne` is symbolic and holds for **every**
  lattice point `(x,y) ∈ Z²` and **every** displacement `d ∈ D`; it is not a
  finite-box check. The finite `decide` computations only certify the residue
  table and the cliques.
- `D` is the union of the two standard displacement sets, so a single colouring
  refutes both readings simultaneously. The lower-bound cliques live in `D`
  (indeed `C5 ⊆ Dsq ⊆ D` and `C3 ⊆ Deuc ⊆ D`), so they also apply to the union
  graph.
- The chromatic number of the *continuous* plane `R²` for the distance set
  `{1,2,4}` is a different (and not settled by this argument) problem; the
  conjecture is written for the integer lattice `Z²`. The periodic colourings
  extend to all of `Z²`; by the de Bruijn–Erdős compactness theorem the
  chromatic number of a lattice graph is the supremum over its finite subgraphs.
- `Int.emod`, `Int.add_emod`, `List.all_eq_true`, `decide` and `omega` are all
  available in `import Std`; no `Finset`, `ZMod` or `Complex` is needed.

## Environment

Lean 4.33.1, Lake, no Mathlib. `lake build` needs no cache download.
