# Submission: rule-3 disproof of conjecture 00000003949

**Conjecture (as stated).** The burning number of the `n × n` square grid
`P_n □ P_n` is **exactly** `⌈2√n − 1⌉`, and for a general `m × n` grid with
`m ≤ n` it is an explicit piecewise correction of this formula.

**Verdict: FALSE.** The closed form fails at `n = 4`:

| `n` | `b(P_n □ P_n)` | `⌈2√n − 1⌉` | match |
|----|----------------|--------------|-------|
| 1  | 1              | 1            | yes   |
| 2  | 2              | 2            | yes   |
| 3  | 3              | 3            | yes   |
| 4  | **4**          | **3**        | **no**|
| 5  | 4              | 4            | yes   |
| 6  | ≥ 5            | 4            | no    |

## The refutation

The burning process is equivalent to: `b(G) = min k` such that there exist
vertices `v₁,…,v_k` with `⋃ᵢ B(vᵢ, k−i) = V(G)` (round `i` has radius `k−i`).

* **No 3-round cover of the 4×4 grid exists.** For `k = 3` the radii are forced
  to be `2, 1, 0`; all `16³ = 4096` ordered centre triples were checked
  exhaustively and none covers all 16 cells.
* **A 4-round cover exists**, with centres (row, col)
  `(0,0)` r=3, `(0,2)` r=2, `(3,2)` r=1, `(2,3)` r=0; their union is all 16
  cells.
* Therefore `b(P₄ □ P₄) = 4 ≠ 3 = ⌈2√4 − 1⌉`.

The failure is not isolated: for `n = 6` the formula gives `4`, but an
exhaustive check of all `36⁴ = 1,679,616` ordered quadruples shows no 4-round
cover exists, so `b(P₆ □ P₆) ≥ 5`.

The formula does hold at `n = 1, 2, 3, 5`. However, the conjecture says
"is **exactly**" — an identity for all `n` — so a large-`n`/asymptotic reading
is not what the text states and would not rescue it at `n = 4` or `n = 6`.

## Contents

```
README.md              this file
main.tex               standalone article with the full proof (amdmath/amssymb/amsthm)
build/main.pdf         compiled article (tectonic)
reproduce.py           stdlib-only brute force, < 1s
lean4/
  lean-toolchain       leanprover/lean4:v4.33.1
  lakefile.toml        package tlmc3949, library Main
  Main.lean            formal refutation (core Lean + Std only)
  Check.lean           axiom audit
  README.md            Lean-specific notes
```

## Reproduce

```sh
# Python brute force (stdlib only)
python3 reproduce.py

# Lean formalisation
export PATH="$HOME/.elan/bin:$PATH"
cd lean4 && lake build && lake env lean Check.lean

# Article
cd ..
mkdir -p build && tectonic --outdir build main.tex
```

Expected: `lake build` succeeds with no `sorry`/`axiom`/`native_decide`;
`Check.lean` prints the three theorems depending only on `propext` (no
`sorryAx`, no `Lean.ofReduceBool`); `reproduce.py` exits 0 and prints
`REFUTATION VERIFIED: PASS`.
