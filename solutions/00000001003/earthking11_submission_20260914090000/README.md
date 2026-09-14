# Disproof of conjecture `00000001003`

**Verdict: FALSE.**

This submission disproves conjecture `00000001003` as stated. The refutation is
unconditional, completely elementary, and does not depend on any unproved
hypothesis: at the first odd prime power `q = 3` the conjecture predicts a
maximal cap size of `14`, but `PG(4,3)` contains an explicit `20`-point cap.
The same formula is beaten at `q = 5` (an explicit `47`-point cap versus `33`),
the even-`q` clause fails at `q = 2` (a `16`-point cap versus `10`), and the
stated description "an elliptic quadric with an explicit three-point
augmentation" is internally inconsistent with the stated formula.

## The conjecture

Quoted verbatim from `conjectures/00000001003.md`:

> **English.** Definition: A cap is a point set of PG(n,q) with no three
> collinear. Conjecture: The maximal cap size in PG(4,q) is
> q²+q+1+⌊(q+1)/3⌋ for all odd q, attained by an elliptic quadric with an
> explicit three-point augmentation; for even q the value increases by 2.
>
> **中文。** 定义：cap 指 PG(n,q) 中无三点共线的点集。猜想：PG(4,q) 的最大 cap
> 尺寸为 q²+q+1+⌊(q+1)/3⌋(对一切奇 q),由椭圆二次曲面与三点的显式增补取得;
> 偶 q 时该值加 2。

**Definition (cap).** A *cap* in `PG(n,q)` is a set of points no three of which
are collinear. Its *size* is its cardinality; it is *inclusion-maximal* if no
further point can be added while remaining a cap.

Throughout, "maximal" is read as **maximum** (largest size), the only reading
under which the conjecture states a numerical value. The inclusion-maximal
reading is tested separately below.

## The 20-point cap in PG(4,3)

Coordinates are homogeneous on `PG(4,3)`, each point written in normalised form
(first nonzero coordinate equal to `1`). The following 20 points form a cap:

```
(1,0,0,0,2) (0,0,0,1,2) (1,2,2,1,1) (0,1,0,0,0) (1,0,2,1,2)
(1,0,1,2,0) (0,1,0,1,0) (1,2,1,2,1) (1,1,2,2,0) (1,2,0,1,2)
(1,2,0,1,0) (1,2,1,0,2) (1,0,1,1,0) (0,1,1,1,2) (0,0,1,0,0)
(0,1,2,2,0) (1,0,2,2,2) (1,2,1,2,2) (0,1,2,2,2) (1,1,0,1,1)
```

No three are collinear. Since the conjecture predicts

```
q² + q + 1 + ⌊(q+1)/3⌋  at q = 3  =  9 + 3 + 1 + ⌊4/3⌋  =  14,
```

we get `M₂(5,3) ≥ 20 > 14`, so the `q = 3` instance of "for all odd q" is
false.

### Three independent verifications

All three agree: **0 collinear triples**.

1. **Line membership.** `PG(4,3)` has 121 points and 1210 lines, each line
   having `q+1 = 4` points. Enumerating all lines and intersecting with the
   `C(20,3) = 1140` triples gives 0 collinear triples.
2. **Rank over F₃.** Three projective points are collinear iff the rank of their
   three coordinate vectors is `≤ 2`. Gaussian elimination over `F₃` on all 1140
   triples gives 0 triples of rank `≤ 2`.
3. **Kernel-checked Lean.** The executable checker in `lean4/Main.lean` (core
   Lean, `import Std`, no Mathlib, no `sorry`) returns `true` on the list; the
   theorem `pts20_isCap` is proved by `decide` and depends on no axioms.

The first two are reproduced from scratch by `reproduce.py`.

## The exact value 20 (SAT-certified upper bound)

We prove `M₂(5,3) ≥ 20`. The matching upper bound `M₂(5,3) ≤ 20` (no 21-point
cap) is a finite computation, reported here as **SAT-certified**, not
kernel-checked:

- a cap of size `≥ 21` spans `PG(4,3)` and therefore contains 5 linearly
  independent points;
- `GL(5,3)` is transitive on ordered bases of `F₃⁵`, so after a projectivity we
  may assume the 5 standard basis points lie in the cap;
- the resulting SAT instance (no three chosen points collinear, at least 21
  chosen) is **UNSAT**.

This matches the classical table value `M₂(5,3) = 20`. **The refutation of the
conjecture does not depend on this upper bound**: the lower bound
`20 > 14` already refutes the value `14`.

## The general formula fails at q = 5

`PG(4,5)` has 781 points. The formula predicts

```
25 + 5 + 1 + ⌊6/3⌋ = 33.
```

There is an explicit cap of **47** points in `PG(4,5)`; all
`C(47,3) = 16215` triples have rank 3 (verified by pairwise line membership and
by rank over `F₅` in `reproduce.py`). Hence `M₂(5,5) ≥ 47 > 33`. So the failure
is not an artefact of `q = 3`; it recurs at the next odd prime power, by a wide
margin. (A 46-point cap at `q = 5` was found earlier; the deterministic list
shipped here has 47 points and is strictly stronger.)

## The even-q clause fails at q = 2

For even `q` the conjecture adds 2 to the formula, giving at `q = 2`

```
4 + 2 + 1 + ⌊3/3⌋ + 2 = 10.
```

But `PG(4,2)` (31 points) contains the **16**-point cap
`{ (1,v) : v ∈ F₂⁴ }`, and in fact `M₂(4,2) = 16 = 2⁴`, the classical value
`M₂(n,2) = 2ⁿ`. The lower bound 16 is verified in `reproduce.py`; the upper
bound `M₂(4,2) ≤ 16` (equivalently, `≥ 17` is UNSAT) is again a finite SAT
certificate, reported as such. So the even-`q` clause is off by 6 at `q = 2`,
and in the direction opposite to the conjecture's "increases by 2".

## Internal inconsistency of the description

The conjecture says the value is "attained by an elliptic quadric with an
explicit three-point augmentation". An elliptic quadric in this setting
contributes `q² + 1` points; adding three gives `q² + 4`. At `q = 3` this is
`13`, whereas the stated formula gives `14`. In general

```
(q²+q+1+⌊(q+1)/3⌋) − (q²+4) = q − 3 + ⌊(q+1)/3⌋ > 0   for odd q ≥ 3,
```

so the construction does not attain the stated value and the stated value is
not produced by the construction: the two halves of the sentence are mutually
inconsistent. At `q = 5`: `29` (quadric description) versus `33` (formula).

## Alternative readings

We tried to save the conjecture by varying the reading; none succeeds.

| Reading | Outcome |
|:--------|:--------|
| Relax "cap" (allow some collinear triples) | Contradicts the file's own definition of a cap and has no canonical value, so the conjecture then states no definite number; it is not a well-posed claim. |
| "Maximal" means inclusion-maximal | The 20-cap above **is** inclusion-maximal (verified: no point of `PG(4,3)` can be added). A survey of 3000 random greedy inclusion-maximal caps gave sizes 16–20 (distribution `16:84, 17:292, 18:1889, 19:459, 20:276`), **never** 14. So this reading does not force the value 14 either. |
| "The formula is meant for `q ≥ 5`" | Fails at `q = 5`: an explicit 47-point cap versus the predicted 33. |
| Even-`q` clause taken as the base formula | Fails at `q = 2`: 16 versus 10. |

Only the first line changes the meaning of a term rather than a quantifier
range; under the file's own definition of "cap" it does not apply.

## Caveats

- The exact upper bounds `M₂(5,3) ≤ 20` and `M₂(4,2) ≤ 16` rest on SAT
  certificates over finite search spaces, not on kernel-checked proofs. They are
  not needed for the refutation, which is a pure existence statement
  (`20 > 14`).
- The `q = 5` and `q = 2` results are verified computationally in
  `reproduce.py` from explicitly listed points using two independent criteria.
  The `q = 5` list was found by randomised greedy search and is then frozen and
  re-verified from scratch; no randomised step remains in the reproduction.
- The Lean formalisation is deliberately scoped to the `q = 3` refutation
  (the component needed to make the verdict rigorous), and proves only the
  existence of the 20-cap, not the upper bound. See `lean4/README.md`.

## Files

| File | Description |
|:-----|:------------|
| `README.md` | This document: verdict, bilingual quote, definition, the 20-cap and its three verifications, the exact value 20 (SAT-certified upper bound), the `q = 5` and even-`q` failures, the quadric inconsistency, alternative readings, caveats, file list, repro commands, rule-3 status. |
| `main.tex` | LaTeX source of the disproof (standalone `article`). |
| `build/main.pdf` | PDF produced by `tectonic --outdir build main.tex`. |
| `reproduce.py` | Python 3 (standard library only) verification: builds `PG(4,3)` (121 points, 1210 lines), checks the 20 points and all 1140 triples by two criteria, checks `20 > 14` and inclusion-maximality, verifies the 47-cap in `PG(4,5)` and the 16-cap in `PG(4,2)`, checks the quadric/formula mismatch; prints `PASS`/`FAIL` and exits non-zero on failure. |
| `lean4/lean-toolchain` | Pins `leanprover/lean4:v4.33.1`. |
| `lean4/lakefile.toml` | Lake configuration; library `Main`, project `tlmc1003`, no dependencies. |
| `lean4/Main.lean` | Lean 4 formalisation of the `q = 3` refutation, core Lean only (`import Std`, no Mathlib, no `sorry`). |
| `lean4/Check.lean` | `#print axioms` audit for every theorem. |
| `lean4/README.md` | Statement table, representation, executable cap test, axiom audit, scope note. |

## Reproducing

Python (dependency-free, runs in well under a second):

```sh
python3 reproduce.py
```

It builds `PG(4,3)` and `PG(4,5)`, verifies the caps by line membership and by
rank over the prime field, prints `PASS`, and exits `0`.

LaTeX document:

```sh
tectonic --outdir build main.tex
```

Lean 4 project:

```sh
cd lean4
lake build
lake env lean Check.lean
```

`lake build` exits `0` (about 7 seconds on first build); `Check.lean` prints
`#print axioms` for every theorem and reports **"does not depend on any
axioms"** for all of them — no `sorryAx`, no `Lean.ofReduceBool`, no Mathlib.

## Status against the submission rules

Rule 3 requires each submission to contain the LaTeX source, a PDF document, and
a Lean 4 project.

- **LaTeX source** — present (`main.tex`), a standalone `article` using only
  `geometry`, `amsmath`, `amssymb`, `amsthm`, `array`, `parskip`, `booktabs`;
  compiles with `tectonic --outdir build main.tex`.
- **PDF document** — present at `build/main.pdf`.
- **Lean 4 project** — present under `lean4/`, with `lean-toolchain`
  (`leanprover/lean4:v4.33.1`), `lakefile.toml` (library `Main`, project
  `tlmc1003`, no dependencies), `Main.lean`, `Check.lean`, and `README.md`. It
  formalises `formula`, the executable cap test `isCap`, the 20-point cap
  `pts20`, `pts20_isCap`, `formula_three : formula 3 = 14`,
  `formula_three_lt_length`, and the main theorem `refutes_conjecture`
  (`∃ S, S.length = 20 ∧ isCap S = true ∧ formula 3 < S.length`). It uses core
  Lean only (no Mathlib), contains no `sorry`, and the audit reports no
  `sorryAx`.
