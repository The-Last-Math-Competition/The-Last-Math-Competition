# Disproof of conjecture `00000001203`

**Verdict: FALSE.**

This submission disproves conjecture `00000001203` as stated. The refutation is
unconditional and elementary. The primary witness is the move set
`S = {1, 3}` with `k = 3`: its SG sequence is `0, 1, 0, 1, …`, whose least
period is **2**. Since `k = 3 ∈ S`, the conjecture demands the period be exactly
`k + 1 = 4`. Crucially `max(S) = 3 = k`, so the two possible readings of the
parameter `k` — ambient bound versus `k = max(S)` — **coincide**, and the
refutation is free of any interpretation of `k`. Corroborating witnesses
(`S = {2}` for the second clause, `S = {1, 2}` for the first clause) confirm
that the failure is systematic.

## The conjecture

Quoted verbatim from `conjectures/00000001203.md`:

> **English.** Definition: An addition-subtraction game is a subtraction game
> whose legal moves are the fixed values in a set S; the SG period is the least
> positive period of g(n). Conjecture: If S ⊂ {1,…,k}, then the period of g
> divides 2^k−1 if and only if S is nonempty and does not contain k; when k ∈ S
> the period is exactly k+1.
>
> **中文。** 定义：加法减法游戏指合法步数为集合 S 中固定值的减法博弈,SG
> 序列周期指 g(n) 的最小正周期。猜想：若 S⊂{1,…,k} 则 g 的周期整除 2^k−1
> 当且仅当 S 非空且不含 k;含 k 时周期恰为 k+1。

Written as two clauses:

- **(C1)** the least period of `g` divides `2^k − 1` **iff** `S` is nonempty and
  `k ∉ S`;
- **(C2)** if `k ∈ S`, the least period is exactly `k + 1`.

Both clauses fail; see below.

## The game and the SG recursion

For a move set `S`, the SG sequence is

```
g(0) = 0,    g(n) = mex { g(n - s) : s ∈ S, s ≤ n },
```

and the SG period is the least positive `p` with `g(n + p) = g(n)` for all
`n ≥ 0`.

## Primary witness: `S = {1, 3}`, `k = 3`

The recursion is `g(n) = mex{g(n−3), g(n−1)}` for `n ≥ 3`, with the base cases
`g(0) = mex ∅ = 0`, `g(1) = mex{0} = 1`, `g(2) = mex{1} = 0`. The first terms
are

```
n     : 0  1  2  3  4  5  6  7  8  9 10 11 ...
g(n)  : 0  1  0  1  0  1  0  1  0  1  0  1 ...
```

**Claim.** `g(n) = n mod 2` for all `n`. *Proof.* Strong induction. For `n ≥ 3`
both predecessors `n − 3` and `n − 1` have the parity of `n − 1`, so by
induction `g(n−3) = g(n−1) = (n−1) mod 2 = a ∈ {0,1}`. Hence
`g(n) = mex{a, a} = mex{a} = 1 − a = n mod 2`. ∎

Consequently `2` is a period (`g(n+2) = g(n)`), and `1` is not
(`g(1) = 1 ≠ 0 = g(0)`). So the least period is exactly **2**.

Because `k = 3 ∈ S`, clause (C2) demands least period `k + 1 = 4`. The actual
least period is `2 ≠ 4`, so the conjecture is false. (With `S = {1,3}`,
`k = 3`, clause (C1) happens to hold: the right-hand side is false because
`3 ∈ S`, and the left-hand side is false because `2 ∤ 2³ − 1 = 7`. It is
clause (C2) that fails for this witness.)

## Corroborating witness for clause (C2): `S = {2}`, `k = 2`

Here the only move is `2`, so `g(n) = mex{g(n−2)}` for `n ≥ 2` and
`g(0) = g(1) = 0` (the move `2` is illegal at `n = 1`). The sequence is

```
n     : 0  1  2  3  4  5  6  7 ...
g(n)  : 0  0  1  1  0  0  1  1 ...
```

i.e. `g(n) = ⌊n/2⌋ mod 2`, with least period **4**. Since `k = 2 ∈ S`, clause
(C2) demands period `k + 1 = 3`; it is `4 ≠ 3`. Again `max(S) = 2 = k`, so this
witness is also interpretation-free.

## Corroborating witness for clause (C1): `S = {1, 2}`

Here `g(n) = mex{g(n−2), g(n−1)}` for `n ≥ 2`, giving

```
n     : 0  1  2  3  4  5 ...
g(n)  : 0  1  2  0  1  2 ...
```

i.e. `g(n) = n mod 3`, with least period **3**. Note `3 = 2² − 1`, so the
period **does divide** `2² − 1`.

- **Charitable reading** `k = max(S) = 2`: because `k = 2 ∈ S`, the right-hand
  side of (C1), “`S` nonempty and `k ∉ S`”, is false, so (C1) requires the period
  **not** to divide `2² − 1 = 3`. But `3 ∣ 3`. Clause (C1) fails.
- **Ambient reading** with `k = 3`: the set `S = {1,2}` is a **proper** subset of
  `{1,2,3}`, the right-hand side is true (`3 ∉ S`), so (C1) requires
  `3 ∣ 2³ − 1 = 7`. But `3 ∤ 7`. Clause (C1) fails again.

So no reading of `k` survives.

## The reading of `k` is genuinely ambiguous

The conjecture writes “if `S ⊂ {1,…,k}`”, which admits two natural readings:

- **(A) ambient bound:** `k` is the bound in `{1,…,k}`, so `S ⊆ {1,…,k}` for a
  `k` that may strictly exceed `max(S)`. This is the reading the literal text
  supports: `k` is introduced as the bound of `{1,…,k}`, and the condition
  “does not contain `k`” is a genuine, non-vacuous condition only when `k` can
  lie outside `S`.
- **(B) charitable / tight reading:** `k = max(S)`. Under this reading the
  condition “`S` nonempty and does not contain `k`” is never satisfiable, since
  `max(S) ∈ S` by definition; the biconditional then degenerates.

**This is a real ambiguity in the text, and we flag it explicitly.** The
primary witness `S = {1,3}`, `k = 3` is immune to it: ambient `k = 3` and
`max(S) = 3` agree, so the demanded period is `k + 1 = 4` under either reading
while the actual period is `2`. The earlier candidate `S = {1}` with `k = 3`
was rejected for exactly this reason: under reading (B) one has `k = 1`, the
period `2 = k + 1`, and the witness no longer refutes clause (C2). `S = {1,3}`
is the robust witness.

## Least periods for `k = 2, 3, 4`

The table lists the least period of `g` for every nonempty `S ⊆ {1,…,k}`, and
whether the conjecture holds for that row under each reading of `k` (`holds` /
`fails`). All values are computed by `reproduce.py` from 600 terms.

| `k` | `S` | least period | (A) ambient `k` | (B) `k = max(S)` |
|----:|:----|:------------:|:---------------:|:----------------:|
| 2 | `{1}`       | 2 | fails | holds |
| 2 | `{2}`       | 4 | fails | fails |
| 2 | `{1,2}`     | 3 | fails | fails |
| 3 | `{1}`       | 2 | fails | holds |
| 3 | `{2}`       | 4 | fails | fails |
| 3 | `{3}`       | 6 | fails | fails |
| 3 | `{1,2}`     | 3 | fails | fails |
| 3 | `{1,3}`     | 2 | **fails (primary witness)** | **fails (primary witness)** |
| 3 | `{2,3}`     | 5 | fails | fails |
| 3 | `{1,2,3}`   | 4 | holds | holds |
| 4 | `{1}`       | 2 | fails | holds |
| 4 | `{2}`       | 4 | fails | fails |
| 4 | `{3}`       | 6 | fails | fails |
| 4 | `{4}`       | 8 | fails | fails |
| 4 | `{1,2}`     | 3 | holds | fails |
| 4 | `{1,3}`     | 2 | fails | fails |
| 4 | `{1,4}`     | 5 | fails | fails |
| 4 | `{2,3}`     | 5 | holds | fails |
| 4 | `{2,4}`     | 6 | fails | fails |
| 4 | `{3,4}`     | 7 | fails | fails |
| 4 | `{1,2,3}`   | 4 | fails | holds |
| 4 | `{1,2,4}`   | 3 | fails | fails |
| 4 | `{1,3,4}`   | 7 | fails | fails |
| 4 | `{2,3,4}`   | 6 | fails | fails |
| 4 | `{1,2,3,4}` | 5 | fails | fails |

Reading (A) is violated in 3/3 rows for `k = 2`, 6/7 for `k = 3`, and 13/15 for
`k = 4`; reading (B) is violated in 2/3, 5/7, and 13/15 rows respectively. Each
table therefore contains violations under either reading.

## Honesty and caveats (required reading)

1. **The only escape and why it fails.** One might try to repair the conjecture
   by restricting clause (C2) to the *full* sets `{1,…,k}`. **The text does not
   state such a restriction.** Even granting it, the conjecture still fails:
   clause (C1) is refuted by `S = {1,2}` (`0,1,2` repeating; period `3` divides
   `2² − 1 = 3` although the charitable reading forbids it under clause (C1)).
   So no such restriction rescues the claim.
2. **The parameter `k` is genuinely ambiguous** (ambient bound versus
   `k = max(S)`); this is a defect of the statement as filed, and we say so.
   The primary witness `S = {1,3}`, `k = 3` is immune to the ambiguity because
   `max(S) = k = 3`.
3. **The fragile witness `S = {1}`, `k = 3` is not used** to carry the
   refutation: under reading (B) it is rescued, since then `k = 1` and the
   period `2 = k + 1`.

## Files

| File | Description |
|:-----|:------------|
| `README.md` | This document: verdict, bilingual quote, SG computations, witnesses, `k`-reading caveat, period table, reproduction, status. |
| `main.tex` | LaTeX source of the disproof. Standalone `article`, compiles with `tectonic`. |
| `build/main.pdf` | PDF produced by `tectonic --outdir build main.tex`. |
| `reproduce.py` | Python 3 (standard library only): SG recursion for all nonempty `S ⊆ {1,…,k}`, `k = 2,3,4`, least periods over 600 terms, witness checks, violations tables for both readings; prints `PASS`/`FAIL`, non-zero exit on failure. |
| `lean4/lean-toolchain` | Pins `leanprover/lean4:v4.33.1`. |
| `lean4/lakefile.toml` | Lake configuration; library `Main`, name `tlmc1203`, no dependencies. |
| `lean4/Main.lean` | Core Lean 4 formalisation (`import Std`, no Mathlib, no `sorry`): `g_eq : g n = n % 2`, `IsLeastPeriod`, `least_period_two`, `not_least_period_four`, the clause-1 witness `g12`, and `conjecture_00000001203_false`. |
| `lean4/Check.lean` | `#print axioms` audit for every theorem. |
| `lean4/README.md` | Statement table, proof strategy, and scope/ambiguity note for the formalisation. |

## Reproducing

Python (dependency-free, runs in well under a second):

```sh
python3 reproduce.py
```

It verifies `g(n) = n mod 2` and least period `2` for `S = {1,3}` (claimed
`k+1 = 4`), least period `4` for `S = {2}` (claimed `3`), and least period `3`
with `3 ∣ 2² − 1` for `S = {1,2}`; then it tabulates the least period of every
nonempty `S ⊆ {1,…,k}` for `k = 2,3,4` and reports the violations under both
readings of `k`. A `FAIL` (non-zero exit status) means a claimed fact did not
verify.

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

The audit reports only `[propext, Quot.sound]` (and no axioms for
`three_dvd_two_sq_sub_one`); there is no `sorryAx`.

## Status against the submission rules

Rule 3 requires each submission to contain the LaTeX source code, a PDF
document, and a Lean 4 project.

- **LaTeX source** — present (`main.tex`), a standalone `article` that uses only
  `geometry`, `amsmath`, `amssymb`, `amsthm`, `array`, `parskip`, and
  `booktabs`, and compiles with `tectonic`.
- **PDF document** — present at `build/main.pdf`, produced by
  `tectonic --outdir build main.tex`.
- **Lean 4 project** — present under `lean4/`, pinned to
  `leanprover/lean4:v4.33.1`, library `Main` (name `tlmc1203`). It formalises
  the primary witness's closed form and least period (`g_eq`,
  `least_period_two`, `not_least_period_four`), the clause-1 witness
  (`g12_eq`, `least_period_three_12`, `three_dvd_two_sq_sub_one`,
  `clause1_fails_charitable`), and packages them in
  `conjecture_00000001203_false`. It uses core Lean only (no Mathlib) and
  contains no `sorry`; `lake env lean Check.lean` reports no `sorryAx`.
- **Reproduction script** — `reproduce.py` uses the Python 3 standard library
  only; it prints `PASS` and exits `0` exactly when every check holds.
