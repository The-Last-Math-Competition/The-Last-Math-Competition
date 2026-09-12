# Disproof of conjecture `00000001243`

**Verdict: FALSE.** The central column of Wolfram's rule 30 is not square-free;
in fact *no* binary sequence is.

## The conjecture

> **Definition:** The central column of Wolfram's rule 30 is the output
> sequence of column 0 from a single 1 as initial condition.
> **Conjecture:** This sequence is not eventually periodic, and among its
> factors of length < 2^k none contains a square: the central column is
> square-free over all prefixes of length 2^k; this rules out any short-period
> structure.

## Why it is false

The refutation needs no dynamics of rule 30 at all.

**Lemma.** Every binary word of length ≥ 4 contains a square `uu`.

*Proof.* Let the first four letters be `s0 s1 s2 s3`. If `s0 = s1`, then `s0 s1`
is a square. Otherwise `s1 ≠ s0`; if `s1 = s2`, then `s1 s2` is a square.
Otherwise `s2 ≠ s1`, so `s2 = s0`; if `s2 = s3`, then `s2 s3` is a square.
Otherwise `s3 ≠ s2`, so `s3 = s1`, and `s0 s1 s2 s3 = s0 s1 s0 s1 = (s0 s1)²`.
∎

The bound is sharp: `010` has length 3 and is square-free.

The central column is a binary sequence, so it fails the property for every
prefix of length 2^k with k ≥ 2. The specific sequence is refuted even
earlier: its first terms are `1, 1, 0, 1, …`, so `11` is a square of period 1
at position 0, and the property fails already at k = 1.

**A consequence worth flagging to the maintainers.** The conjecture cannot
serve its stated purpose of "ruling out any short-period structure", because
it is satisfied by no binary sequence whatsoever. Any conjecture of the form
"this binary sequence is square-free" is refuted a priori. This looks like a
generation defect rather than a false mathematical claim: the *intended*
statement was presumably about factors of bounded length (the classical
square-free / overlap-free questions for rule 30 are meaningful), but as
written the quantifier over all factors makes the claim vacuous.

## Files

| file | purpose |
|---|---|
| `main.tex` | the proof (LaTeX) |
| `build/main.pdf` | compiled PDF, built with `tectonic` |
| `reproduce.py` | verifies the lemma exhaustively and locates the earliest square |
| `lean4/` | Lean 4 formalisation — **complete, builds with no `sorry`, core Lean only** |

## Scope of the refutation

The conjecture is a conjunction of two claims: (i) the central column is not
eventually periodic, and (ii) it is square-free over all prefixes of length
`2^k`. **Only (ii) is addressed here**, and refuting a conjunct refutes the
conjecture. Claim (i) is untouched, and is in our reading the harder of the two:
it is a genuine question about rule 30, whereas (ii) is refuted by a four-case
argument that never mentions rule 30.

## Reproducing

Pure Python 3, standard library only, no dependencies:

```bash
python3 reproduce.py
```

Output: the first 32 terms `11011100110001011001001110101110`, the earliest
square at `start=0, period=1, factor=[1, 1]`, and an exhaustive check that for
every `n` with `4 ≤ n ≤ 16` none of the `2^n` binary words is square-free.

The computation is a check, not a proof: Lemma 3.1 is a four-case argument.

## Status against the submission rules

Rule 3 requires a LaTeX source, a compiled PDF, and a Lean 4 project. All three
are present.

- **LaTeX source:** `main.tex`.
- **Compiled PDF:** `build/main.pdf`, built with `tectonic`.
- **Lean 4 project:** `lean4/`. Builds with `lake build` with **no `sorry`**,
  using **core Lean 4 only** (no Mathlib dependency). Every theorem depends only
  on the standard axiom `propext` — no `sorryAx`, no `Classical.choice`. The
  axiom check is machine-verifiable via `lake env lean Check.lean`.

The formalisation states the main result for an **arbitrary** `f : Nat → Bool`,
matching the paper's point that the obstruction has nothing to do with rule 30.
See `lean4/README.md` for the full statement table and the proof structure.
