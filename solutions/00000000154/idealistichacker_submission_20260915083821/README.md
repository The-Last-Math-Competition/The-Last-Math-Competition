# Disproof package for conjecture 00000000154

**Status: local, unreviewed preparation only.** This directory is neither an
upstream pull request nor an organizer-accepted solution. It claims no award,
priority, affiliation, or human verification. It includes a real `main.pdf`
compiled from `main.tex`, but has **no** `review.json`: an independent review
remains a publication gate.

Prepared with AI assistance for GitHub account `idealistichacker`; no
institutional affiliation is claimed.

## Frozen organizer statement

The source is `conjectures/00000000154.md` at organizer commit
`95acb520ec5607c826b8a997b1ef2fc82d6f7c57`:

> **English.** Conjecture: Prime values of derangement numbers: there exist
> infinitely many even n such that D_n is prime (D_n can be odd only when n is
> even).
>
> **中文。** 猜想：错排数 D_n 的素值:存在无穷多偶数 n 使 D_n 为素数(D_n 为奇要求 n 偶)。

- Frozen Git blob: `5d2fb2e814a4c521d2ace36034863cc8ec6fe836`.
- SHA-256 of frozen Git-blob bytes:
  `694c389d34ad78b41caae8ad4e1f414fa0541e6b19b81aeab432466039dc87c1`.
- Text-hash convention: UTF-8 bytes with CRLF normalized to LF; for this text
  file this equals the Git blob's content hash input.

Neither the original conjecture nor organizer metadata is modified.

## Result, source-statement bridge, and proof outline

Under the standard definition of `D_n` as the number of fixed-point-free
permutations of an `n`-element set, the conjecture is false. The index set
whose infinitude the source asserts is formalized as:

```lean
TLMC154.evenPrimeDerangementIndices : Set ℕ :=
  {n | Even n ∧ Nat.Prime (Fintype.card (derangements (Fin n)))}
```

The final statement bridge is not only an indexed recurrence theorem. Lean
proves both:

```lean
TLMC154.fin_all_even_derangements_card_not_prime :
  ∀ n : ℕ, Even n →
    ¬ Nat.Prime (Fintype.card (derangements (Fin n)))

TLMC154.evenPrimeDerangementIndices_eq_empty :
  evenPrimeDerangementIndices = ∅

TLMC154.evenPrimeDerangementIndices_not_infinite :
  ¬ Set.Infinite evenPrimeDerangementIndices
```

This directly negates the source's existence of infinitely many even prime
indices. It uses Mathlib's actual subtype `derangements (Fin n)`, not a custom
sequence. The proved bridge
`card_derangements_fin_eq_numDerangements` connects the cardinality of that
subtype with Mathlib's derangement recurrence.

The proof has exactly these branches:

1. `D_0 = 1`, so index `0` is not prime.
2. `D_2 = 1`, so index `2` is not prime.
3. For every even `n >= 4`,
   `D_n = (n - 1) * (D_(n-1) + D_(n-2))`. Both derangement numbers in the
   second factor are positive, so the second factor is at least two while
   `n - 1 >= 3`; hence the product is not prime.

The parenthetical source remark that `D_n` *can be odd only when n is even* is
contextual information about parity. It is **not** the target of this proof,
not an extra premise, and not asserted here as a new theorem. The proof only
addresses the claimed existence of infinitely many **even** indices with prime
`D_n`.

`main.tex` gives the complete English mathematical argument and repeats this
scope boundary.

## Lean project and axiom transparency

The project requires:

- Lean `leanprover/lean4:v4.33.1`;
- Mathlib input tag `v4.33.1` pinned by `lean4/lake-manifest.json` to resolved
  commit `0df444a360eaa60ab8c11dca51a86af692955474`;
- Python 3 standard library plus Git for the reproducer.

`lean4/Check.lean` prints the transitive dependencies of every theorem named in
`submission.json`. The expected dependency footprint is:

| Theorems | Printed dependencies |
| --- | --- |
| positivity and recurrence-factorization lemmas | `[propext, Quot.sound]` |
| cardinality bridge, all-even theorem, empty-set bridge, and non-infinite bridge | `[propext, Classical.choice, Quot.sound]` |

These are standard Lean/Mathlib logical, choice, and quotient principles. This
is **not** a zero-axiom claim. The package declares no custom axiom and has no
`sorry`, `admit`, `native_decide`, or `unsafe` in `Main.lean`.

## Reproduce the Lean evidence

From this directory:

```powershell
python .\reproduce.py `
  --lake 'D:\AStudy\开源杂\LastMathC\.local\tools\lean-4.33.1-windows\bin\lake.exe'
```

The script is Python-standard-library only. It verifies the source commit,
Git blob, and SHA-256; checks the Lake manifest's exact Mathlib revision; runs
`lake update` with Mathlib's automatic binary-cache hook disabled (so a clean
machine can source-build rather than depending on that optional hook); then
runs `lake build`, a direct `Main.lean` replay, and `Check.lean`.

Pass `--skip-update` only when exact dependencies are already materialized.
The script never compiles LaTeX, creates a PDF, writes Git history, pushes, or
contacts GitHub.

## Evidence and remaining gates

On **2026-09-15**, the final packaged Lean sources were actually checked with
Lean 4.33.1 by `lake build`, direct `Main.lean` replay, and `Check.lean`; all
three exited `0`. The resulting audit is reported to the coordinator and is
not an independent review.

Before release, a different agent must independently review mathematics, Lean
correspondence, source-statement alignment, reproducibility, and the compiled
PDF. The release coordinator must create a truthful `review.json`, reproducibly
rebuild and compare `main.pdf`, refresh upstream source and duplicate checks
immediately before publication, and obey the one-active-
upstream-solution-PR limit. Local verification never implies organizer
acceptance.


## PDF build record

The coordinator compiled `main.tex` with **Tectonic 0.15.0** and
`SOURCE_DATE_EPOCH=0`, producing `main.pdf` with SHA-256
`6b8a63cb4e5c22cf7ef4361fac6ae5d84682784d5ff931479c98c4eda025680c`.
The two rendered pages were visually inspected. This verifies the local artifact
only; independent review and organizer acceptance remain absent.
