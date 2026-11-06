# Disproof of Conjecture 00000000259

## Result and Source Correspondence

Both source languages explicitly concern **primes p = 1 modulo 4**. Every such
prime admits integers x,y with x^2-p*y^2=-1. Within this named prime class, the
actual finite counting ratio of solvable primes is identically one for N>=6.
Its limit is one, not the printed constant:

    C = 1 - product_{k>=2} (1 - 2^(-k)), with 1/4 <= C <= 7/16 < 1.

The denominator is explicitly the number of primes p<N with p=1 modulo 4.
This is the standard relative-prime-class interpretation of the printed density.
No uniform distribution on infinitely many primes is used. This is **not** a
resolution of the different literature conjecture about composite squarefree
radicands, a density theorem relative to all primes/integers, or a proof of the
source's introductory wide-class-number assertion. See `statement-alignment.md`.

`source.md` reproduces the exact bilingual source from upstream commit
`b355e42906e6eaf52bc7e9d005e0ef02d8aa7400`, Git blob
`15fe4da518462416cfbace31ff72247830e4ea6b`, raw SHA-256
`65b4858329041120379b9cff39d4e5df0f12e825236e59030c78c5d4ab0769e4`.
No original conjecture or organizer metadata is modified.

## Mathematical and Lean Content

- `lean4/PrimePell.lean`: genuine integer Pell solutions. Positive Pell
  existence/minimality and coprime square-factor descent prove negative Pell
  solvability for every eligible prime, not merely sampled primes.
- `lean4/ProductBounds.lean`: actual infinite-product convergence and exact
  rational bounds using finite-product and geometric-tail inequalities.
- `lean4/RelativeDensity.lean`: actual Finset counts, equality of successful and
  eligible prime sets, denominator positivity, eventual ratio one and its limit,
  and the closed negation of convergence to the printed constant.
- `lean4/Main.lean` imports the complete proof. `lean4/Check.lean` prints every
  one of the 19 actual theorem types and axiom footprints. Only `propext`,
  `Classical.choice`, and `Quot.sound` are allowed.

The complete proof is in `main.tex` and its actually compiled `main.pdf`.
No new axioms or proof escapes are introduced. The finite Python regressions
do not establish the universal Pell or asymptotic result.

## Reproduction

Use Python 3.10+, installed Lean 4.33.1, and an organizer-source Git checkout
containing the fixed source commit. Mathlib is pinned to
`0df444a360eaa60ab8c11dca51a86af692955474`; the complete nine-package lock is
included. Normal online preparation:

```text
python reproduce.py --lake <installed-Lean4.33.1-lake> --repo <organizer-source-checkout>
```

If the nine exact physical Git dependencies and compatible build caches have
already been prepared, the explicitly offline path is:

```text
python reproduce.py --lake <installed-Lean4.33.1-lake> --repo <organizer-source-checkout> --skip-update
python -m unittest discover -s tests -q
```

The reproducer checks source identity, declarative configuration, every theorem,
all fixed dependency origins/HEADs/tracked bytes/index/tree boundaries, and all
authored bytes before and after. It deletes **only its own project build cache**,
then builds Main, replays all authored math and Main with warnings as errors,
and checks every compiled type and axiom audit. Dependencies must own physical
`.git` directories; junctions, symbolic links and parent-Git redirects are
rejected. Three exact inert Git-link blobs may be ordinary link-text files on
Windows only; the corresponding benchmark scripts are never executed.

Default reproduction budget is 285 seconds within the coordinator's 300-second
subprocess limit. A timeout is failure, not permission to reuse old evidence.
`--preflight-only` never executes Lean and is **not** sufficient for publication.
`tests/test_reproduce.py` uses synthetic safety fixtures, not extra mathematical
proofs or claimed clean-platform tests.

Installed compiler and dependency build caches remain trust inputs. No
empty-machine, full-dependency-clean, cross-platform, hosted-CI or human-review
claim is made. `review.json` records a separate AI-agent review of the frozen
package; it does not substitute for the organizers' review.

AI-assisted submission by **idealistichacker**; no affiliation, acceptance,
award, ranking, or first-solver claim.
