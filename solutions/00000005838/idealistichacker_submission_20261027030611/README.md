# Disproof of Conjecture 00000005838

## Result and Exact Scope

Both languages assert that an involution centralizer has half its modular
p-blocks real-valued. Take the actual nonidentity involution in C2 and p=2.
Over the concrete algebraically closed characteristic-two field
K=AlgebraicClosure(ZMod 2), the actual modular group algebra K[C_G(s)] has
exactly one nonzero primitive central idempotent, hence one modular block.

For EVERY predicate selecting blocks, the selected subtype has an integer
cardinality r, so 2*r cannot equal 1. Therefore no block-selection predicate,
in particular the actual real-block predicate, can make the asserted half
count true. Rational and real half equalities are refuted explicitly, not
natural-number floor division. This is stronger than guessing a realness
value or classifying a few ordinary characters.

We refute this well-defined necessary conjunct of the universal source
claim. We do not formalize or repair its undefined dichotomy/kernel language,
or separately refute the conjugate-pair clause. No odd-prime, nonabelian,
simple-group or principal-block exclusion is inserted.

## Source and Mathematical Objects

`source.md` reproduces the complete bilingual Git blob from upstream commit
`b355e42906e6eaf52bc7e9d005e0ef02d8aa7400`, blob
`bcf128f6c8b7e7c438e4e096e9e99e38c3135082`, raw SHA-256
`c29985410d56eec486321081fc35957dbf31d5b14ffce47a32214383d48135d7`.
Original conjectures and organizer metadata are not modified.

- `lean4/BlockTheory.lean`: standard modular algebra blocks as ACTUAL nonzero
  primitive central idempotents, including actual multiplication/centrality
  and nontrivial orthogonal-decomposition conditions. If all idempotents are
  0 or 1, it proves block existence, uniqueness, finite cardinality one,
  finiteness of every predicate subtype and integer/rational half-count failure.
- `lean4/Involution.lean`: actual group Multiplicative(ZMod 2), actual
  nonidentity square-one element, genuine Subgroup.centralizer, its cardinality
  and an explicit group/algebra isomorphism to the original C2 algebra.
- `lean4/C2Algebra.lean`: all elements of actual MonoidAlgebra K C2, not a toy
  pair model; full coefficient decomposition and multiplication prove that
  every idempotent is zero or one over EVERY characteristic-two field.
- `lean4/Counterexample.lean`: concrete AlgebraicClosure(ZMod 2) field and
  characteristic/algebraic-closedness certificates, actual centralizer algebra
  transport, finite modular-block count one and natural/rational/real
  half-count negations for arbitrary dependent block-selection families.

The final theorem is
`Counterexample5838.half_clause_false_for_every_selection`. Its only explicit
parameter is an arbitrary selection family; no desired count, realness value
or negative conclusion is assumed. `lean4/Check.lean` prints all 34 actual
public theorem types and axiom footprints. Only `propext`, `Classical.choice`
and `Quot.sound` are permitted.

We use the standard primitive-central-idempotent definition of a modular
p-block. The standard correspondence with ordinary-character partition cells
is cited and reviewed in the paper, NOT advertised as a general Lean
character-theory theorem. No ordinary-character membership or realness
classifier is claimed: the predicate-parametric counting theorem requires
neither. This is not the characteristic-zero semisimple algebra C[C2].
See `statement-alignment.md`, `main.tex` and the actual compiled `main.pdf`.

## Reproduction

Use Python 3.10+, installed Lean 4.33.1, and an organizer-source Git checkout
containing the pinned source commit. Mathlib is pinned to
`0df444a360eaa60ab8c11dca51a86af692955474`; all nine dependency commits,
origins and lock specifications are included.

```text
python reproduce.py --lake <installed-Lean4.33.1-lake> --repo <organizer-source-checkout>
```

With the nine exact physical Git checkouts and compatible caches prepared:

```text
python reproduce.py --lake <installed-Lean4.33.1-lake> --repo <organizer-source-checkout> --skip-update
python -m unittest discover -s tests -q
```

The portable reproducer checks physical dependency paths, origins/HEADs,
tracked raw bytes, index/tree equality and frozen authored bytes before and
after execution. It clears only its OWN project build output, actually builds
Main, replays all four mathematical modules/Main with warnings as errors, and
checks every one of the 34 compiled types and axiom records. Junctions,
symbolic links and parent-Git redirects are rejected. Three exact inert
Windows Git-link-text dependency files are the sole documented exceptions;
those files are never executed. The whole-run budget is 285 seconds, and
timeout is failure. `--preflight-only` is not sufficient for release.

Exact finite group-algebra diagnostics over small fields and singleton
selection-count regressions are independent bounded checks, not the universal
proof over the actual algebraic closure. Synthetic tests exercise reproducer
safety, path, inventory, source, hash, timeout and dependency gates, not extra
mathematical assumptions.

Installed Lean and pinned dependency build caches remain trust inputs. No
full-dependency-clean build, empty-machine bootstrap, Linux, hosted-CI or human
expert verification is claimed. `review.json` records the actual separate AI
frozen-package review; it is not organizer acceptance.

AI-assisted submission by **idealistichacker**. No affiliation, priority,
acceptance, ranking or award is claimed. This is a request for review.
