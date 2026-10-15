# Conjecture 00000006238: a clopen singleton is not fixed by complement

**Status: disproved.** In the discrete space `X = {0,1}`, the subset `{0}`
is nonempty, proper, and clopen. Its complement is `{1}`, so it is not a
fixed point of the complement involution. This contradicts the conjecture's
explicit assertion that the fixed points of complement are the clopen
elements. The complement-square identity is valid.

The example uses the complete Boolean lattice `P(X)` of subobjects, with
ordinary set union, intersection, and complement. In the discrete topology,
both the closed and open subobject lattices are all of `P(X)`, so the
complement operation is defined on exactly the same complete lattice.
There is no reliance on an empty or improper clopen witness.

## Contents

- `proof.tex` and `proof.pdf`: the full mathematical disproof and the scope
  of its formalization.
- `lean4/`: a standalone Lean 4.24.0 project with no external dependencies.

## Reproduction

With the version in `lean4/lean-toolchain`, run in `lean4/`:

```console
lake build
lake exe verify
lake env lean Conjecture6238.lean
```

To compile the report from the submission directory:

```console
pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error proof.tex
pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error proof.tex
```

## What Lean verifies

The source defines subsets as predicates and their actual set operations.
It verifies arbitrary suprema and infima, complement-square, the Boolean
complement identities, and reversal of inclusion. A topology structure
requires all the standard topology axioms, including arbitrary unions;
the discrete topology on `Bool` is explicitly constructed with those proofs.

Closed is defined by openness of the complement, and clopen by the
conjunction of open and closed. The witness `singleton` consists exactly
of `false`; its complement consists exactly of `true`. Lean verifies
nonemptiness, properness, clopenness, and failure to be fixed by complement.
It also proves the general fact that complement has no fixed subset of
any inhabited set.

`not_discrete_fixed_point_claim` negates the precise fixed-point clause
restricted to the discrete two-point space. The universal topological
version is refuted by `not_universal_fixed_point_claim`. The final theorem
`refutes_every_claim_covering_discrete_case` records the logical implication
for any full claim containing the disputed clause. No interpretation of
the unrelated unspecified deficit term is needed to refute this conjunction.

The files contain no proof holes, native decision procedure, or custom
axioms. Axiom dependencies are printed by the source.

## Initial submission check

At selection, `metadata.csv` had both solved flags set to `false` for
`00000006238`, and no solution directory existed for that problem.
All contribution files are restricted to this personal submission directory.

## 中文说明

第 6238 题将补对合的不动点说成既闭又开的元素。取二点离散空间
`X={0,1}`，其幂集是完备布尔格，所有子集既闭又开。非空真子集 `{0}`
的补集却是 `{1}`，因此不是补对合的不动点，猜想中的这一明确子命题
为假。Lean 实际构造集合运算、任意上确界与下确界及满足所有公理的
离散拓扑，验证反例条件并证明相应全称命题的否定。
