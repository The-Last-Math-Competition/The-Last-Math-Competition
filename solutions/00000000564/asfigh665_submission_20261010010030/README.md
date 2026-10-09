# Conjecture 00000000564: a type A2 counterexample

**Status: disproved.** In the principal-coefficient cluster algebra of type A2,
the variable obtained by mutating the initial seed at vertex 1 has
`F(y1,y2) = 1 + y1`. Thus `F(1,1) = 2`, but the corresponding generalized
Catalan number is `Cat(A2) = (5/2)(6/3) = 5`, and `2` does not divide `5`.

This uses the usual finite-Coxeter-type generalized Catalan number
`Cat(W) = product_i (h + e_i + 1)/(e_i + 1)`, with type A2 data
`h = 3` and exponents `1,2`. The conjecture specifies no extra Fuss parameter.

## Contents

- `proof.tex`: the complete mathematical disproof, definitions, exchange
  relation, and scope of the formalization.
- `proof.pdf`: the compiled two-page report.
- `lean4/`: a standalone Lean 4.24.0 project using only Lean's standard library.

## Reproduce

Install the version in `lean4/lean-toolchain`, then run:

```sh
cd lean4
lake build
lake exe verify
lake env lean Conjecture564.lean
```

The last command prints the axiom dependencies of the main theorems. The
project contains no proof holes, native decision procedure, or custom axioms.
The allowed foundational axioms are `propext`, `Classical.choice`, and
`Quot.sound`; `decide +kernel` performs exact kernel-checked arithmetic.

To rebuild the report from this submission directory:

```sh
pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error proof.tex
pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error proof.tex
```

## Mathematical and formal correspondence

The Lean source constructs the rank-two integer exchange matrix and its
principal extension, checks its type A2 Cartan companion, and applies the
general initial F-polynomial mutation numerator using positive and negative
column exponents. All initial F-polynomials equal 1, so the recurrence divisor
is 1. The theorem `a2_first_mutation_polynomial` establishes `F = 1 + y1` for
every natural-number coefficient assignment, and
`a2_first_mutation_at_one` establishes its required specialization.

`generalizedCatalan` uses exact rational factors, and
`a2_generalizedCatalan` computes their product as 5.
`not_A2DivisibilityClaim` proves the negation of the universal first-mutation
divisibility requirement in type A2. The theorem
`refutesEveryClaimCoveringA2` states the logical reduction from any global
claim that includes this required instance.

This is an explicit counterexample formalization. The project does not
implement the general theory of finite Coxeter groups or the entire cluster
mutation graph. The report identifies the concrete Cartan matrix and standard
Coxeter data with type A2; the Lean theorem checks the corresponding mutation,
exact Catalan arithmetic, and failure of divisibility. One legitimate instance
is sufficient to disprove the universal assertion.

## Submission scope

At preparation, both solved flags for `00000000564` in `metadata.csv` were
`false`, there was no existing solution directory, and an all-state GitHub PR
search for this problem number returned no submissions. Only files under this
personal submission directory are included in this contribution.

## 中文说明

第 564 题被 A2 型的一个初始突变直接证伪：主系数交换关系为
`x1*x1' = y1 + x2`。把初始簇变量设为 1，得到 F 多项式 `1+y1`，
从而 `F(1,1)=2`；A2 型的广义 Catalan 数为 5，因此整除断言不成立。
LaTeX 报告给出完整推导，Lean 项目验证具体矩阵、突变计算、精确有理数
Catalan 积和该类型整除命题的否定。形式化的覆盖范围在上文明确列出。
