# Disproof of conjecture `00000001245`

**Verdict: FALSE — the infimum is 0, and the proposed extremal rule has no
Garden-of-Eden patterns at all.**

## The conjecture (verbatim from `conjectures/00000001245.md`)

> Conjecture: Among elementary cellular automata, the infimum of the minimal
> densities of Garden-of-Eden patterns is 1/4 (a candidate extremal rule 51,
> programmatically verifiable).

**Object consistency.** We attack exactly: "minimal density of GoE patterns"
of an ECA rule (density = ones / width of the finite forbidden word), the
infimum over the 256 elementary rules, and the proposed extremal rule 51.

## Refutation 1 — rule 51 has NO GoE patterns

Rule 51 (output = NOT center) is a **bijection** on blocks of every width
(checked exhaustively for widths 2..10; the width-2 case is the Lean
certificate: the four blocks 00,01,10,11 map to 11,10,01,00). A bijective
global map has an empty Garden-of-Eden set. So the conjectured extremal
rule's minimal GoE density is not 1/4 — there is nothing to minimize.

## Refutation 2 — the infimum is 0

Rule 133 maps the four width-2 blocks 00,01,10,11 to 11,01,10,11 — **never
00**. The all-zeros word of width 2 is therefore a GoE pattern of rule 133,
and its density is 0/2 = **0** < 1/4. The infimum over the 256 rules is
consequently 0, not 1/4. (Exhaustive sweep in `reproduce.py`: **57** of the
256 elementary rules have a density-0 GoE word; the smallest such width is
2.)

## Reproduce

`python3 reproduce.py` — (a) verifies rule 51 is bijective on blocks of
widths 2..10; (b) sweeps all 256 rules × widths 2..10, listing every rule
with an all-zeros GoE word (57 rules) and the minimal such width; (c)
asserts rule 133 width-2 never outputs 00. Exit 0 iff all checks pass.

Lean: `cd lean4 && lake build && lake env lean Check.lean` — 14 theorems
(all `does not depend on any axioms`): the rule-51 width-2 bijection table,
the rule-133 width-2 table with the four "never 00" disjunctions, and the
density arithmetic 0/2 < 1/4 (cross-multiplied) with 0 ≠ 1/4.

## Boundary

Only the literal claim is refuted: inf = 0 ≠ 1/4, and rule 51 is not an
extremal witness (empty GoE set). Which rules are "extremal" among those
that do have GoE patterns is a different question, not needed here.
