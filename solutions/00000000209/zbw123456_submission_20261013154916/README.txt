Conjecture 00000000209: the literal whole-prefix recurrence
=========================================================

STATUS AND SCOPE

The Lean proof is complete for the recurrence printed in the problem: the
entire preceding word must equal Y^k. Its unique solution is 1,1,2,1,1,1,...,
so 5 never occurs. Existence, uniqueness and the universal absence of 5
are all proved, not inferred from a finite prefix computation.

This is NOT a disproof about the standard Gijswijt sequence. That sequence
uses XY^k, permitting an arbitrary initial word X. The problem's name and
parenthetical occurrence information conflict with its displayed rule.
If the maintainer interprets the problem as the standard XY^k recurrence,
this submission is not applicable. No official acceptance is claimed.

FILES

proof.tex                 Mathematical argument and interpretation limits
proof.pdf                 Compiled two-page report
lean/Conjecture209.lean    Full proof; imports only Init
lean/lean-toolchain        Pinned Lean 4.19.0
lean/lakefile.toml         Default target builds the proof module
lean/lake-manifest.json    Empty third-party dependency list
verification.txt          Captured actual build and axiom-audit output
verify.sh                 Reproduce the checks with Lean and pdfLaTeX installed

REPRODUCE

Install the version specified in lean/lean-toolchain, then run:

    sh verify.sh

Alternatively, from lean/:

    lake build
    lake env lean -DwarningAsError=true Conjecture209.lean

From this directory, compile the report twice:

    pdflatex -interaction=nonstopmode -halt-on-error proof.tex
    pdflatex -interaction=nonstopmode -halt-on-error proof.tex

The main theorems' printed dependencies are only propext and Quot.sound,
standard Lean foundational axioms. There are no additional axioms or
proof placeholders, and no native_decide. Ordinary decide and omega produce
proof terms checked by the Lean kernel.

FORMALIZATION

The indexing is zero-based. IsPower a N k means k > 0 and there is m > 0
with N = m*k, such that a(j*m+i) = a(i) for every j < k and i < m.
This is an actual decomposition into consecutive copies of a nonempty
word, not a Boolean proxy. IsNext states both attainment and maximality.
FollowsRule includes the initial value and every positive-index equation.

The final theorem no_rule_solution_contains_five negates the existence of
any sequence satisfying this rule together with any index at which it is 5.
The theorem counterexample supplies a solution to establish nonvacuity.

SOURCE

Official base commit: 1e3f7c25616e84b611350a412febceabad75b56a
Problem: https://github.com/The-Last-Math-Competition/The-Last-Math-Competition/blob/1e3f7c25616e84b611350a412febceabad75b56a/conjectures/00000000209.md
Standard sequence: https://cs.uwaterloo.ca/journals/JIS/VOL10/Sloane/sloane55.html

Prepared for zbw123456 with AI assistance. Only this personal submission
directory is proposed for the repository; no problem, metadata, leaderboard,
review directory, or repository-wide README changes are included.
