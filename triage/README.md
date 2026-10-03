# Disproof targeting — how the three disproof submissions were found

Rule 5 asks the organizers to adjust the generator strategy based on

> the existing conjectures, the evaluations of them, and the successful
> proofs or disproofs.

This directory is the input to that loop from the contributor side: a ranking of
which conjectures are cheapest to *refute*, plus an honest account of how well
that ranking actually worked. It is the targeting pass that produced the three
disproof submissions in PRs #1, #2 and #3.

**This PR adds files only. `metadata.csv` is not modified.**

## Contents

| file | what it is |
|---|---|
| `triage.md` | the ranked shortlist — the 45 most attackable conjectures out of 1,238 candidates, each with its full text |
| `triage.py` | the ranking model (readable, ~100 lines) |
| `campaign_report.md` | the campaign ledger: all six adjudications in detail, the two cross-cutting findings, and the delivery ledger |
| `target_quick.py` | reproduces verdicts A, B, D (standard library only) |
| `target_ef.py` | reproduces verdicts E, F (needs numpy) |
| `zerodivisor.py` | reproduces verdict C — exact χ/ω for n ≤ 1000 |
| `validate_zd.py` | validates the reduction behind C against brute force (run this first) |

## The pipeline

```
10,000 conjectures
   │  scoring pass (see ../scoring/)  →  disproof_difficulty for every row
   ▼
1,238 conjectures with disproof_difficulty ≤ 2   (12.4%)
   │  triage.py ranks them by how cheaply a counterexample could be produced
   ▼
45 read in full, by hand
   │  a machine can tell you a statement is finite and numeric;
   │  it cannot tell you whether the claim is actually refutable
   ▼
6 adjudicated
   │
   ▼
3 packaged as rule-3 submissions        (PRs #1, #2, #3)
```

The ranking model is in `triage.py` and is deliberately simple:

```
+ (5 - disproof_difficulty) × 2.0   the main driver
+ 1.5   contains an explicit numeric bound
+ 1.5   finite / specific object
+ 1.0   topic is number theory / combinatorics / probability
+ 1.0   has ≥3 numeric parameters
+ 0.5   existential claim (refutable by exhaustion)
+ 0.5   short statement (less ambiguous, cheaper to formalise)
- 1.5   asymptotic / density claim (a single counterexample cannot refute it)
```

## The yield, stated plainly

Of the 45 conjectures read in full, **3 were refuted and packaged** — a
conversion rate of **3/45 ≈ 6.7%** of the shortlist, or 3/1,238 ≈ 0.24% of the
candidate pool. Two more turned out to be **ill-posed** (they have no truth
value) and one was **confirmed**.

That is the number a maintainer should use to decide whether this method is
worth repeating. It is not a high yield — but the three that landed are cheap:
each is a short argument plus a small formalisation, and one of them
(`00000001668`) refutes 89 of its own 96 test cases in a single stroke.

## The finding that matters most: rank #3 was *true*

The model put `00000002222` (χ = ω for the zero-divisor graph Γ(ℤₙ), n ≤ 1000)
at **position 3 of 45**. It is **not** false. It is true, and it is now the one
conjecture in the batch that has been *confirmed*.

This is not a bug to be fixed — it is the hard limit of the method, and it is
the single most useful thing this directory has to say:

> **"finite and computationally checkable" is not the same as "refutable".**

A ranking model built from text features can detect the first property. It has
no access to the second, because the second is a mathematical fact about the
statement, not a syntactic one. Every entry in `triage.md` therefore carries a
hidden, unknown prior on "is this even false", and the human reading pass is not
optional. **`triage.py` is a sorting tool, not a decision procedure.**

Two further cautions follow from the same episode:

1. **The head of the list is contaminated by known results.** §4 of
   `campaign_report.md` documents five of the top-45 entries that restate
   settled mathematics — the Hadamard matrix classification of orders 12/16/24
   (correct, and known since the 1960s), the Golomb–Welch conjecture (proved
   2023), the Borsuk counterexample dimension, the almost Mathieu spectral
   dimension, and the Hadamard conjecture itself. The automatic scoring gave all
   of them `novelty = 3`; they should be `novelty = 1`. No text-based model can
   catch this, because **0 of the 10,000 conjectures contain any literature
   reference at all**.
2. **A refutation is only as good as the reading of the statement.** These
   conjectures are often loosely worded. Every verdict in the campaign report
   records the exact interpretation it used; if the maintainer intended a
   different reading, the verdict must be revised.

## The ranking consumes the rule-2 scores, and inherits their gap

The ranking is driven by `disproof_difficulty` — one of the five columns filled
by the scoring pass in `../scoring/`. So the quality of this shortlist is bounded
by the quality of that column.

The corpus-wide numbers are worth stating because they invert the obvious
intuition about which direction is easier:

| column | median |
|---|---|
| `proof_difficulty` | **2** |
| `disproof_difficulty` | **4** |

**Disproving is, on this corpus, harder than proving.** The reason is concrete:
most of the 10,000 conjectures are asymptotic or density claims ("the density
equals…", "the error term is O(…)"), and *no single counterexample can refute an
asymptotic claim*. Only 1,238 of 10,000 (12.4%) fall at `disproof_difficulty ≤ 2`,
and that 12.4% is the entire usable surface for this method.

This is why the strategy here is **not** "disproof is the cheap path". It is
"find the small minority where disproof is cheap, and accept that the search for
them is expensive."

## Reproduction

`triage.md` reproduces byte-for-byte from the ranking script:

```bash
# 1. produce the feature pass and the scored table (see ../scoring/)
# 2. rank
python3 triage.py --top 45 --out triage.md \
    --features features_all.jsonl \
    --metadata metadata.scored.csv \
    --conjectures conjectures
# -> candidates with dp<=2: 1238
# -> wrote top 45 -> triage.md
```

The verdict scripts are self-contained and run from this directory:

```bash
python3 target_quick.py   # A, B, D  — standard library only
python3 validate_zd.py    # checks the reduction behind C against brute force
python3 zerodivisor.py    # C        — exact χ/ω for every composite n ≤ 1000
python3 target_ef.py      # E, F     — needs numpy
```

`validate_zd.py` is a **precondition**, not a nicety: it compares the twin-class
reduction against a direct brute-force computation of ω and χ on the real graph
for n ∈ [4, 120]. If it ever reports a mismatch, verdict C is void.

Dependency note: `triage.py` needs `metadata.scored.csv`, which is produced by
the scoring pass in `../scoring/` (PR #5). If that PR is not merged, the ranking
cannot be re-run as-is; the script's defaults are repository-relative so it will
work once both are in place.

## What is *not* here

- **`00000002222` is not packaged as a submission.** Its verdict is solid
  (verified by exhaustive exact computation over all 831 composite n ≤ 1000,
  0 counterexamples, reduction validated against brute force), but it has no
  short path to a complete proof: ω has no closed form, so a submission would
  need the 831-case computation plus a formalisation — expensive, and the payoff
  is confirming a conjecture that was already true. The verdict, the reduction,
  the validation, and the literature context are all in
  `campaign_report.md` §3.3 and §8. **Say the word if you want it packaged.**
- **The two ill-posed verdicts (`00000001016`, `00000001619`) are not
  submitted** either — there is no proposition to formalise. How to record them
  is a rules question, raised separately as an issue.

## Where this should live, and questions

Rule 5 assigns the strategy adjustment to the organizers; rule 3 specifies where
*solutions* go but says nothing about targeting documents. So, as with the
scoring pass, **the location is your call** — I have put this in a new top-level
`triage/` directory and touched nothing else.

1. Is `triage/` the right place for this, or would you rather it live elsewhere
   (or not be tracked in the repository at all)?
2. Is the 3/45 yield high enough to be worth the human reading pass? If not, the
   honest conclusion is that this ranking is not a useful generator input, and I
   would rather say so than oversell it.
3. Should the ranking weight `well_definedness_level` more heavily? Two of the
   six adjudications were ill-posed statements, which suggests the ranking is
   spending effort on conjectures that cannot have a truth value at all.
4. `campaign_report.md` is in Chinese (matching the conjecture files' second
   language). Would you prefer English?
