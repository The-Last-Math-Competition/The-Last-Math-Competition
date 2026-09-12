# Scoring of all 10,000 conjectures — rule 2

Rule 2 asks that the conjectures be scored jointly by humans and AI agents:

> Humans and AI Agents will jointly score all existing conjectures across
> different dimensions, estimating the difficulty of proving or disproving them,
> and evaluating the conjectures' importance.

As of this PR, the five score columns of `metadata.csv` are empty for all 10,000
rows — 0 of 50,000 cells filled. This directory contains a complete, reproducible
pass over the whole corpus.

**This PR adds files only. `metadata.csv` is not modified.** See
"Where these numbers should live" below.

## Contents

| file | what it is |
|---|---|
| `metadata.scored.csv` | the scored table — schema and row order byte-identical to `metadata.csv`; the 5 score columns filled for all 10,000 rows, every other column untouched |
| `rubric.md` | the rubric: what each dimension means, its scale, the scoring rules, and the calibration report *(in Chinese)* |
| `scoring_report.md` | distributions per dimension, confidence bands, topic breakdown *(in Chinese)* |
| `review_queue.csv` | all 10,000 rows with the confidence band and the structural flags behind each score, sorted least-confident first — this is the actionable artefact |
| `calibration_sample.md` | a stratified sample of scored conjectures with their features, for spot-checking by hand *(in Chinese)* |
| `extract_features.py` | stage 1 — deterministic feature extraction |
| `score_conjectures.py` | stage 2 — the scoring model |

## How to reproduce

Pure Python 3, standard library only. No network, no LLM calls, no dependencies.

```bash
# stage 1: features (the pipeline was run in 4 chunks of 2500)
python3 extract_features.py --start 1 --count 2500 \
    --conjectures conjectures --out feats_0.jsonl --freq freq_0.json
#   ... repeat with --start 2501, 5001, 7501 ...

cat feats_0.jsonl feats_1.jsonl feats_2.jsonl feats_3.jsonl > features_all.jsonl

# stage 2: scoring
python3 score_conjectures.py --features features_all.jsonl \
    --metadata metadata.csv --outdir out
```

`--conjectures` defaults to `conjectures` and `--metadata` to `metadata.csv`, so
the commands run from a checkout of this repository with no editing.

**Verified end to end.** The pipeline was re-run from a clean checkout of this
repository — all four chunks, then the scoring stage — and its output compared
cell by cell against `metadata.scored.csv`: **0 differences across all 10 columns
× 10,000 rows.** The confidence bands reproduce exactly too (high 8972 / medium
1001 / low 27). Nothing in this directory was produced by a step that cannot be
re-run from the repository alone.

Rows with no extracted features are left **blank** rather than filled with a
default — the scorer does not invent a value for a conjecture it did not read.
That is also why a partial run is safe to inspect: the first 400 rows of a
400-row run are identical to the first 400 rows of the full run.

## Results

| dimension | 1 | 2 | 3 | 4 | 5 | median |
|---|---|---|---|---|---|---|
| `well_definedness_level` | 192 | 853 | 6948 | 930 | 1070 | 3 |
| `importance` | 99 | 6001 | 2936 | 881 | 83 | 2 |
| `novelty` | 166 | 1041 | 8793 | — | — | 3 |
| `proof_difficulty` | 304 | 7395 | 1875 | 364 | 62 | 2 |
| `disproof_difficulty` | 145 | 1093 | 2470 | 5019 | 1273 | 4 |

`well_definedness_level` also has **7 rows scored 0**, the scorer's flag for
possibly ill-posed statements.

The two difficulty columns are independent, and they disagree in a way that
matters for triage: the median `proof_difficulty` is **2** while the median
`disproof_difficulty` is **4**. Proving is, on this corpus, the easier of the two
— because most conjectures are asymptotic or density claims, which no single
counterexample can refute. A "disprove-first" strategy that ignores this will
spend its budget on targets where success is structurally impossible.

## Confidence and the review queue

Every score carries a confidence value, banded `high` / `medium` / `low`
(89.7% / 10.0% / 0.3% of rows). `review_queue.csv` sorts by ascending confidence
and carries the flags behind each score (`meta`, `no_def`, `vague_x3`,
`bare_latex`, `no_quant`, `short`, …), so a human reviewer can work the weakest
10% first instead of re-reading all 10,000.

## Limitations — please read before using these numbers

This is a **structural heuristic** scorer. It reads signals in the text, not
mathematics. Three limits are load-bearing:

**1. `novelty` is not usable as a novelty signal, and I recommend not merging it
as one.** 8,793 of 10,000 rows (87.9%) receive the same value, 3. The reason is
structural, not a bug in the model: **no conjecture in the corpus carries any
literature reference**, so no text-based method can determine whether a statement
has already been settled. It fails on cases I checked by hand:

| id | statement | reality | scored |
|---|---|---|---|
| `00000001093` | Hadamard matrix classes: 1 of order 12, 5 of order 16, 60 of order 24 | **correct and known** — classified in the 1960s | `novelty = 3` |
| `00000001034` | no nontrivial perfect Lee code for n ≥ 4 | **Golomb–Welch, proved 2023** | `novelty = 3` |
| `00000001602` | Hausdorff dimension of the critical almost Mathieu spectrum is 1/2 | **known theorem (Avila)** | `novelty = 3` |
| `00000000242` | Borsuk counterexample dimension ≤ 65 | Borsuk's conjecture **refuted 1993** (Kahn–Kalai) | `novelty = 3` |

Note that these are also the conjectures a text-based triage ranks as *most
attractive targets* — easy to state, finite, bounded — so the failure is
concentrated exactly where a generator-tuning signal would be read. My
suggestion: split the column into `novelty_lower_bound` (a value supported by
evidence, so `null` when there is none) and `literature_checked` (a boolean). A
single column that is 87.9% one value cannot be used for tuning, and a column
that says `3` for a 1960s classification is worse than an empty one. If you
prefer, I will re-send with this column left empty.

**2. The `well_definedness_level` scale is my assumption.** The column was empty
and no scale is published anywhere in the repository. I used an integer 0–5
(0 = the object does not exist or the description is self-contradictory; 5 = all
of: terms defined, quantifiers scoped, no vague wording, notation consistent).
If the intended scale is different, this column has to be re-derived; the other
four are far less sensitive to the convention. I would rather be told than
guess — this is question 4 of #4.

**3. The 7 rows scored 0 are a flag, not a verdict.** They are the scorer's
suspicion that the object discussed does not exist. I confirmed 2 of that kind by
hand (`00000001016`, `00000001619`, see #4) and the question of how to *record*
them is open. The other 5 need a human.

**What the method cannot do at all:** decide whether a conjecture is true. It
cannot see mathematics, only how mathematics is written down. It should be used
to *allocate review attention*, never as a verdict.

## Where these numbers should live

I have deliberately not touched `metadata.csv`, for two reasons: rule 4 says the
organizers maintain that table, so folding these values into it is your call; and
a 10,000-row diff against a file you may regenerate is not a good thing to force
through review.

If you would rather have them applied directly, say so and I will send the diff
— it is mechanical and clean: exactly the 5 score columns, all 10,000 rows, and
**0 changes** to `id`, `proven`, `disproven`, `first_submission_time` and
`completed_by_ai`. I have verified that.

## Questions

1. Is `scoring/` the right location, or would you prefer the values applied to
   `metadata.csv` directly (see above), or a different path?
2. Is the 0–5 scale right for `well_definedness_level`? (Also asked in #4.)
3. How should a contribution be attributed? Rule 4's table records "the name and
   affiliation of the successful solver", and there is no stated convention for
   how a submitter supplies that — the directory naming in rule 3 uses a
   timestamp, which carries no identity. Happy to follow whatever you specify.
4. Would you like `rubric.md`, `scoring_report.md` and `calibration_sample.md`
   translated to English? They are currently in Chinese because that is how they
   were drafted.

## Related

PRs #1, #2 and #3 are rule-3 submissions (complete proofs/disproofs of
`00000001243`, `00000008540`, `00000001668`). This PR is the rule-2 work and is
independent of them.
