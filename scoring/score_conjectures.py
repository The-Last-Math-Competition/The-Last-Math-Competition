#!/usr/bin/env python3
"""
Stage 2: score every conjecture on the five dimensions required by metadata.csv.

Consumes the feature JSONL produced by extract_features.py so the model can be
re-tuned without re-reading 10,000 files.

Dimensions and their intended semantics are documented in rubric.md. This is a
*structural heuristic* scorer: it is fully reproducible and auditable, but it
reads signals, not mathematics. Every score carries a confidence band and a
review queue is emitted for the items where the model is least trustworthy.

Usage:
  python3 score_conjectures.py --features features_all.jsonl \
      --metadata metadata.csv --outdir out
"""
import argparse
import collections
import csv
import json
import math
import os
import statistics

FIELDS = [
    "id", "well_definedness_level", "importance", "novelty",
    "proof_difficulty", "disproof_difficulty", "proven", "disproven",
    "first_submission_time", "completed_by_ai",
]

CORE_FIELDS = {
    "number theory", "algebraic geometry", "algebra / representation theory",
    "topology / geometry", "analysis / PDE / dynamics",
}


def clamp(x, lo, hi):
    return max(lo, min(hi, x))


def rnd(x):
    """Half-up rounding; Python's round() is banker's rounding and would send
    a score of 0.5 to 0, which collides with the 'degenerate' sentinel."""
    return int(math.floor(x + 0.5))


def score(r):
    """Return (well_definedness, importance, novelty, proof, disproof, conf)."""
    has_def = r["has_def"]
    quant = r["has_forall"] or r["has_exists"]
    chars = r["chars"]
    nv = r["n_vague_phrase"]
    grand = bool(r["grand"])
    n_deep = len(r["deep"])
    asym = r["has_asymptotic"]
    fin = r["has_finite_obj"]
    var = r["has_variant"]
    infam = r["has_infinite_family"]

    # --- well_definedness_level (0-5) -------------------------------------
    # Continuous additive scale. 5 requires defined terms, explicit quantifier
    # scope, enough context and clean notation; each missing precondition costs
    # a fixed amount so the scale stays monotone.
    wd = 2.0
    wd += 0.5 if has_def else -0.5
    wd += 1.5 if quant else 0.0
    wd += 0.5 if chars >= 300 else 0.0
    wd -= 0.5 if chars < 250 else 0.0
    wd -= 1.0 if r["has_vague_const"] else 0.0
    wd -= 0.2 * min(nv, 3)
    wd -= 1.0 if r["has_meta"] else 0.0
    wd -= 1.0 if r["has_bare_latex"] else 0.0
    wd = clamp(rnd(wd), 0, 5)

    # --- importance (1-5) -------------------------------------------------
    imp = 2.0
    if grand:
        imp += 3.0
    elif n_deep >= 2:
        imp += 1.5
    elif n_deep == 1:
        imp += 1.0
    if r["has_forall"] and asym:
        imp += 0.5
    if r["has_named_thm"]:
        imp += 0.5
    if var:
        imp += 0.5
    if infam:
        imp += 0.5
    if r["topic"] == "general / other":
        imp -= 0.5
    if chars < 250:
        imp -= 0.5
    if wd <= 1:
        imp -= 0.5
    imp = clamp(rnd(imp), 1, 5)

    # --- novelty (1-5) ----------------------------------------------------
    # Deliberately conservative and one-sided: 3 means "no evidence of
    # non-novelty found", NOT "verified novel". Without a literature search
    # novelty is not establishable, so only negative evidence moves the score.
    if r["has_meta"]:
        nov = 1
    elif grand or var:
        nov = 2
    else:
        nov = 3

    # --- proof_difficulty (1-5) ------------------------------------------
    pr = 2.0
    if grand:
        pr += 3.0
    elif n_deep >= 2:
        pr += 1.5
    elif n_deep == 1:
        pr += 1.0
    if r["has_forall"] and asym:
        pr += 0.5
    if infam and asym:
        pr += 0.5
    if fin:
        pr -= 1.0
    pr = clamp(rnd(pr), 1, 5)

    # --- disproof_difficulty (1-5) ---------------------------------------
    dp = 3.5
    if fin:
        dp -= 1.5
    if r["has_bound"]:
        dp -= 1.0
    if r["has_exists"]:
        dp -= 0.5
    if r["n_numbers"] >= 3:
        dp -= 0.5
    if asym:
        dp += 1.0
    if r["has_forall"] and asym:
        dp += 0.5
    if grand:
        dp += 0.5
    dp = clamp(rnd(dp), 1, 5)

    # --- confidence -------------------------------------------------------
    conf = 0.85
    if r["has_meta"]:
        conf -= 0.25
    if r["has_bare_latex"]:
        conf -= 0.2
    if chars < 250:
        conf -= 0.15
    if r["topic"] == "general / other":
        conf -= 0.1
    if nv >= 3:
        conf -= 0.15
    if not has_def:
        conf -= 0.1
    conf = round(clamp(conf, 0.05, 0.95), 2)

    return wd, imp, nov, pr, dp, conf


def band(conf):
    return "high" if conf >= 0.75 else ("medium" if conf >= 0.5 else "low")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--features", default="features_all.jsonl")
    ap.add_argument("--metadata", default="metadata.csv")
    ap.add_argument("--outdir", default="out")
    a = ap.parse_args()
    os.makedirs(a.outdir, exist_ok=True)

    feats = [json.loads(l) for l in open(a.features, encoding="utf-8")]
    by_id = {f["id"]: f for f in feats}

    rows = list(csv.DictReader(open(a.metadata, encoding="utf-8")))
    out_rows = []
    review = []
    dist = {k: collections.Counter() for k in
            ["well_definedness_level", "importance", "novelty",
             "proof_difficulty", "disproof_difficulty"]}
    conf_bands = collections.Counter()
    missing = 0

    for r in rows:
        cid = r["id"]
        f = by_id.get(cid)
        if f is None:
            missing += 1
            out_rows.append(r)
            continue
        wd, imp, nov, pr, dp, conf = score(f)
        r["well_definedness_level"] = str(wd)
        r["importance"] = str(imp)
        r["novelty"] = str(nov)
        r["proof_difficulty"] = str(pr)
        r["disproof_difficulty"] = str(dp)
        out_rows.append(r)
        dist["well_definedness_level"][wd] += 1
        dist["importance"][imp] += 1
        dist["novelty"][nov] += 1
        dist["proof_difficulty"][pr] += 1
        dist["disproof_difficulty"][dp] += 1
        b = band(conf)
        conf_bands[b] += 1
        review.append({
            "id": cid, "confidence": conf, "band": b, "topic": f["topic"],
            "wd": wd, "imp": imp, "nov": nov, "pr": pr, "dp": dp,
            "chars": f["chars"],
            "flags": "|".join(x for x, v in [
                ("meta", f["has_meta"]), ("bare_latex", f["has_bare_latex"]),
                ("no_def", not f["has_def"]), ("short", f["chars"] < 250),
                ("vague_x3", f["n_vague_phrase"] >= 3),
                ("grand", bool(f["grand"])), ("no_quant", not (f["has_forall"] or f["has_exists"])),
            ] if v),
        })

    # --- write scored metadata (identical schema + row order) -------------
    scored_path = os.path.join(a.outdir, "metadata.scored.csv")
    with open(scored_path, "w", encoding="utf-8", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=FIELDS)
        w.writeheader()
        w.writerows(out_rows)

    # --- write review queue, lowest confidence first ---------------------
    review.sort(key=lambda x: (x["confidence"], x["id"]))
    rq_path = os.path.join(a.outdir, "review_queue.csv")
    with open(rq_path, "w", encoding="utf-8", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=list(review[0].keys()))
        w.writeheader()
        w.writerows(review)

    # --- report ----------------------------------------------------------
    lines = []
    A = lines.append
    A("# 评分结果报告\n")
    A(f"- 评分条目：{len(out_rows)} 行（其中 {missing} 行缺少特征记录）")
    A(f"- 输出：`{scored_path}`（严格保持原 10 列 schema 与行序）")
    A(f"- 复核队列：`{rq_path}`（按置信度升序）\n")
    A("## 各维度分布\n")
    for k, c in dist.items():
        tot = sum(c.values())
        A(f"### {k}\n")
        A("| 分值 | 条目数 | 占比 |")
        A("|---|---|---|")
        for v in sorted(c):
            A(f"| {v} | {c[v]} | {100*c[v]/tot:.1f}% |")
        vals = sorted(c.elements())
        A(f"\n中位数 **{statistics.median(vals)}**，均值 **{statistics.mean(vals):.2f}**\n")
    A("## 置信度分布\n")
    A("| 置信带 | 条目数 | 占比 |")
    A("|---|---|---|")
    for b in ("high", "medium", "low"):
        A(f"| {b} | {conf_bands[b]} | {100*conf_bands[b]/len(out_rows):.1f}% |")
    A(f"\n## 主题分布\n")
    tc = collections.Counter(f["topic"] for f in feats)
    A("| 主题 | 条目数 | 占比 |")
    A("|---|---|---|")
    for t, c in tc.most_common():
        A(f"| {t} | {c} | {100*c/len(feats):.1f}% |")
    open(os.path.join(a.outdir, "scoring_report.md"), "w", encoding="utf-8").write(
        "\n".join(lines) + "\n")

    print(f"scored {len(out_rows)} rows -> {scored_path}")
    print(f"review queue: {len(review)} rows -> {rq_path}")
    print("confidence bands:", dict(conf_bands))


if __name__ == "__main__":
    main()
