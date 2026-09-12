#!/usr/bin/env python3
"""
Disproof triage.

Ranks conjectures by how cheaply a *counterexample* could be produced, which is
a different question from how hard they are to prove. The ranking is then
manually curated: a machine can tell you which statements are finite and
numeric, it cannot tell you whether a claim is actually refutable.

Usage:
  python3 triage.py --top 45 --out triage.md

Inputs (all relative by default, so this runs from a checkout of the
repository once the feature pass has been produced by ../scoring/):

  --features    features_all.jsonl    per-conjecture features (scoring/extract_features.py)
  --metadata    metadata.scored.csv   the scored table (scoring/score_conjectures.py)
  --conjectures conjectures           the conjecture markdown files
"""
import argparse
import csv
import json
import os

# Topics where counterexamples are most often reachable by brute force.
TRACTABLE_TOPICS = {"number theory", "combinatorics / discrete", "probability"}


def tractability(f, r):
    """Higher = cheaper to attack computationally."""
    s = 0.0
    dp = int(r["disproof_difficulty"])
    s += (5 - dp) * 2.0                 # low disproof difficulty is the main driver
    if f["has_bound"]:
        s += 1.5                        # explicit numeric bound => falsifiable
    if f["has_finite_obj"]:
        s += 1.5                        # finite/specific object => searchable
    if f["topic"] in TRACTABLE_TOPICS:
        s += 1.0
    if f["n_numbers"] >= 3:
        s += 1.0                        # concrete parameters
    if f["has_exists"]:
        s += 0.5                        # existential: refute by exhaustion
    if f["chars"] <= 450:
        s += 0.5                        # short => unambiguous => formalizable
    if f["has_meta"]:
        s += 0.5                        # self-declared known => likely already settled
    if f["has_asymptotic"]:
        s -= 1.5                        # density/error-term claims resist counterexamples
    if f["has_forall"] and f["has_asymptotic"]:
        s -= 1.0
    return s


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--top", type=int, default=45)
    ap.add_argument("--out", default="triage.md")
    ap.add_argument("--features", default="features_all.jsonl",
                    help="per-conjecture features (jsonl)")
    ap.add_argument("--metadata", default="metadata.scored.csv",
                    help="scored metadata table")
    ap.add_argument("--conjectures", default="conjectures",
                    help="directory of conjecture markdown files")
    a = ap.parse_args()

    rows = {r["id"]: r for r in csv.DictReader(
        open(a.metadata, encoding="utf-8"))}
    feats = [json.loads(l) for l in open(a.features, encoding="utf-8")]

    ranked = []
    for f in feats:
        r = rows[f["id"]]
        if int(r["disproof_difficulty"]) > 2:
            continue
        ranked.append((tractability(f, r), f, r))
    ranked.sort(key=lambda x: -x[0])

    lines = ["# 反证目标 triage\n",
             f"共 {len(ranked)} 条 `disproof_difficulty ≤ 2` 的候选，按可攻击性排序，取前 {a.top} 条。\n"]
    for i, (s, f, r) in enumerate(ranked[:a.top], 1):
        cid = f["id"]
        text = open(os.path.join(a.conjectures, cid + ".md"), encoding="utf-8").read()
        en = text.split("**中文。")[0].strip()
        en = " ".join(en.split())
        en = en.replace(f"# {cid}", "").replace("**English.**", "").strip()
        lines.append(
            f"**{i}. `{cid}`** score={s:.1f} | dp={r['disproof_difficulty']} "
            f"pr={r['proof_difficulty']} imp={r['importance']} wd={r['well_definedness_level']} "
            f"| topic={f['topic']} | bound={f['has_bound']} fin={f['has_finite_obj']} "
            f"exists={f['has_exists']} nums={f['n_numbers']}\n\n> {en}\n")

    open(a.out, "w", encoding="utf-8").write("\n".join(lines) + "\n")
    print(f"candidates with dp<=2: {len(ranked)}")
    print(f"wrote top {a.top} -> {a.out}")


if __name__ == "__main__":
    main()
