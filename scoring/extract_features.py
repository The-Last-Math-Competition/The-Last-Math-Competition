#!/usr/bin/env python3
"""
Stage 1: feature extraction for The Last Math Competition scoring pipeline.

Reads a slice of conjectures/*.md and emits one JSON object per conjecture to
JSONL. Deliberately split from scoring so the expensive IO pass runs once and
the scoring model can be re-tuned cheaply.

Sandbox note: process at most ~2500 files per invocation.

Usage:
  python3 extract_features.py --start 1 --count 2500 --out features_01.jsonl \
      --freq freq_01.json
"""
import argparse
import collections
import json
import os
import re

# Directory holding the conjecture markdown files. Override with --conjectures.
# Relative by default so the pipeline runs from a checkout of the repository.
CONJ = "conjectures"

# --- lexicons -------------------------------------------------------------

# Grand-challenge anchors: resolving these would be a landmark result.
# NOTE: kept deliberately narrow. "invariant subspace" was removed after
# calibration showed it matched 28 files where it is ordinary vocabulary
# ("the genus of invariant subspaces") rather than the invariant subspace
# problem, producing spurious importance=5.
GRAND = [
    "riemann hypothesis", "riemann zeta", "p vs np", "p ≠ np", "p = np",
    "navier-stokes", "navier–stokes", "hodge conjecture", "birch",
    "swinnerton", "langlands", "goldbach", "twin prime", "collatz",
    "yang-mills", "yang–mills", "abc conjecture", "sato-tate",
    "generalized riemann", "grh", "invariant subspace problem",
    "unique games conjecture", "unique games",
]

# Deep-but-not-grand machinery. Signals research-frontier technique.
# NOTE: entries must not be substrings of one another, or a single word
# double-counts (e.g. "motivic" contains "motiv"). Overlaps are collapsed
# at match time by _distinct().
DEEP = [
    "l-function", "l 函数", "modular form", "galois representation", "étale",
    "etale", "cohomology", "khovanov", "baum-connes", "baum–connes", "novikov",
    "fontaine", "springer", "kac", "del pezzo", "manin", "freiman", "selberg",
    "riesz", "khintchine", "steiner", "mds", "julia", "courant", "beatty",
    "peyre", "brauer", "shimura", "motivic", "p-adic", "p 进", "hecke",
    "maass", "weil", "artin", "mordell", "fermat", "catalan", "ramanujan",
    "partition", "affine lie", "weyl", "unipotent", "nodal", "spectral synthesis",
    "rips", "coarse", "hyperbolic group", "knot", "jones polynomial",
    "szemerédi", "szemeredi", "hales-jewett", "van der waerden", "matroid",
    "expander", "autocorrelation", "eigen", "quiver", "hopf",
    "schatten", "besov", "sobolev", "ergodic", "peacock", "kellerer",
    "bateman", "horn", "schinzel", "bourgain", "green-tao",
    "invariant subspace", "waring-goldbach", "waring–goldbach",
]

TOPICS = {
    "number theory": [
        "prime", "zeta", "riemann", "goldbach", "twin", "modular", "l-function",
        "l 函数", "galois", "class number", "dirichlet", "sieve", "divisor",
        "p-adic", "p 进", "fermat", "mordell", "elliptic curve", "diophantine",
        "quadratic", "discriminant", "selberg", "beatty", "digit", "bateman",
        "artin", "sato", "hecke", "maass", "ramanujan", "partition",
        "multiplicative", "mertens", "liouville", "mobius", "totient",
        "factorial", "bernoulli", "euler", "residue", "congruence", "integer",
        "polynomial", "squarefree", "square-free", "valuation", "arithmetic progression",
    ],
    "algebraic geometry": [
        "scheme", "variety", "del pezzo", "birational", "cohomology", "motive",
        "motivic", "étale", "etale", "hodge", "brauer", "fano", "abelian variety",
        "jacobian", "sheaf", "stack", "rational point", "blow-up", "divisor class",
        "k3 surface", "elliptic surface", "genus", "moduli",
    ],
    "algebra / representation theory": [
        "representation", "lie algebra", "weyl", "root system", "unipotent",
        "springer", "kac", "affine lie", "module", "ideal", "galois group",
        "finite group", "semigroup", "quiver", "hopf", "nilpotent",
        "character theory", "symmetric group", "automorphism", "ring",
    ],
    "topology / geometry": [
        "manifold", "knot", "homology", "homotopy", "fundamental group",
        "riemannian", "curvature", "geodesic", "hyperbolic", "simplicial",
        "bundle", "cobordism", "surgery", "morse", "foliation", "sphere",
        "3-manifold", "nodal domain", "eigenfunction", "laplacian",
    ],
    "combinatorics / discrete": [
        "graph", "ramsey", "szemerédi", "szemeredi", "hypergraph", "set system",
        "steiner", "coding", "mds", "matroid", "coloring", "matching", "poset",
        "extremal", "sumset", "freiman", "additive", "design", "permutation",
        "hypercube", "clique", "independent set", "sperner", "combinatorial",
    ],
    "analysis / PDE / dynamics": [
        "pde", "navier", "stokes", "schrödinger", "schrodinger", "heat equation",
        "wave equation", "harmonic", "sobolev", "spectral", "eigenvalue",
        "fourier", "riesz", "frame", "banach", "hilbert", "measure",
        "integral", "courant", "entropy", "ergodic", "dynamical", "julia",
        "mandelbrot", "operator", "inequality", "convex", "functional",
    ],
    "probability": [
        "random", "probability", "distribution", "gaussian", "brownian",
        "martingale", "coupling", "peacock", "limit theorem", "variance",
        "expectation", "stochastic", "kellerer",
    ],
    "logic / complexity": [
        "p vs np", "computab", "turing", "complexity", "decidab", "zfc",
        "consistency", "model theory", "set theory", "gödel", "godel",
        "proof theory", "circuit", "satisfiability", "np-complete",
    ],
}

VAGUE_CONST = re.compile(
    r"some (?:absolute )?constant|a constant|explicit constant|"
    r"sufficiently large|some universal constant|某个常数|适当大|充分大|某常数",
    re.I,
)
VAGUE_PHRASE = re.compile(r"\bexplicit\b|显式|\boptimal\b|最优", re.I)
# Status meta-commentary leaking into the statement instead of living in
# metadata.csv. The bare 已知 catches Chinese phrasings like 已知结果/已知存在.
META = re.compile(
    r"\(known\)|\(open\)|\(partially known|partly known|is known|are known|"
    r"known result|已知|完全开放|部分开放",
    re.I,
)
BARE_LATEX = re.compile(r"\\[a-zA-Z]{2,}")
DOLLAR_LATEX = re.compile(r"\$[^$\n]+\$")
# Explicit quantifier scope. The 'for <token> <relation>' alternative was added
# after calibration: forms like "For p ≥ 5" and "For |A| > (p−1)/3" are common
# in this corpus and were previously missed, which wrongly tanked
# well_definedness for precise statements.
FORALL = re.compile(
    r"for every|for all|for each|for any|for sufficiently|"
    r"for\s+[^\s,]{1,14}\s*(?:≥|≤|>|<|=|∈)|"
    r"\bevery\b|\ball\b|\bany\b|\bwhenever\b|"
    r"对每个|对一切|对任意|对所有|任意|每个|一切",
    re.I,
)
EXISTS = re.compile(r"there exist|there are infinitely|there is|存在", re.I)
ASYMPTOTIC = re.compile(
    r"asymptot|density|error term|tends to|converges|O\(|o\(|~|"
    r"渐近|密度|误差|趋于|收敛|上界|下界",
    re.I,
)
# Evaluated on the ENGLISH block only. Matching the Chinese translation caused
# false positives: 有限 renders "finitely verifiable" as readily as "finite
# object", which wrongly marked ~9% of the corpus as finitely falsifiable.
FINITE_OBJ = re.compile(
    r"on the isosceles|on the triangle|of length|of order|of genus|"
    r"for n = |for p = |degree-\d|dimension \d|q\+2|2\^\{n|n ≤|"
    r"specific|explicit list|finite (?:list|table|classification)",
    re.I,
)
NUMBER = re.compile(r"\b\d+\b")
# Falsifiable-bound markers: a claim with an explicit numeric bound is far
# cheaper to attack than a qualitative one.
BOUND = re.compile(r"≤|≥|<|>|at most|at least|equals|exactly|exceeds|"
                   r"不超过|不超过|至少|恰好|等于|大于|小于", re.I)
NAMED_THM = re.compile(r"theorem|定理|lemma|lemma|inequality|不等式", re.I)
SEQUENCE = re.compile(r"sequence|序列|enumeration|计数|count of", re.I)
# Variant markers: the statement openly presents itself as a strengthening /
# optimal form / analogue of an existing result. Strong negative novelty signal.
VARIANT = re.compile(
    r"strengthen|optimal form|optimal version|generalization|generalisation|"
    r"analogue|analog of|variant|refinement|sharp form|"
    r"加强|推广|最优形式|最优版本|变体|类比",
    re.I,
)
# Claims over an infinite family are structurally more significant than claims
# about one specific object.
INFINITE_FAMILY = re.compile(r"infinitely many|infinite family|无穷多|无限多|无穷多个", re.I)


def _find_terms(low, terms, boundary=False):
    """boundary=True rejects matches glued to a hyphen/word char, so
    'goldbach' does not fire inside 'waring-goldbach'."""
    found = []
    for t in terms:
        if boundary:
            if re.search(r"(?<![\w\-–])" + re.escape(t) + r"(?![\w])", low):
                found.append(t)
        elif t in low:
            found.append(t)
    return found


def _distinct(found):
    """Collapse overlaps: 'motivic' contains 'motiv', and counting both made a
    single word look like two independent pieces of deep machinery."""
    return [t for t in found if not any(u != t and t in u for u in found)]


def load_slice(start, count, conj_dir=CONJ):
    files = sorted(os.listdir(conj_dir))
    return files[start - 1:start - 1 + count]


def classify_topic(text_low):
    best, best_hits = "general / other", 0
    for topic, keys in TOPICS.items():
        hits = sum(1 for k in keys if k in text_low)
        if hits > best_hits:
            best, best_hits = topic, hits
    return best, best_hits


def features(cid, text):
    low = text.lower()
    parts = text.split("**中文。")
    en_part, zh_part = parts[0], (parts[1] if len(parts) > 1 else "")
    grand = _distinct(_find_terms(low, GRAND, boundary=True))
    deep = _distinct(_find_terms(low, DEEP))
    names = grand + deep
    topic, topic_hits = classify_topic(low)
    f = {
        "id": cid,
        "bytes": len(text.encode("utf-8")),
        "chars": len(text),
        "title_ok": text.startswith(f"# {cid}"),
        "has_def": bool(re.search(r"Definition|定义", text)),
        "has_conj_token": bool(re.search(r"Conjecture|猜想", text)),
        "has_forall": bool(FORALL.search(text)),
        "has_exists": bool(EXISTS.search(text)),
        "has_vague_const": bool(VAGUE_CONST.search(text)),
        "n_vague_phrase": len(VAGUE_PHRASE.findall(text)),
        "has_meta": bool(META.search(text)),
        "has_bare_latex": bool(BARE_LATEX.search(text)),
        "has_dollar_latex": bool(DOLLAR_LATEX.search(text)),
        "has_asymptotic": bool(ASYMPTOTIC.search(text)),
        "has_finite_obj": bool(FINITE_OBJ.search(en_part)),
        "has_bound": bool(BOUND.search(text)),
        "has_named_thm": bool(NAMED_THM.search(text)),
        "has_sequence": bool(SEQUENCE.search(text)),
        "has_variant": bool(VARIANT.search(text)),
        "has_infinite_family": bool(INFINITE_FAMILY.search(text)) or bool(FORALL.search(text)),
        "n_numbers": len(NUMBER.findall(text)),
        "grand": grand,
        "deep": deep,
        "n_names": len(names),
        "topic": topic,
        "topic_hits": topic_hits,
        "en_len": len(en_part),
        "zh_len": len(zh_part),
        "zh_ratio": round(len(zh_part) / max(len(en_part), 1), 3),
        "n_sentences": len(re.findall(r"[.!?;。；]", en_part)),
    }
    return f


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--start", type=int, required=True)
    ap.add_argument("--count", type=int, default=2500)
    ap.add_argument("--conjectures", default=CONJ,
                    help="directory of conjecture markdown files")
    ap.add_argument("--out", required=True)
    ap.add_argument("--freq", required=True)
    a = ap.parse_args()

    files = load_slice(a.start, a.count, a.conjectures)
    term_freq = collections.Counter()
    topic_freq = collections.Counter()
    n = 0
    with open(a.out, "w", encoding="utf-8") as out:
        for fn in files:
            cid = fn[:-3]
            with open(os.path.join(a.conjectures, fn), encoding="utf-8") as fh:
                text = fh.read()
            f = features(cid, text)
            out.write(json.dumps(f, ensure_ascii=False) + "\n")
            topic_freq[f["topic"]] += 1
            for t in f["grand"] + f["deep"]:
                term_freq[t] += 1
            n += 1

    json.dump(
        {"n": n, "topics": topic_freq.most_common(), "terms": term_freq.most_common(200)},
        open(a.freq, "w", encoding="utf-8"),
        ensure_ascii=False,
        indent=1,
    )
    print(f"wrote {n} features to {a.out}")


if __name__ == "__main__":
    main()
