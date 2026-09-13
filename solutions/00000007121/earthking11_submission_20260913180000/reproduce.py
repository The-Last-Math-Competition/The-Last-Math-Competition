#!/usr/bin/env python3
"""
Reproducer / checker for conjecture 00000007121 (earthking11 submission).

WHAT THIS SCRIPT DOES
---------------------
1. Quotes the catalogue statement.
2. Checks the Santos (2012) arithmetic: a 43-dimensional polytope with
   86 facets has Hirsch bound 86 - 43 = 43, and its diameter is 44 > 43.
3. Prints the *logical* analysis of the two conjuncts of the statement as
   written, showing that the second conjunct is exactly the negation of the
   first (over Nat) and that they therefore cannot both hold.

WHAT THIS SCRIPT DOES **NOT** DO
--------------------------------
It does NOT reproduce, verify, or construct Santos's polytope. The existence
of a 43-dimensional polytope with 86 facets and diameter 44 is a published
literature result (Santos, Annals of Mathematics 176 (2012), 383-412) and is
taken as given here. Only the arithmetic 86 - 43 = 43 < 44 is checked.

Stdlib only. Prints PASS/FAIL. Always exits 0.
"""

STATEMENT_EN = (
    "Conjecture: The Hirsch conjecture's diameter upper bound of face count "
    "minus dimension holds, and the counterexample to the bound is the "
    "high-dimensional double configuration. "
    "(high-dimensional counterexample to the Hirsch bound)"
)

# --- Santos 2012 arithmetic ------------------------------------------------
SANTOS_DIM = 43
SANTOS_FACETS = 86
SANTOS_DIAM = 44

# --- finite model of the pure logic ----------------------------------------
# A small carrier used to *illustrate* the quantifier duality. It is not a
# model of polytopes; it only witnesses the arithmetic skeleton.
TRIPLES = [
    (d, f, diam)
    for d in range(0, 6)
    for f in range(0, 6)
    for diam in range(0, 6)
]

results = []


def check(name, ok, detail=""):
    results.append((name, ok))
    tag = "PASS" if ok else "FAIL"
    print(f"[{tag}] {name}" + (f" -- {detail}" if detail else ""))


def main():
    print("=" * 72)
    print("Conjecture 00000007121 -- rule-3 disproof reproducer")
    print("=" * 72)
    print()

    print("Catalogue statement (English):")
    print(f"  {STATEMENT_EN}")
    print()

    # 1. Santos arithmetic ---------------------------------------------------
    print("-" * 72)
    print("1. Santos (2012) arithmetic")
    print("-" * 72)
    bound = SANTOS_FACETS - SANTOS_DIM
    check(
        "Hirsch bound for the Santos object = facets - dimension",
        bound == 43,
        f"{SANTOS_FACETS} - {SANTOS_DIM} = {bound}",
    )
    check(
        "Santos diameter strictly exceeds the bound",
        SANTOS_DIAM > bound,
        f"{SANTOS_DIAM} > {bound}",
    )
    check(
        "Santos object disproves the Hirsch bound",
        SANTOS_FACETS - SANTOS_DIM < SANTOS_DIAM,
        f"{SANTOS_FACETS} - {SANTOS_DIM} < {SANTOS_DIAM}",
    )
    print("  NOTE: the polytope itself is NOT reproduced here; this is only")
    print("        the published arithmetic of Santos's counterexample.")
    print()

    # 2. Logical analysis of the statement as written ------------------------
    print("-" * 72)
    print("2. Logical analysis of the statement as written")
    print("-" * 72)
    print("  The statement conjoins two claims:")
    print("    (A) the bound HOLDS:   forall d f diam, diam <= f - d")
    print("    (B) a COUNTEREXAMPLE:  exists d f diam, f - d < diam")
    print("  Over Nat, f - d < diam is definitionally NOT (diam <= f - d),")
    print("  hence (B) <=> not (A): the two conjuncts are P and not P.")
    print()

    holds = all(diam <= f - d for (d, f, diam) in TRIPLES)
    exists_ce = any(f - d < diam for (d, f, diam) in TRIPLES)

    check(
        "(A) holds on the finite model",
        holds is False,
        "'forall' is FALSE (e.g. d=0,f=0,diam=1 violates it)",
    )
    check(
        "(B) holds on the finite model",
        exists_ce is True,
        "'exists' is TRUE (witness d=0,f=0,diam=1)",
    )
    check(
        "(B) <=> not (A) on the finite model",
        exists_ce == (not holds),
        "the second conjunct is the negation of the first",
    )
    check(
        "(A) and (B) cannot both be true",
        not (holds and exists_ce),
        "P and not P is unsatisfiable",
    )
    both_at_one_triple = [
        (d, f, diam) for (d, f, diam) in TRIPLES if diam <= f - d and f - d < diam
    ]
    check(
        "no triple satisfies both (A)-at-a-point and (B)-at-a-point",
        len(both_at_one_triple) == 0,
        "diam <= f-d and f-d < diam is unsatisfiable",
    )
    print()

    # 3. Cross-check: (B) entails not-(A) ------------------------------------
    print("-" * 72)
    print("3. Cross-check: a witness to (B) refutes (A)")
    print("-" * 72)
    witnesses = [(d, f, diam) for (d, f, diam) in TRIPLES if f - d < diam]
    if witnesses:
        d, f, diam = witnesses[0]
        implied_not_holds = not all(
            diam2 <= f2 - d2 for (d2, f2, diam2) in TRIPLES
        )
        check(
            "witness forces the universal claim to fail",
            implied_not_holds,
            f"witness (d={d}, f={f}, diam={diam})",
        )
    print()

    # Summary -----------------------------------------------------------------
    print("=" * 72)
    n_fail = sum(1 for _, ok in results if not ok)
    print(f"SUMMARY: {len(results) - n_fail}/{len(results)} checks passed")
    print("Verdict: the statement as written is internally inconsistent;")
    print("independently, the Hirsch bound is false by Santos (2012).")
    print("Santos's construction itself is NOT reproduced by this script.")
    print("DONE" if n_fail == 0 else f"{n_fail} CHECK(S) FAILED")
    print("=" * 72)


if __name__ == "__main__":
    main()
    raise SystemExit(0)
