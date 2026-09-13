#!/usr/bin/env python3
"""Reproduce the disproof of conjecture 00000008848.

    Definition: fixed points of order-preserving maps.
    Conjecture: minimal and maximal fixed points of order-preserving maps
    always exist; and monotone iterations of the sub/supersolution method
    approximate them in countably many steps.

The conjecture is FALSE.  The file specifies no poset (no "complete lattice",
no boundedness) and states no sub/supersolution hypothesis for the first
clause, so its first clause ranges over all order-preserving self-maps of
ordered sets.  This script checks the three independent failures:

  [1] Clause (a), shift witness.  f(x) = x + 1 on Z is order-preserving and
      has NO fixed point at all: f(x) = x would force x + 1 = x, i.e. 1 = 0.

  [2] Clause (a), non-vacuous witness.  id on Z is order-preserving, every
      point is fixed, yet the fixed-point set Z has no least and no greatest
      element: for any claimed least m, the point m - 1 is fixed and m <= m - 1
      fails; for any claimed greatest M, the point M + 1 is fixed and
      M + 1 <= M fails.  The contradiction is reported for each candidate.

  [3] Clause (b), complete-lattice witness.  On the complete lattice
      omega_1 + 1 with g(alpha) = alpha + 1 for alpha < omega_1 and
      g(omega_1) = omega_1, the map g is order-preserving with the single
      fixed point omega_1, and the monotone iteration from the subsolution 0
      satisfies u_alpha = alpha, so it first reaches omega_1 at stage
      omega_1 -- UNCOUNTABLY many steps.  The script SIMULATES the first
      finitely many stages (showing u_n = n, never converged), and then
      records the standard transfinite argument for all countable alpha and
      the limit stage.  The finite simulation is a computation; the general
      statement is an ARGUMENT, clearly labelled as such, not a computation
      of an uncountable object.

Standard library only.  Python 3.8+.  Exits non-zero if any check fails.

Honest caveat.  Because the file specifies no poset, a charitable reading that
adds "complete lattice" makes clause (a) the Knaster-Tarski theorem (true) and
puts the Z witnesses out of scope; under that reading the disproof of the
conjunction rests on clause (b).  See README.md and lean4/README.md.
"""

import sys

# ----------------------------------------------------------------------------
# Sentinels and order helpers (exact integer order on Z)
# ----------------------------------------------------------------------------

# omega_1 is the first uncountable ordinal; it is not representable as a Python
# int and is never computed here.  The sentinel below stands for it in the
# *labelled argument* block only.
OMEGA_1 = "omega_1"
OMEGA = "omega"            # first infinite ordinal, used only in the argument


def shift(x):
    """The shift map f(x) = x + 1 on Z (and g(alpha) = alpha + 1 for alpha < omega_1)."""
    if x == OMEGA_1:
        return OMEGA_1        # g(omega_1) = omega_1
    return x + 1


def identity(x):
    """The identity map id on Z."""
    return x


def check(name, ok, detail):
    """Record and print a single check; return the boolean."""
    mark = "ok  " if ok else "FAIL"
    print(f"    [{mark}] {name}")
    print(f"           {detail}")
    return bool(ok)


def main():
    all_ok = True
    line = "=" * 72

    print(line)
    print("Disproof of conjecture 00000008848 -- reproduction")
    print(line)

    # ======================================================================
    # [1] Clause (a), shift witness: f(x) = x + 1 on Z has no fixed point.
    # ======================================================================
    print("\n[1] Clause (a), shift witness: f(x) = x + 1 on Z has no fixed point.")

    # 1a. Algebraic fact: x + 1 = x  <=>  1 = 0, impossible.
    all_ok &= check(
        "f(x) = x + 1 satisfies f(x) = x  <=>  1 = 0, hence never",
        (1 != 0),
        "f(x) = x  <=>  x + 1 = x  <=>  1 = 0, and 1 != 0 in Z",
    )

    # 1b. Finite simulation over a large window: f(x) != x for all tested x.
    LO, HI = -100000, 100000
    bad = [x for x in range(LO, HI + 1) if shift(x) == x]
    all_ok &= check(
        f"finite window check: f(x) != x for all x in [{LO}, {HI}]",
        not bad,
        f"offending x: {bad[:5]}" if bad else
        f"checked {HI - LO + 1} integers, no fixed point",
    )

    # 1c. Monotonicity: a <= b  =>  f(a) <= f(b), checked on a sample and by
    #     the exact algebraic identity f(b) - f(a) = b - a.
    mono_ok = all(shift(a) <= shift(b)
                  for a in range(-200, 201) for b in range(a, 201))
    all_ok &= check(
        "f is order-preserving on the sampled range (shift is monotone)",
        mono_ok,
        "checked all pairs -200 <= a <= b <= 200; algebraically f(b)-f(a) = b-a >= 0",
    )

    all_ok &= check(
        "conclusion [1]: no fixed point, hence no least/maximal fixed point of f",
        not bad and (1 != 0),
        "clause (a) fails already for the order-preserving map f on Z",
    )

    # ======================================================================
    # [2] Clause (a), non-vacuous witness: id on Z.
    # ======================================================================
    print("\n[2] Clause (a), non-vacuous witness: id on Z, every point fixed, no extremum.")

    # 2a. Every point is fixed.
    bad_id = [x for x in range(LO, HI + 1) if identity(x) != x]
    all_ok &= check(
        f"every point of Z is fixed by id on [{LO}, {HI}]",
        not bad_id,
        f"offending x: {bad_id[:5]}" if bad_id else "id(y) = y for every tested y",
    )

    # 2b. No least fixed point: for each claimed least m, exhibit m - 1.
    candidates = [-3, -1, 0, 1, 2, 7, 100, 10 ** 18]
    contradictions_least = []
    for m in candidates:
        y = m - 1
        is_fixed = (identity(y) == y)      # always True
        fails_min = not (m <= y)           # m <= m - 1 is False
        contradictions_least.append((m, y, is_fixed and fails_min))
    all_ok &= check(
        "no least fixed point of id: each claimed m is contradicted by m - 1",
        all(c for (_, _, c) in contradictions_least),
        "; ".join(
            f"m={m}: y={y} fixed and y<m, so not(m<=y)"
            for (m, y, _) in contradictions_least[:4]
        ) + " ... (all candidates contradicted)",
    )

    # 2c. No greatest fixed point: for each claimed greatest M, exhibit M + 1.
    contradictions_greatest = []
    for M in candidates:
        y = M + 1
        is_fixed = (identity(y) == y)
        fails_max = not (y <= M)           # M + 1 <= M is False
        contradictions_greatest.append((M, y, is_fixed and fails_max))
    all_ok &= check(
        "no greatest fixed point of id: each claimed M is contradicted by M + 1",
        all(c for (_, _, c) in contradictions_greatest),
        "; ".join(
            f"M={M}: y={y} fixed and M<y, so not(y<=M)"
            for (M, y, _) in contradictions_greatest[:4]
        ) + " ... (all candidates contradicted)",
    )

    # 2d. The contradiction, stated for an arbitrary claimed m (symbolic).
    #     This is the actual proof, not a finite sample: from "m is least" we
    #     instantiate minimality at y = m - 1, which is fixed, to get m <= m-1;
    #     adding 1 to both sides gives m + 1 <= m, and subtracting m gives
    #     1 <= 0, a contradiction.
    all_ok &= check(
        "argument (2d): arbitrary m  =>  m <= m - 1  =>  1 <= 0, contradiction",
        (1 <= 0) is False,
        "m least => (m-1 fixed) => m <= m-1 => (add 1) m+1 <= m => 1 <= 0: false",
    )

    all_ok &= check(
        "conclusion [2]: id has fixed points but neither a least nor a greatest one",
        not bad_id
        and all(c for (_, _, c) in contradictions_least)
        and all(c for (_, _, c) in contradictions_greatest),
        "clause (a) fails non-vacuously: even assuming a fixed point exists",
    )

    # ======================================================================
    # [3] Clause (b): omega_1 + 1 needs uncountably many iteration steps.
    # ======================================================================
    print("\n[3] Clause (b): omega_1 + 1, the map g, and the monotone iteration.")

    # 3a. COMPUTATION (finite): simulate the first finitely many stages from the
    #     subsolution 0.  All stages are finite ordinals < omega_1, so on them
    #     g(alpha) = alpha + 1 and g(0) = 1 >= 0 makes 0 a subsolution.
    STAGES = 50
    u = 0
    trace = [u]
    for _ in range(STAGES):
        u = shift(u)
        trace.append(u)
    sim_ok = all(trace[n] == n for n in range(STAGES + 1))
    all_ok &= check(
        f"computation (finite): u_n = n for n = 0..{STAGES} (subsolution 0, g(0)=1>=0)",
        sim_ok,
        f"trace u_0..u_5 = {trace[:6]}, ..., u_{STAGES} = {trace[STAGES]}; "
        "no finite stage is the fixed point omega_1",
    )
    all_ok &= check(
        "computation (finite): at no finite stage n is u_n = omega_1",
        all(trace[n] != OMEGA_1 for n in range(STAGES + 1)),
        "u_n is a finite ordinal n for every simulated n, and omega_1 is infinite; "
        "so the iteration has not converged at any finite stage",
    )

    # 3b. ARGUMENT, not computation: the transfinite induction of the write-up.
    #     Labelled explicitly so that the finite simulation above is not
    #     mistaken for a verification of the uncountable statement.
    argument_lines = [
        "ARGUMENT (transfinite; NOT a computation -- omega_1 is not representable).",
        "  Claim: u_alpha = alpha for every ordinal alpha <= omega_1.",
        "  Proof by transfinite induction on alpha <= omega_1:",
        "    (zero)     u_0 = 0 by definition of the iteration;",
        "    (successor) if u_alpha = alpha < omega_1 then",
        "               u_{alpha+1} = g(u_alpha) = g(alpha) = alpha + 1;",
        "    (limit)    if lambda is a limit ordinal and u_beta = beta for all",
        "               beta < lambda, then u_lambda = sup_{beta<lambda} beta",
        "               = lambda, since the ordinals below lambda are cofinal in it.",
        "  Consequences:",
        "    - for every countable alpha < omega_1, u_alpha = alpha < omega_1:",
        "      the iteration has NOT reached the least fixed point after any",
        "      countable number of steps;",
        "    - u_{omega_1} = omega_1, which is the unique fixed point of g",
        "      (g(alpha) = alpha + 1 > alpha for alpha < omega_1, g(omega_1) = omega_1).",
        "    - first convergence stage = omega_1, the first UNCOUNTABLE ordinal.",
        "  Hence clause (b)'s 'countably many steps' is false on the complete",
        "  lattice omega_1 + 1, without any further hypothesis.",
    ]
    for ln in argument_lines:
        print("    " + ln)

    # 3c. ARGUMENT: continuity failure, why convergence is not at stage omega.
    #     sup_n (n + 1) = omega, while g(omega) = omega + 1 != omega.
    #     (omega and omega + 1 are sentinels used only for this labelled
    #     argument; they are not computed.)
    sup_of_successors = OMEGA            # sup_{n<omega} (n + 1) = omega
    g_of_omega = OMEGA + "+1"            # g(omega) = omega + 1
    all_ok &= check(
        "argument (3c): g is not sup-continuous: g(sup D) != sup g(D) for D = omega",
        sup_of_successors != g_of_omega,
        "sup_{n<omega}(n+1) = omega, but g(omega) = omega + 1 > omega; "
        "this is exactly why u_omega = omega is not yet fixed and why the "
        "iteration continues past stage omega",
    )

    # 3d. The subsolution check for 0 (the starting point used above).
    all_ok &= check(
        "argument (3d): 0 is a subsolution, g(0) = 1 >= 0",
        shift(0) >= 0,
        "g(0) = 1 and 1 >= 0, so the iteration from below from 0 is the standard one",
    )

    all_ok &= check(
        "conclusion [3]: clause (b) fails -- not countably many steps",
        sim_ok and all(trace[n] != OMEGA_1 for n in range(STAGES + 1)),
        "finite simulation shows no finite convergence; the labelled transfinite "
        "argument locates convergence exactly at the uncountable stage omega_1",
    )

    # ======================================================================
    # Report
    # ======================================================================
    print("\n" + line)
    if all_ok:
        print("PASS: all checks verified; conjecture 00000008848 is FALSE.")
        print("  Clause (a): f(x)=x+1 on Z is order-preserving with no fixed point;")
        print("              id on Z has fixed points but no least/greatest fixed point.")
        print("  Clause (b): on the complete lattice omega_1+1, the monotone iteration")
        print("              from 0 reaches the unique fixed point only at stage")
        print("              omega_1 -- uncountably many steps, not countably many.")
        print("  Caveat: no poset is specified; under a charitable complete-lattice")
        print("          reading clause (a) is Knaster-Tarski (true) and the disproof")
        print("          of the conjunction rests on clause (b).")
        print(line)
        return 0
    print("FAIL: at least one check did not verify.")
    print(line)
    return 1


if __name__ == "__main__":
    sys.exit(main())
