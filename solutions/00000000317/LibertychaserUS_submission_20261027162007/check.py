import sys
#!/usr/bin/env python
"""Exact integer bookkeeping for the continued fraction of Freiman's constant
F = (2221564096 + 283748*sqrt(462)) / 491993569, and generator of Disproof.lean.

Each Gauss-map state is kept as (p + r*sqrt(462)) / s with integers p, r, s (s > 0).
Step: a = floor(x); p' = p - a*s; 1/(x - a) = s*(p' - r*sqrt462) / (p'^2 - 462 r^2),
then divide numerator/denominator by their gcd g and make the denominator positive.
"""
from fractions import Fraction
from math import gcd, isqrt
import sympy as sp

D = 462
N = 20  # we need a_0..a_20 (21 quotients) to cover both indexing conventions
SQ = sp.sqrt(D)


def floor_state(p, r, s):
    """exact floor of (p + r*sqrt(D))/s using sympy."""
    return int(sp.floor((p + r * SQ) / s))


states = [(2221564096, 283748, 491993569)]
quotients = []
steps = []  # (p, r, s, a, g, P, R, S)
for n in range(N + 1):
    p, r, s = states[-1]
    a = floor_state(p, r, s)
    quotients.append(a)
    pp = p - a * s
    rawP, rawR, rawS = s * pp, -s * r, pp * pp - D * r * r
    assert rawS != 0
    g = gcd(gcd(rawP, rawR), rawS)
    if rawS < 0:
        g = -g
    P, R, S = rawP // g, rawR // g, rawS // g
    assert g * P == rawP and g * R == rawR and g * S == rawS and S > 0
    steps.append((p, r, s, a, g, P, R, S))
    states.append((P, R, S))

print("partial quotients a_0..a_20:", quotients)
print("count of 1 among a_0..a_19:", quotients[:20].count(1))
print("count of 1 among a_1..a_20:", quotients[1:21].count(1))

# cross-check against sympy's continued_fraction_iterator
F = (2221564096 + 283748 * SQ) / 491993569
it = sp.continued_fraction_iterator(F)
ref = [next(it) for _ in range(N + 1)]
assert ref == quotients, (ref, quotients)
print("sympy continued_fraction_iterator agrees")
print("F ~", sp.N(F, 20))

# rational bounds for sqrt(462): L = floor(sqrt462 * 10^k)/10^k, U = L + 10^-k
K = 12
L = Fraction(isqrt(D * 10 ** (2 * K)), 10 ** K)
U = L + Fraction(1, 10 ** K)
assert L * L < D < U * U

# check that the floor inequalities a*s <= p + r*q < (a+1)*s follow from L < q < U by linear reasoning
for (p, r, s, a, g, P, R, S) in steps:
    lo = p + r * (L if r >= 0 else U)   # minimum of p + r q over q in (L,U)
    hi = p + r * (U if r >= 0 else L)   # maximum
    assert lo >= a * s, (p, r, s, a)
    assert hi < (a + 1) * s, (p, r, s, a)
print("bounds with K =", K, "decimal digits suffice for every floor")


def real(n):
    """Lean real literal for an integer (negative numbers parenthesised)."""
    return f"({n})" if n < 0 else f"{n}"


def state_expr(p, r, s):
    return f"({real(p)} + {real(r)} * Real.sqrt 462) / {real(s)}"


lines = []
A = lines.append
A("import Mathlib")
A("")
A("/-!")
A("# Disproof of Conjecture 00000000317 (The Last Math Competition)")
A("")
A("The conjecture claims (i) Freiman's constant `c_F` belongs to the Lagrange spectrum `L`")
A("but not to the Markov spectrum `M`, and (ii) among the first 20 partial quotients of `c_F`")
A("the digit 1 appears exactly 8 times.")
A("")
A("We refute the conjunction through clause (ii), which is a finite exact computation:")
A("the regular continued fraction of `c_F` begins")
A(f"`[{quotients[0]}; {', '.join(str(a) for a in quotients[1:])}, ...]`,")
A(f"so the digit 1 occurs {quotients[:20].count(1)} times among `a_0, …, a_19` and")
A(f"{quotients[1:21].count(1)} times among `a_1, …, a_20` — never 8.")
A("Clause (i) is left as an abstract proposition: it is false too (`L ⊆ M` is a theorem),")
A("but the refutation of the conjunction does not need it, so the spectra are not formalised.")
A("")
A("All partial quotients are obtained by the standard Gauss-map recursion, with every tail")
A("kept exactly in the form `(p + r·√462)/s` with explicit integers.")
A("-/")
A("")
A("open Real")
A("")
A("namespace Freiman")
A("")
A("/-- Freiman's constant `c_F`, the right end point of the maximal gap `(2√2, c_F)` of the")
A("Markov spectrum, in its standard closed form (Freiman 1975):")
A("`c_F = (2221564096 + 283748·√462) / 491993569 ≈ 4.5278295661…`. -/")
A("noncomputable def freimanConstant : ℝ :=")
A("  (2221564096 + 283748 * Real.sqrt 462) / 491993569")
A("")
A("/-- The Gauss-map orbit of a real number `x`: `cfState x 0 = x` and")
A("`cfState x (n+1) = 1 / fract (cfState x n)`. This is the standard recursion producing the")
A("regular continued fraction of `x`: `cfState x n` is the `n`-th complete quotient. -/")
A("noncomputable def cfState (x : ℝ) : ℕ → ℝ")
A("  | 0 => x")
A("  | n + 1 => 1 / Int.fract (cfState x n)")
A("")
A("/-- The `n`-th partial quotient `a_n` of the regular continued fraction")
A("`x = [a_0; a_1, a_2, …]`, defined as the integer part of the `n`-th complete quotient. -/")
A("noncomputable def pq (x : ℝ) (n : ℕ) : ℤ := ⌊cfState x n⌋")
A("")
A("theorem cfState_zero (x : ℝ) : cfState x 0 = x := rfl")
A("")
A("theorem cfState_succ (x : ℝ) (n : ℕ) : cfState x (n + 1) = 1 / Int.fract (cfState x n) := rfl")
A("")
A("/-! ### Arithmetic of `√462` -/")
A("")
A("theorem sq_sqrt462 : Real.sqrt 462 ^ 2 = 462 := Real.sq_sqrt (by norm_num)")
A("")
A(f"/-- Lower rational bound on `√462`, obtained from `{L.numerator}^2 < 462 · {L.denominator}^2`. -/")
A(f"theorem sqrt462_gt : ({L.numerator} : ℝ) / {L.denominator} < Real.sqrt 462 :=")
A("  (Real.lt_sqrt (by norm_num)).2 (by norm_num)")
A("")
A(f"/-- Upper rational bound on `√462`, obtained from `462 · {U.denominator}^2 < {U.numerator}^2`. -/")
A(f"theorem sqrt462_lt : Real.sqrt 462 < ({U.numerator} : ℝ) / {U.denominator} :=")
A("  (Real.sqrt_lt' (by norm_num)).2 (by norm_num)")
A("")
A("/-! ### Generic lemmas for one step of the Gauss map on `(p + r√462)/s` -/")
A("")
A("/-- Floor of a number of the form `(p + r√462)/s`, given rational bracketing. -/")
A("theorem floor_of_bounds (p r s : ℝ) (a : ℤ) (hs : 0 < s)")
A("    (h₁ : (a : ℝ) * s ≤ p + r * Real.sqrt 462)")
A("    (h₂ : p + r * Real.sqrt 462 < ((a : ℝ) + 1) * s) :")
A("    ⌊(p + r * Real.sqrt 462) / s⌋ = a := by")
A("  rw [Int.floor_eq_iff, le_div_iff₀ hs, div_lt_iff₀ hs]")
A("  exact ⟨h₁, h₂⟩")
A("")
A("/-- One Gauss-map step. If the `n`-th complete quotient is `(p + r√462)/s` with integer part")
A("`a`, then the next one is `(P + R√462)/S`, where `g·P = s(p − a s)`, `g·R = −s r`,")
A("`g·S = (p − a s)² − 462 r²` for some non-zero common factor `g` (used to cancel a gcd). -/")
A("theorem gauss_step (x : ℝ) (n : ℕ) (p r s P R S g : ℝ) (a : ℤ)")
A("    (hx : cfState x n = (p + r * Real.sqrt 462) / s) (hs : s ≠ 0)")
A("    (ha : ⌊cfState x n⌋ = a) (hg : g ≠ 0) (hS : S ≠ 0)")
A("    (hP : g * P = s * (p - a * s)) (hR : g * R = -(s * r))")
A("    (hSS : g * S = (p - a * s) ^ 2 - 462 * r ^ 2) :")
A("    cfState x (n + 1) = (P + R * Real.sqrt 462) / S := by")
A("  have hq := sq_sqrt462")
A("  set q := Real.sqrt 462 with hqdef")
A("  rw [cfState_succ, Int.fract, ha, hx]")
A("  have hfr : (p + r * q) / s - (a : ℝ) = ((p - a * s) + r * q) / s := by")
A("    field_simp")
A("    ring")
A("  rw [hfr]")
A("  have hne : (p - a * s) + r * q ≠ 0 := by")
A("    intro h0")
A("    apply hS")
A("    apply mul_left_cancel₀ hg")
A("    rw [hSS, mul_zero]")
A("    have : ((p - a * s) + r * q) * ((p - a * s) - r * q) = 0 := by rw [h0, zero_mul]")
A("    linear_combination this + r ^ 2 * hq")
A("  rw [one_div_div, div_eq_div_iff hne hS]")
A("  apply mul_left_cancel₀ hg")
A("  linear_combination s * hSS - ((p - a * s) + r * q) * hP - q * ((p - a * s) + r * q) * hR")
A("    + s * r ^ 2 * hq")
A("")
A("/-! ### The orbit of Freiman's constant, step by step -/")
A("")
p0, r0, s0 = states[0]
A(f"theorem state_0 : cfState freimanConstant 0 = {state_expr(p0, r0, s0)} := rfl")
A("")
for n, (p, r, s, a, g, P, R, S) in enumerate(steps):
    A(f"theorem pq_{n} : pq freimanConstant {n} = {a} := by")
    A(f"  unfold pq")
    A(f"  rw [state_{n}]")
    A(f"  have hL := sqrt462_gt")
    A(f"  have hU := sqrt462_lt")
    A(f"  exact floor_of_bounds _ _ _ _ (by norm_num) (by push_cast; linarith) (by push_cast; linarith)")
    A("")
    if n < N:
        A(f"theorem state_{n+1} : cfState freimanConstant {n+1} = {state_expr(P, R, S)} :=")
        A(f"  gauss_step freimanConstant {n} _ _ _ _ _ _ {real(g)} _ state_{n} (by norm_num) pq_{n}")
        A(f"    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)")
        A("")

A("/-! ### Counting the digit 1 -/")
A("")
A(f"/-- Among the first 20 partial quotients `a_0, …, a_19` of Freiman's constant, the digit 1")
A(f"occurs exactly {quotients[:20].count(1)} times (at indices {', '.join(str(i) for i in range(20) if quotients[i]==1)}). -/")
A("theorem count_ones_first20 :")
A(f"    ((Finset.range 20).filter (fun n => pq freimanConstant n = 1)).card = {quotients[:20].count(1)} := by")
A("  simp only [Finset.card_filter, Finset.sum_range_succ, Finset.sum_range_zero,")
A("    " + ", ".join(f"pq_{n}" for n in range(20)) + "]")
A("  norm_num")
A("")
A(f"/-- Variant indexing: among `a_1, …, a_20` the digit 1 occurs exactly {quotients[1:21].count(1)} times. -/")
A("theorem count_ones_1_to_20 :")
A(f"    ((Finset.range 20).filter (fun n => pq freimanConstant (n + 1) = 1)).card = {quotients[1:21].count(1)} := by")
A("  simp only [Finset.card_filter, Finset.sum_range_succ, Finset.sum_range_zero]")
A("  norm_num [" + ", ".join(f"pq_{n}" for n in range(1, 21)) + "]")
A("")
A("/-! ### Main theorems -/")
A("")
A("/-- **Conjecture 00000000317 is false.** The first clause (\"`c_F ∈ L` and `c_F ∉ M`\") is")
A("abstracted as an arbitrary proposition `InLNotM`: the refutation of the conjunction does not")
A("depend on it, because the second clause (\"the digit 1 appears exactly 8 times among the first")
A("20 partial quotients of `c_F`\") is false — the digit 1 appears exactly 5 times. -/")
A("theorem conjecture_00000000317_fails (InLNotM : Prop) :")
A("    ¬ (InLNotM ∧ ((Finset.range 20).filter (fun n => pq freimanConstant n = 1)).card = 8) := by")
A("  rintro ⟨-, h⟩")
A("  rw [count_ones_first20] at h")
A("  norm_num at h")
A("")
A("/-- Same conclusion if \"the first 20 partial quotients\" is read as `a_1, …, a_20`")
A("(the digit 1 then appears exactly 6 times, still not 8). -/")
A("theorem conjecture_00000000317_fails' (InLNotM : Prop) :")
A("    ¬ (InLNotM ∧ ((Finset.range 20).filter (fun n => pq freimanConstant (n + 1) = 1)).card = 8) := by")
A("  rintro ⟨-, h⟩")
A("  rw [count_ones_1_to_20] at h")
A("  norm_num at h")
A("")
A("end Freiman")
A("")
A("#print axioms Freiman.count_ones_first20")
A("#print axioms Freiman.count_ones_1_to_20")
A("#print axioms Freiman.conjecture_00000000317_fails")
A("#print axioms Freiman.conjecture_00000000317_fails'")

import sys
for st in steps:
    print(st)
pqs = [st[-1] if isinstance(st, (list, tuple)) else None for st in steps]
if "--write" in sys.argv:
    # Regenerate Disproof.lean next to this script (only on explicit request).
    import os
    out = os.path.join(os.path.dirname(os.path.abspath(__file__)), "Disproof.lean")
    with open(out, "w") as f:
        f.write("\n".join(lines) + "\n")
    print("wrote", out)
