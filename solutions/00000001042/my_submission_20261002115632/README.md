# Disproof of TLMC Conjecture 00000001042

**Verdict: FALSE.**

## Object discipline — the statement attacked (verbatim from `conjectures/00000001042.md`)

> **English.** Conjecture: The variance of the value-set size of a random polynomial f uniform of degree ≤ d is asymptotically q·(1 − 1/e)/d (value-set variance).
>
> **中文。** 猜想：随机多项式 f 均匀取自次数 ≤ d 的值集大小的方差为 q·(1 − 1/e)/d 的渐近(值集方差)。

Reading (matches the confirmed verify-note "a,b 全 F_q"): *f uniform of degree ≤ d* means uniform over **all** coefficient tuples (a₀, …, a_d) ∈ F_q^{d+1} (constant polynomials included), and the value set is {f(x) : x ∈ F_q} ⊆ F_q. The conjecture is a universal claim over d; exhibiting d = 1 falsifies it.

## Attack point (from the verify queue): d = 1, q = 101 — exact enumeration

For d = 1, f(x) = a·x + b with (a, b) uniform over F_101 × F_101 (10201 polynomials):

* a ≠ 0: x ↦ a·x + b is a bijection F_101 → F_101, so the value-set size is V = 101;
* a = 0: f is constant, V = 1.

Exact enumeration (reproduced independently in `reproduce.py` and in `lean4/Main.lean`):

| quantity | exact value | decimal |
|---|---|---|
| ΣV | (q−1)·q² + q = 1020201 | |
| E[V] | 10101/101 | 100.00990099… |
| ΣV² | (q−1)·q³ + q = 103030201 | |
| E[V²] | 1020101/101 | 10100.00990099… |
| **Var = E[V²] − E[V]²** | **1000000/10201** | **98.02960494…** |

Closed form for general q (exact rational identity; Var·q⁴ = q²·(q−1)³):

Var = (q−1)³/q², checked by brute-force enumeration in `reproduce.py` for q ∈ {2, …, 50, 101}.

## Disproof

Conjectured value at (q, d) = (101, 1): q·(1 − 1/e)/d = 101·(1 − 1/e) ≈ **63.84417644** (e ≈ 2.718281828). True value: **98.02960494**. Absolute gap ≈ 34.19; ratio ≈ 1.535.

The key step is done **without floating point**, by an explicit rational bound for Euler's number: e = Σ_{k≥0} 1/k! < (1 + 1 + 1/2 + 1/6 + 1/24 + 1/120) + (1/720)·Σ_{j≥0} 7^{−j} = 163/60 + 7/4320 = 11743/4320 ≈ 2.7182870 < 2.72 = 68/25. Hence 1/e > 25/68 and

conjectured value = 101·(1 − 1/e) < 101·(1 − 25/68) = 4343/68 ≈ 63.8676 < 98.0296 = 1000000/10201,

where the last inequality is the exact integer check 4343·104060401 = 451934321543 < 693668000000 = 68·10201000000.

Asymptotic refutation: Var(q) = (q−1)³/q² → q as q → ∞, so Var(q)/q → **1**, whereas the conjecture asserts the limit is 1 − 1/e ≈ 0.6321. The claimed asymptotic constant is wrong; d = 1 is a counterexample to the "asymptotically q(1−1/e)/d" claim (matches the verify note "d=1 渐近 Var→q≠(1−1/e)q").

| q | Var = (q−1)³/q² (exact) | claimed (1−1/e)·q |
|---|---|---|
| 101 | 98.0296 | 63.8442 |
| 1009 | 1006.0030 | 637.8096 |
| 10007 | 10004.0003 | 6325.6304 |

## Boundary case (alternative reading)

If "uniform of degree ≤ d" were instead read as "uniform over degree-**exactly**-d polynomials" (a ≠ 0, N = 10100 pairs), then V ≡ 101 deterministically and **Var = 0 ≠ 63.8442** — the conjecture fails under this reading as well.

## Lean formalization (`lean4/`, Lean 4.33.1 core only — no Mathlib, zero axioms, no `sorry`)

* `Main.lean` defines the value-set size `V`, enumerates all 10201 (resp. 10100) polynomials with recursive sums, and proves:
  * `totalV_eq`, `totalV2_eq`, `scaledVar_eq` (`Var·101⁴ = totalV2·101² − totalV² = 10201000000`, i.e. Var = 1000000/10201), `gap` (`4343·101⁴ < 68·10201000000`) — all by `decide` on the actual enumeration;
  * `attack` — the main disproof: for every pair (m, d) representing a candidate e = n/d = (m+d)/d with m > 0 and 25·(m+d) ≤ 68·d (i.e. 1 < e ≤ 68/25), the equation `Var·101⁴·(m+d) = 101·m·101²` is refuted by pure Nat arithmetic (no `omega`, no truncated subtraction: the difference n − d is the explicit witness m);
  * `scaledVar1_eq`, `attack_exact1`, `deg1_deterministic` — the boundary reading (Var = 0 ≠ conjectured value for e > 1).
* Helper lemmas `mul_assoc'`, `mul_left_comm'`, `mul_swap`, `add_mul'`, `add_le_add_right_cancel'` are proved by pure structural induction because the corresponding core lemmas (`Nat.mul_assoc`, `Nat.add_mul`, ...) drag in `propext`.
* `Check.lean` runs `#print axioms` on every theorem: all are axiom-free (audited by `pack.sh verify`).

Proof tactics used: `decide`, `rw` with hand-built induction lemmas, `if_neg` — no `omega`, no `simp`, no classical axioms, no `sorry`.

## Reproduce

```bash
python3 reproduce.py                     # exact rational enumeration + bound checks
cd lean4 && lake build && lake env lean Check.lean   # Lean proofs + axiom audit
```
