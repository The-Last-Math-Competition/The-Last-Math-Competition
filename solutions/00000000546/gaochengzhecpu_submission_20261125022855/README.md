# Conjecture 00000000546 — Disproof and Complete Structural Resolution

## Source Statement

> **English.** Definition: The depth of monomial subrings. Conjecture: The depth-drop threshold of the numerical semigroup $\langle a, a+1, \dots, a+k \rangle$ equals $\lceil a/k \rceil$ (a depth jump for symmetric gaps).
>
> **中文。** 定义：Monomial 子环的 depth。猜想：数值半群 $\langle a, a+1, \dots, a+k \rangle$ 的深度递降阈值为 $\lceil a/k \rceil$ (对称间隙的深度跃变)。

## Verdict: **Disproved (Refuted Across All Homological and Combinatorial Readings, with Exact Closed-Form Corrections)**

Conjecture `00000000546` conflates the **homological depth** of commutative monomial subrings with Shalom Eliahou's **combinatorial depth** $q(S) = \lceil C(S)/m(S) \rceil$ of numerical semigroups, and the claimed formula $\lceil a/k \rceil$ is **false** under every standard algebraic and combinatorial interpretation of $S_{a,k} = \langle a, a+1, \dots, a+k \rangle$ ($a \ge 2$, $1 \le k \le a-1$):

1. **Affine monomial subring $K[S_{a,k}] = K[t^a, t^{a+1}, \dots, t^{a+k}] \subseteq K[t]$:**
   Over every field $K$, $t^a \in \mathfrak{m}$ is a nonzerodivisor and every polynomial $g \in \mathfrak{m}$ satisfies $g^{\lceil (a-1)/k \rceil + 1} \in t^a K[S_{a,k}]$. Thus $\mathrm{depth}_{\mathfrak{m}}(K[S_{a,k}]) = 1$ identically for all $a \ge 2$ and $1 \le k \le a-1$ — no depth drop ever occurs.

2. **Projective monomial curve coordinate ring $R_{a,k} = K[u^{a+k}, u^k v^a, \dots, v^{a+k}] \subseteq K[u, v]$:**
   Over every field $K$, $\bigl(u^{a+k}, v^{a+k}\bigr)$ is an $R_{a,k}$-regular sequence of length $2$ and $\mathfrak{m}_{R_{a,k}}^{\lceil (a-1)/k \rceil + 2} \subseteq \bigl(u^{a+k}, v^{a+k}\bigr) R_{a,k}$. Hence $\mathrm{depth}_{\mathfrak{m}}(R_{a,k}) = 2$ identically for all $a \ge 2$ and $1 \le k \le a-1$ — interval projective monomial curves are always Cohen–Macaulay and never drop depth.

3. **Tangent cone $\mathrm{gr}_{\mathfrak{m}}(K[[S_{a,k}]])$ and powers of the defining toric ideal $P / I_{a,k}^t$:**
   - Every $s \in S_{a,k}$ has exact $\mathfrak{m}$-adic valuation $\nu_{\mathfrak{m}}(t^s) = \lfloor s/a \rfloor$, so $\nu_{\mathfrak{m}}(t^{s+a}) = \nu_{\mathfrak{m}}(t^s) + 1$; by Sally's criterion, $\overline{t^a}$ is a nonzerodivisor and $\mathrm{depth}\bigl(\mathrm{gr}_{\mathfrak{m}}(K[[S_{a,k}]])\bigr) = 1$ identically.
   - Its Hilbert function $H_{\mathrm{gr}_{\mathfrak{m}}}(r) = \min(rk+1, a)$ and reduction number $\min\{r \ge 1 : \mathfrak{m}^{r+1} = t^a \mathfrak{m}^r\}$ equal $\lceil (a-1)/k \rceil$, whereas $\lceil a/k \rceil$ is instead the nilpotency index of the top generator $\overline{t^{a+k}}$ in $\mathrm{gr}_{\mathfrak{m}}(K[[S_{a,k}]])$ (the first $r$ where $r G_{a,k} \cap (r+1) G_{a,k} \ne \emptyset$).
   - For powers $P / I_{a,k}^t$ of the toric ideal, complete intersections ($k=1$ for all $a \ge 2$, and $k=2$ for all even $a \ge 4$) maintain $\mathrm{depth}(P / I_{a,k}^t) = 1$ for all $t \ge 1$, while $S_{5,2}$ drops to depth $0$ at $t = 2 \ne 3 = \lceil 5/2 \rceil$ and $S_{5,3}$ drops at $t = 3 \ne 2 = \lceil 5/3 \rceil$.

4. **Eliahou's combinatorial depth $q(S_{a,k}) = \lceil C(S_{a,k})/m(S_{a,k}) \rceil$ and ordinary power truncations $S_{a,k}^{(m)}$:**
   - Multiplicity is $m(S_{a,k}) = a$, conductor is $C(S_{a,k}) = \lceil (a-1)/k \rceil a$, Frobenius number is $F(S_{a,k}) = \lceil (a-1)/k \rceil a - 1$, and both $q(S_{a,k})$ and the ordinary threshold of $S_{a,k}^{(m)}$ equal
     $$q(S_{a,k}) = \left\lceil \frac{a-1}{k} \right\rceil.$$
   - This strictly disagrees with $\lceil a/k \rceil$ if and only if $a \equiv 1 \pmod{k}$, including **every** $a \ge 2$ when $k = 1$ (e.g., $S_{3,1} = \langle 3, 4 \rangle$ is symmetric with $q(S_{3,1}) = 2 \ne 3 = \lceil 3/1 \rceil$, and $S_{5,2} = \langle 5, 6, 7 \rangle$ has $q(S_{5,2}) = 2 \ne 3 = \lceil 5/2 \rceil$).

5. **Exact Symmetric-Gap Depth Jump vs. Failure of $\lceil a/k \rceil$:**
   - For $a \ge 2$ and $1 \le k \le a-1$, $S_{a,k}$ has symmetric gaps if and only if $k = 1$ or $k \mid (a - 2)$.
   - For fixed $k \ge 2$ and $a \ge k+2$, $S_{a,k}$ has symmetric gaps **if and only if** the true Eliahou depth jumps: $q(S_{a,k}) = q(S_{a-1,k}) + 1$ (dually, $q(S_{a,k+1}) \lt q(S_{a,k})$ at every symmetric $S_{a,k}$ with $1 \le k \le a-2$).
   - By contrast, the conjectured formula $\lceil a/k \rceil$ satisfies $\lceil a/k \rceil = \lceil (a-1)/k \rceil$ at **every** symmetric-gap semigroup for $k \ge 2$ (e.g., at symmetric $S_{5,3} = \langle 5, 6, 7, 8 \rangle$, $q$ jumps $1 \to 2$ while $\lceil 4/3 \rceil = 2 = \lceil 5/3 \rceil$ has zero jump).

6. **Symmetric-gap pinched Veronese subrings $B_{a,k}^{(m)}$ ($A^{\mathrm{sym}}_{a,k} = \{0,\dots,k\} \cup \{a,\dots,a+k\}$, $a \ge k+2$):**
   Even when embedding the symmetric gap block $\{k+1, \dots, a-1\}$ directly into a $2$-variable monomial subring $B_{a,k} \subseteq K[u, v]$, its $m$-th Veronese subring $B_{a,k}^{(m)}$ satisfies $\mathrm{depth}_{\mathfrak{m}}\bigl(B_{a,k}^{(m)}\bigr) = 2 \iff m \ge \lceil (a-1)/k \rceil$ (and depth $1$ for $1 \le m \lt \lceil (a-1)/k \rceil$), again refuting $\lceil a/k \rceil$ whenever $a \equiv 1 \pmod{k}$ (e.g., $a=5, k=2, m=2$).

## Package Contents

- `SOURCE.md` — Original bilingual problem statement (unmodified).
- `main.tex`, `main.pdf` — Self-contained mathematical manuscript with complete proofs and summary table across all six interpretations.
- `lean/` — Core Lean `v4.19.0` formalization (`zero` external dependencies, `-DwarningAsError=true`, zero `sorry`/`admit`/`native_decide`/custom axioms):
  - `Conjecture00000000546/Basic.lean` — Ceiling division `ceilDiv`, modular jump criteria, constructive field typeclass `FieldCoeff` with $\mathbb{F}_2$ witness, and univariate polynomial algebra `Poly1 K`.
  - `Conjecture00000000546/Semigroup.lean` — Interval numerical semigroup `InIntervalSemigroup`, conductor, Frobenius number, Eliahou depth `eliahouDepth_intervalSemigroup`, `powerSemigroup_ordinary_iff`, `hasSymmetricGaps_iff`, `symmetricGaps_iff_eliahouDepth_jump`, and `conjectured_formula_no_jump_at_symmetricGaps`.
  - `Conjecture00000000546/TangentCone.lean` — Exact $\mathfrak{m}$-adic order `inMaxIdealPower_iff_le_div`, Sally's criterion `tangentCone_ta_nonzerodivisor_poly`, `reductionNumber_threshold_iff`, and `topGenerator_nilpotent_in_gr_iff`.
  - `Conjecture00000000546/MonomialSubrings.lean` — Full polynomial subrings `K[S_{a,k}]`, projective closures `R_{a,k}`, and symmetric-gap pinched Veronese subrings `B_{a,k}^{(m)}` (`pinchedVeronese_isRegSeq2_iff`).
  - `Conjecture00000000546/Main.lean` — Master theorem `master_resolution_00000000546` and concrete counterexamples / non-vacuity witnesses (`counterexample_S3_1`, `counterexample_S5_2_all_readings`, `counterexample_symmetric_jump_S5_3`, `nonvacuity_witness_F2_5_2`).
- `verify.py` — Standalone Python 3.12 verification suite checking $435$ semigroup pairs, affine and tangent-cone filtrations, projective closures, $437$ pinched Veronese triples, and exact rational Gaussian elimination on toric ideal powers $P / I_{a,k}^t$.
- `verification/` — Recorded verification logs (`lake-build.log`, `lean-axioms.log`, `lean-version.log`, `pdf-build.log`, `python-verify.log`) and `SELF_REVIEW.md`.
