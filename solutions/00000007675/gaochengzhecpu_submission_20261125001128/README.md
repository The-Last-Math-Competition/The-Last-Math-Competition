# Resolution of Conjecture `00000007675`

- **Conjecture ID:** `00000007675`
- **Verdict:** **DISPROVED** (Conjecture `00000007675` is **FALSE**)
- **Lean Toolchain:** `leanprover/lean4:v4.19.0` (self-contained Core Lean 4, zero external dependencies, `-DwarningAsError=true`)

## Official Conjecture Statement (`SOURCE.md`)

- **English:** *Definition: The valuation v_p([n choose k]_q) at a prime power is defined by substituting q=p and then taking the p-adic valuation. Conjecture: v_p([n choose k]_p) = sum_{j>=1} (floor(n/p^j) - floor(k/p^j) - floor((n-k)/p^j) - carry_j(k,n-k)), where carry_j counts the j-th carry; and the alternative LCM-expression holds only when p<=n-k. (carry formula for Gaussian binomial valuations)*
- **中文:** *定义：Gaussian 二项式系数在素数幂处的赋值 v_p([n choose k]_q)|_{q=p} 定义为先代入再取 p-adic 赋值。猜想：v_p([n choose k]_p) = Σ_{j≥1} (floor(n/p^j) - floor(k/p^j) - floor((n-k)/p^j) - carry_j(k,n-k))，其中 carry_j 为第 j 位进位计数；特别地该值等于 floor(log_p LCM(k+1,…,n)/(k!(n-k)!)) 型表达式时仅当 p≤n-k。*

## Mathematical Summary

1. **Identically Vanishing Valuation of Gaussian Binomials at Prime Powers:**
   From the $q$-Pascal recurrence $\begin{bmatrix} n+1 \\ k+1 \end{bmatrix}_q = \begin{bmatrix} n \\ k+1 \end{bmatrix}_q + q^{n-k}\begin{bmatrix} n \\ k \end{bmatrix}_q$ (verified equivalent to both the $q$-factorial quotient $\frac{[n]_q!}{[k]_q![n-k]_q!}$ and the multiplicative formula $\prod_{i=1}^k \frac{q^{n-k+i}-1}{q^i-1}$), every Gaussian binomial coefficient satisfies $\begin{bmatrix} n \\ k \end{bmatrix}_q \equiv 1 \pmod{q}$ for all $q \ge 2$ and $0 \le k \le n$. Consequently, for **every** prime $p$, **every** integer $r \ge 1$, and **all** $0 \le k \le n$,
   $$v_p\!\left(\begin{bmatrix} n \\ k \end{bmatrix}_{p^r}\right) = 0, \qquad \text{and in particular} \qquad v_p\!\left(\begin{bmatrix} n \\ k \end{bmatrix}_p\right) = 0.$$

2. **Complete Resolution of Clause 1 (Carry-Difference Sum):**
   - Under the standard $1$-indexed base-$p$ carry convention ($\mathrm{carry}_j(a, b)$ denoting the carry into $p^j$, proved identical under schoolbook ripple-carry addition and modulo-$p^j$ residue addition), Kummer's exact termwise identity yields $\lfloor (a+b)/p^j \rfloor - \lfloor a/p^j \rfloor - \lfloor b/p^j \rfloor = \mathrm{carry}_j(a, b)$ for every $j \ge 1$. Thus every summand in Clause 1 vanishes identically, making Clause 1 a tautological $0 = 0$ identity.
   - Under the shifted $0$-indexed carry convention (carry out of $p^j$ into $p^{j+1}$, summed over $j \ge 1$), Clause 1 already fails at $\bigl(p, n, k) = (2, 2, 1\bigr)$ ($1 \neq 0$).

3. **Decisive Refutation of Clause 2 (and the Conjecture) Across All Parsings & Quantifier Scopes:**
   - **Refutation of "only when $p \le n - k$" (`仅当 p ≤ n - k`):**
     - For **every odd prime $p \ge 3$**, at the strictly interior pair $\bigl(n, k) = (2, 1\bigr)$ ($0 \lt k \lt n$), we have $n - k = 1 \lt p$ (so $p \le n - k$ is **false**), yet $\mathrm{lcm}(2)/(1!\,1!) = 2 \in [1, p)$ yields $\lfloor \log_p(2/1) \rfloor = 0 = v_p\!\left(\begin{bmatrix} 2 \\ 1 \end{bmatrix}_p\right)$ — and in fact **all eight** candidate parsings $\mathrm{LCM}_1, \dots, \mathrm{LCM}_8$ equal $0$.
     - At $p = 2$, the strictly interior pair $\bigl(n, k) = (3, 2\bigr)$ satisfies $n - k = 1 \lt 2 = p$ while $\lfloor \log_2(\mathrm{lcm}(3)/(2!\,1!)) \rfloor = \lfloor \log_2(3/2) \rfloor = 0 = v_2\!\left(\begin{bmatrix} 3 \\ 2 \end{bmatrix}_2\right)$.
   - **Refutation of the converse "when $p \le n - k$" and biconditional:**
     - At $\bigl(p, n, k) = (2, 4, 1\bigr)$ ($0 \lt k \lt n$, $p = 2 \le 3 = n - k$), $\mathrm{lcm}(2,3,4)/(1!\,3!) = 12/6 = 2$ gives $\lfloor \log_2 2 \rfloor = 1 \neq 0$ (and $\bigl(2, 3, 1\bigr)$ refutes the outer-quotient parsing $\mathrm{LCM}_2$).
     - More generally, for **every prime $p \ge 2$**, at $\bigl(n, k) = (2p + 6, 1\bigr)$ we have $p \le 2p + 5 = n - k$ while $\mathrm{lcm}(2, \dots, 2p + 6) \le (2p + 5)! / 2 \lt 1!\,(2p + 5)!$, forcing $\mathrm{LCM}_1(p, 2p + 6, 1) \le -1 \lt 0$.

## Package Structure

- `SOURCE.md` — Exact copy of `conjectures/00000007675.md`.
- `main.tex` / `main.pdf` — Complete mathematical disproof manuscript and compiled PDF.
- `verify.py` — Standalone Python 3.12 computational verification script (zero external packages).
- `lean/` — Self-contained Core Lean 4.19.0 project (`lean-toolchain`, `lakefile.toml`, `lake-manifest.json`, `Main.lean`).
- `verification/` — Build and verification logs (`lean-version.log`, `lake-build.log`, `lean-axioms.log`, `pdf-build.log`, `python-verify.log`, `SELF_REVIEW.md`).

## Reproducibility Commands

```powershell
# 1. Run Python verification
python verify.py

# 2. Build Core Lean 4.19.0 formalization (with -DwarningAsError=true)
cd lean
lake build

# 3. Compile LaTeX manuscript (2 passes)
pdflatex -interaction=nonstopmode -halt-on-error main.tex
pdflatex -interaction=nonstopmode -halt-on-error main.tex
```
