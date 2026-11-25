# Conjecture 00000008546 — Disproof Package

## Verdict: **Disproved**

## Conjecture Statement (`SOURCE.md`)

> **English.** Definition: Orbit-Sperner refers to the Sperner property under group actions. Conjecture: The maximum of orbit antichains under symmetric group actions is the symmetrized Sperner number; and its difference from the classical Sperner number is of logarithmic order. (orbit Sperner deficit)
>
> **中文。** 定义：Orbit–Sperner 指群作用下的 Sperner 性。猜想：对称群作用下的轨道反链的最大值为对称化 Sperner 数；其与经典 Sperner 数之差为对数级。（轨道 Sperner 亏）

---

## Summary of the Disproof

Conjecture `00000008546` makes two assertions for symmetric group actions on graded Sperner posets (canonically the Boolean lattice $B_n = \mathcal{P}([n])$ of classical Sperner number $S(n) = \binom{n}{\lfloor n/2 \rfloor}$):

1. **Clause 1 (Orbit-Sperner identity):** The maximum size of an orbit antichain equals the *symmetrized Sperner number* (the largest symmetrized rank size).
2. **Clause 2 (Logarithmic orbit Sperner deficit):** Its difference from the classical Sperner number has logarithmic growth order $\Theta(\log n)$.

In algebraic combinatorics (Pouzet 1976, Stanley 1984, Harper 1985, Freese 1974, Engel 1997), an *orbit antichain* under a group action $G \le \mathrm{Aut}(P)$ has two canonical size measures:

- **Model I (Quotient-poset / Orbit-count model):** Antichains $\mathcal{F} \subseteq P/G$ of pairwise incomparable $G$-orbits in the quotient poset $P/G$, measured by the number of orbits $|\mathcal{F}|$, with maximum $w_{\mathrm{orb}}(P,G) = \mathrm{width}(P/G)$, symmetrized Sperner number $S_G^{\mathrm{orb}}(P) = \max_k |P_k/G|$, and deficit $\Delta_{\mathrm{orb}}(P,G) = \mathrm{width}(P) - \mathrm{width}(P/G)$.
- **Model II (Invariant-antichain / Element-count model):** Equivalently, unions $A = \bigcup_{\mathcal{O} \in \mathcal{F}} \mathcal{O} \subseteq P$ of orbit antichains are the $G$-invariant antichains in $P$, measured by element count $|A|$, with maximum $w_{\mathrm{inv}}(P,G) = \max\{|A| : A \subseteq P \text{ is a } G\text{-invariant antichain}\}$ and deficit $\Delta_{\mathrm{inv}}(P,G) = \mathrm{width}(P) - w_{\mathrm{inv}}(P,G)$.

We prove that **the conjecture is false under every standard mathematical formulation**:

1. **Identically zero deficit in Model II (Freese–Dilworth Invariant Antichain Theorem):**
   For *every* finite poset $\bigl(P, \le\bigr)$ (graded or ungraded, Sperner or non-Sperner) and *every* group $G \le \mathrm{Aut}(P)$, the unique downset-minimal maximum antichain $A^* \subseteq P$ is fixed by all of $\mathrm{Aut}(P)$. Hence $w_{\mathrm{inv}}(P,G) = \mathrm{width}(P)$ and
   $$\Delta_{\mathrm{inv}}(P, G) = 0 \quad \text{identically,}$$
   which is never of logarithmic order $\Theta(\log n)$. On $B_n$ under any subgroup $H \le S_n$, the middle rank $L_{\lfloor n/2 \rfloor}$ is itself $H$-invariant of size $\binom{n}{\lfloor n/2 \rfloor}$.

2. **Exponential deficit in Model I on Boolean lattices (Universal Subgroup Dichotomy):**
   - For the canonical $S_n$-action on $B_n$, two subsets lie in the same $S_n$-orbit iff $|X| = |Y|$, and $[X]_{S_n} \le [Y]_{S_n} \iff |X| \le |Y|$. Thus $B_n / S_n \cong C_{n+1}$ is a chain of width $w_{\mathrm{orb}}(B_n, S_n) = 1$, and the deficit
     $$\Delta_{\mathrm{orb}}(B_n, S_n) = \binom{n}{\lfloor n/2 \rfloor} - 1 \sim \sqrt{\frac{2}{\pi n}}\,2^n$$
     grows **exponentially**, not as $\Theta(\log n)$.
   - More generally, for *every* subgroup $H \le S_n$ acting on $B_n$: either $H = \{\mathrm{id}\}$ ($\Delta_{\mathrm{orb}} = 0$), or $H$ contains $\sigma \ne \mathrm{id}$ moving some $a \ne b$ ($n \ge 2$), in which case every orbit antichain $\mathcal{F} \subseteq B_n / H$ satisfies
     $$2|\mathcal{F}| \le \binom{n}{\lfloor n/2 \rfloor} + \binom{n-1}{\lfloor (n-1)/2 \rfloor},$$
     forcing an exponential deficit $\Delta_{\mathrm{orb}}(B_n, H) \ge \frac{1}{2}\bigl(\binom{n}{\lfloor n/2 \rfloor} - \binom{n-1}{\lfloor (n-1)/2 \rfloor}\bigr) = \Omega\bigl(2^n / \sqrt{n}\bigr)$ (with exact minimum $\binom{n-2}{\lfloor n/2 \rfloor - 1}$ attained by a single transposition). Even auxiliary variants (Young subgroups, diagonal $B_n \times B_n$, unlabeled graphs $B_{\binom{m}{2}}/S_m$, orbit-transversal antichains, or log-ratios $\log_2 \mathrm{width}(B_n) - \log_2 \mathrm{width}(B_n/S_n) = \Theta(n)$) never produce $\Theta(\log n)$.

3. **Refutation of Clause 1 on general bounded graded Sperner posets:**
   While Clause 1 holds on unitary Peck posets such as $B_n$ by Stanley's theorem (1984), mere Spernerity does *not* pass to symmetric-group quotients. For every $n \ge 2$, we construct a bounded graded poset $P(n)$ of rank $3$ and size $4n + 6$ with a **faithful** $S_n$-action such that $\mathrm{width}(P(n)) = 2n + 2 = \max_k |P(n)_k|$ (so $P(n)$ is Sperner), yet $P(n)/S_n$ has orbit-rank sizes $\bigl(1, 4, 4, 1\bigr)$ (symmetrized Sperner number $4$) and exact orbit-antichain width $\mathrm{width}(P(n)/S_n) = 5 \gt 4$.

---

## Package Structure

| Path | Description |
|---|---|
| `SOURCE.md` | Original untouched conjecture statement (English & Chinese) |
| `main.tex` / `main.pdf` | Self-contained mathematical paper proving all theorems and counterexamples |
| `verify.py` | Standalone Python 3 verification suite covering all models, bounds, and counterexamples |
| `lean/lean-toolchain` | Pinned to `leanprover/lean4:v4.19.0` |
| `lean/lakefile.toml` | Core Lean 4 package configuration (`moreLeanArgs = ["-DwarningAsError=true"]`, zero external dependencies) |
| `lean/OrbitSperner/Foundations.lean` | Posets, Harper–Stanley orbit-antichain lemma, pigeonhole on `Fin n`, `Perm n`, quotient poset $P/G$, and invariant-antichain bijection |
| `lean/OrbitSperner/BooleanSperner.lean` | Boolean lattice $B_n$, De Bruijn–Tengbergen–Kruyswijk symmetric chain decomposition, Sperner's theorem for all $n$, and $\bigl(n+1\bigr)\binom{n}{\lfloor n/2 \rfloor} \ge 2^n$ |
| `lean/OrbitSperner/SymmetricActions.lean` | Canonical $\bigl(B_n, S_n\bigr)$ orbit/quotient theorems and the universal nontrivial permutation subgroup bound |
| `lean/OrbitSperner/Counterexamples.lean` | Freese–Dilworth invariant antichain theorem, faithful $S_n$-counterexample family $P(n)$, asymptotic $\Theta(\log n)$ refutations, and master disproof theorem |
| `verification/` | Build logs (`lake-build.log`, `lean-axioms.log`, `lean-version.log`, `pdf-build.log`, `python-verify.log`) and `SELF_REVIEW.md` |

## Reproduction Commands

From inside `lean/`:
```bash
lake build
```

From the package root:
```bash
python3 verify.py
pdflatex -interaction=nonstopmode -halt-on-error main.tex
pdflatex -interaction=nonstopmode -halt-on-error main.tex
```
