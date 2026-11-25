# Conjecture 00000002223 — Complete Disproof

## Overview

**Verdict:** **Disproven** — while Clause 1 ($\mathrm{diam}(\Gamma(R \mathbin{\triangleright\!\triangleleft} P)) \le 3$) holds universally by Anderson–Livingston's theorem, Clause 2 (*"and the spectral condition on ideals attaining three is given by prime chains of length two"*) is **false in both logical directions** (both necessity and sufficiency fail across all standard interpretations of prime-chain length and ambient prime spectrum).

### Official Conjecture Statement (`SOURCE.md`)

- **English:**
  > Definition: Amalgamated duplication is the doubled-copy ring of a prime ideal. Conjecture: The diameter of its zero-divisor graph is at most three; and the spectral condition on ideals attaining three is given by prime chains of length two. (duplicated ring zero-divisor graph diameter three)
- **Chinese:**
  > 定义：amalgamated duplication 指素理想的双副本环。猜想：其零因子图的直径不超过三；且达到三的理想谱条件由素链的长度二给出。（重复环零因子图直径三）

### Mathematical Summary

For a commutative ring $R$ ($1_R \ne 0_R$) and a prime ideal $P \in \mathrm{Spec}(R)$, the **amalgamated duplication** of $R$ along $P$ (D'Anna–Fontana 2007) is the subring
$$R \mathbin{\triangleright\!\triangleleft} P := \{(r, s) \in R \times R : s - r \in P\} = \{(r, r + p) \in R \times R : r \in R,\; p \in P\},$$
and its **zero-divisor graph** $\Gamma(R \mathbin{\triangleright\!\triangleleft} P)$ (Anderson–Livingston 1999) has vertex set $Z^*(R \mathbin{\triangleright\!\triangleleft} P) = \{x \in (R \mathbin{\triangleright\!\triangleleft} P) \setminus \{0\} : \exists y \ne 0,\; xy = 0\}$ with edges between distinct $x \ne y$ satisfying $xy = 0$.

1. **Clause 1 holds universally:** For *every* commutative ring $A$ (and in particular every $R \mathbin{\triangleright\!\triangleleft} P$), every pair of vertices in $\Gamma(A)$ has graph distance at most $3$ (`zeroDivisorGraph_diameter_at_most_three`, `amalgamatedDuplication_diameter_at_most_three`).
2. **Clause 2 — Failure of Necessity (Minimal $4$-Element Counterexample & Infinite Boolean Family):**
   - For $R_0 = \mathbb{F}_2 \times \mathbb{F}_2$ and $P_0 = \{0\} \times \mathbb{F}_2 \in \mathrm{Spec}(R_0)$, $R_0 \mathbin{\triangleright\!\triangleleft} P_0 \cong \mathbb{F}_2^3$ has $8$ elements, and $\Gamma(R_0 \mathbin{\triangleright\!\triangleleft} P_0)$ is the $6$-vertex $3$-sunlet (net) graph of **exact diameter $3$** (with shortest path $\bigl((0,1),(0,1)) \sim ((1,0),(1,0)) \sim ((0,1),(0,0)) \sim ((1,0),(1,1)\bigr)$).
   - More generally, for every $m \in \mathbb{N}$, $R^{(m)} = \mathbb{F}_2^{m+2}$ along $P^{(m)} = \{f : f(0) = 0\}$ yields pairwise non-isomorphic finite Boolean rings ($|R^{(m)}| = 2^{m+2}$, $|R^{(m)} \mathbin{\triangleright\!\triangleleft} P^{(m)}| = 2^{2m+3}$) with $\mathrm{diam}(\Gamma(R^{(m)} \mathbin{\triangleright\!\triangleleft} P^{(m)})) = 3$.
   - In *any* Boolean ring $B$ ($a^2 = a$), every inclusion $Q_0 \subseteq Q_1$ of prime ideals is an equality (`boolean_prime_subset_eq`). Hence **neither $\mathrm{Spec}(R^{(m)})$ nor $\mathrm{Spec}(R^{(m)} \mathbin{\triangleright\!\triangleleft} P^{(m)})$ contains any strict prime chain of length $\ge 1$** (ruling out both $2$-edge chains $Q_0 \subsetneq Q_1 \subsetneq Q_2$ and $1$-edge chains $Q_0 \subsetneq Q_1$).
3. **Clause 2 — Failure of Sufficiency (Integral Domains & Exact Height-Two Witness $\mathbb{F}_2[x, y]$):**
   - For *every* commutative integral domain $D$ and *every* nonzero prime ideal $P \in \mathrm{Spec}(D) \setminus \{\{0\}\}$, $\Gamma(D \mathbin{\triangleright\!\triangleleft} P)$ is the complete bipartite graph $K_{|P \setminus \{0\}|, |P \setminus \{0\}|}$ with $|P \setminus \{0\}| \ge 2$, and therefore has **exact diameter $2 \ne 3$** (`domain_nonzero_prime_duplication_diam_two`).
   - Specifically, in $D = \mathbb{F}_2[x, y]$ at $P = (x, y)$, $\lparen 0) \subsetneq (x) \subsetneq (x, y) = P$ is a strict prime chain of **exact height $\mathrm{ht}(P) = 2$** (`f2xy_idealXY_hasExactHeight_two`), lifting to a strict prime chain of length $2$ in $\mathbb{F}_2[x, y] \mathbin{\triangleright\!\triangleleft} (x, y)$ as well — yet $\mathrm{diam}(\Gamma(\mathbb{F}_2[x, y] \mathbin{\triangleright\!\triangleleft} (x, y))) = 2 \ne 3$.

---

## Package Contents

```text
package/
├── .gitignore                      # Ignores .lake/, *.aux, *.log (except verification/*.log), *.out, __pycache__/
├── SOURCE.md                       # Byte-for-byte copy of conjectures/00000002223.md (SHA-256 verified)
├── README.md                       # Package overview, reproduction commands, and formal coverage table
├── main.tex                        # Self-contained mathematical paper (LaTeX source)
├── main.pdf                        # Compiled mathematical paper (0 errors, 0 overfull boxes)
├── verify.py                       # Independent Python 3.12 finite-ring & polynomial-window verifier
├── lean/
│   ├── lean-toolchain              # leanprover/lean4:v4.19.0
│   ├── lakefile.toml               # Self-contained Lake config (-DwarningAsError=true, zero dependencies)
│   ├── lake-manifest.json          # Lake manifest (zero external packages)
│   └── Main.lean                   # Complete Core Lean 4.19.0 formalization + #print axioms checks
└── verification/
    ├── lean-version.log            # Lean 4.19.0 and Lake version output
    ├── lake-build.log              # Clean scratch build log (exit 0, zero warnings)
    ├── lean-axioms.log             # Axiom audit output (lake env lean -DwarningAsError=true Main.lean)
    ├── pdf-build.log               # Clean two-pass pdflatex build log
    ├── python-verify.log           # Output of verify.py
    └── SELF_REVIEW.md              # Adversarial semantic and formal audit against SOURCE.md
```

---

## Reproduction Commands

### 1. Lean 4 Formal Verification (Core Lean `v4.19.0`, zero network access)

```powershell
# Add Lean 4.19.0 to PATH if needed:

cd lean
lake build
lake env lean -DwarningAsError=true Main.lean
```

### 2. LaTeX Compilation (`pdflatex`)

```powershell
# Add TinyTeX to PATH if needed:

pdflatex -interaction=nonstopmode -halt-on-error main.tex
pdflatex -interaction=nonstopmode -halt-on-error main.tex
```

### 3. Independent Python 3.12 Verification

```powershell
python verify.py
```

---

## Formal Coverage Summary (`lean/Main.lean`, Namespace `Conjecture2223`)

All definitions and proofs are developed from first principles in Core Lean `4.19.0` with `-DwarningAsError=true` and zero external dependencies (`packages = []`). Every `#print axioms` check depends exclusively on subsets of `{propext, Classical.choice, Quot.sound}` (with `hasGraphDiameter_unique` using zero axioms, and zero occurrences of `sorry`, `admit`, `native_decide`, custom `axiom`, `unsafe`, `implemented_by`, `extern`, or `opaque`).

| Concept / Theorem | Lean 4 Declaration(s) | Role |
|---|---|---|
| Commutative rings, ideals, prime ideals, prime chains, exact height | `CommRing`, `Ideal`, `IsPrimeIdeal`, `HasPrimeChainEndingAt`, `HasPrimeChainOfLength`, `HasExactHeight` | First-principles ring & spectral definitions ($0 \ne 1$, proper prime ideals, $k$-step strict chains) |
| Amalgamated duplication $R \mathbin{\triangleright\!\triangleleft} P$ & chain lifting | `AmalgamatedDuplication`, `instCommRingAmalgamatedDuplication`, `mem_duplication_iff_add`, `lift_primeChainOfLength` | Subring $\{(r, s) : s - r \in P\}$, equivalence with $\{(r, r+p)\}$, and $\pi_1^{-1}$ lifting of prime chains |
| Zero-divisor graph $\Gamma(A)$, simple-path equivalence, diameter uniqueness | `ZeroDivisorVertex`, `zdgAdj`, `HasGraphDiameter`, `exists_walk_le_iff_exists_simplePath_le`, `hasGraphDiameter_unique` | Anderson–Livingston graph on $Z^*(A)$, walk vs. simple-path equivalence, uniqueness of diameter |
| Clause 1: Universal upper bound $\mathrm{dist} \le 3$ | `zeroDivisorGraph_diameter_at_most_three`, `amalgamatedDuplication_diameter_at_most_three` | Proves Clause 1 holds for all commutative rings $A$ and all $R \mathbin{\triangleright\!\triangleleft} P$ |
| Boolean spectrum theorem ($\dim = 0$) | `IsBooleanRing`, `boolean_prime_subset_eq`, `boolean_no_prime_chain_ge_one`, `amalgamatedDuplication_isBoolean` | Proves neither $B$ nor $B \mathbin{\triangleright\!\triangleleft} P$ has any strict inclusion $Q_0 \subsetneq Q_1$ of prime ideals |
| Infinite Boolean counterexample family $R^{(m)} = \mathbb{F}_2^{m+2}$ | `CounterexampleRingFamily`, `counterexampleDupFamily_hasDiameter_three`, `counterexampleRingFamily_pairwise_noniso`, `counterexampleDupFamily_pairwise_noniso` | Pairwise non-isomorphic finite Boolean rings ($m=0$ gives $\mathbb{F}_2 \times \mathbb{F}_2$) with $\mathrm{diam} = 3$ and zero prime chains |
| Integral domain duplication theorem ($\mathrm{diam} = 2$) | `domain_nonzero_prime_duplication_diam_two`, `domain_chain_ge_one_diam_two` | Proves $\Gamma(D \mathbin{\triangleright\!\triangleleft} P)$ has exact diameter $2 \ne 3$ for every integral domain $D$ and nonzero prime $P$ |
| Exact height-2 witness $\mathbb{F}_2[x, y]$ at $P = (x, y)$ | `Poly`, `F2XY`, `f2xy_idealXY_hasExactHeight_two`, `f2xy_dup_hasDiameter_two`, `f2xy_dup_not_hasDiameter_three` | Certifies $\mathrm{ht}((x, y)) = 2$ via pseudo-division while $\mathrm{diam}(\Gamma(\mathbb{F}_2[x,y] \mathbin{\triangleright\!\triangleleft} (x,y))) = 2 \ne 3$ |
| Positive non-vacuity & complete disproofs | `non_vacuity_positive_witnesses`, `disproof_conjecture2223_iff_baseChain2`, `disproof_conjecture2223_iff_idealChain2`, `disproof_conjecture2223_iff_exactHeight2`, `disproof_conjecture2223_iff_dupChain2`, `disproof_conjecture2223_iff_chain1_base`, `disproof_conjecture2223_iff_chain1_dup`, `disproof_necessity_anyStrictChain`, `disproof_sufficiency_exactHeight2` |Simultaneously certifies non-vacuity and refutes characterization, necessity, and sufficiency across all spectral readings |
