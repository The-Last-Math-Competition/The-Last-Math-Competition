# Conjecture 00000004768 — Complete Disproof

## Overview

**Verdict:** **Disproven** (unconditional counterexamples at $n = 3$ and $n = 4$, including a universal prime-factor obstruction at $n = 4$ showing that $e(\mathrm{NC}_4) = 1{,}399{,}200 = 2^5 \cdot 3 \cdot 5^2 \cdot 11 \cdot 53$ divides neither $|\mathrm{NC}_4|! = 14!$ nor $\lparen |\mathrm{NC}_4|-2)! = 12!$ and admits no integer hook-length formula or bounded-factor product over the block-size product $D_4$).

### Official Conjecture Statement (`SOURCE.md`)

- **English:**
  > Definition: The noncrossing lattice is the poset lattice of partitions under refinement. Conjecture: Its linear extension count is an explicit hook-length type product, the denominator is the product of block sizes, and the count is computable in polynomial time. (hook-length product of NC linear extensions)
- **Chinese:**
  > 定义：非交叉格指分拆按加细的偏序格。猜想：其线性扩展计数为钩长型显式积,分母为块大小乘积且计数多项式时间可算。（NC 线性扩展钩长积）

### Mathematical Summary of the Disproof

1. **Coincidental agreement at $n = 1$ and $n = 2$ (Non-vacuity):** Let $\mathrm{NC}_n$ be Kreweras's noncrossing partition lattice of $[n]$ ordered by block refinement ($|\mathrm{NC}_n| = C_n = \frac{1}{n+1}\binom{2n}{n}$), let $e(\mathrm{NC}_n)$ be its number of linear extensions, and let $D_n := \prod_{\pi \in \mathrm{NC}_n} \prod_{B \in \pi} |B|$ be the product of all block sizes across $\mathrm{NC}_n$. At $n = 1$ ($|\mathrm{NC}_1| = 1, e = 1, D_1 = 1$) and $n = 2$ ($|\mathrm{NC}_2| = 2, e = 1, D_2 = 2$), the literal block-size hook-length formula $|\mathrm{NC}_n|! / D_n = e(\mathrm{NC}_n)$ holds.
2. **Direct failure of the block-size denominator at $n = 3$:** At $n = 3$, $|\mathrm{NC}_3| = 5$ ($M_3$), $e(\mathrm{NC}_3) = 3! = 6$, and $D_3 = 1 \cdot 2^3 \cdot 3 = 24$, so $|\mathrm{NC}_3|! / D_3 = 120 / 24 = 5 \ne 6 = e(\mathrm{NC}_3)$.
3. **Exact hand-verifiable evaluation and prime-factor obstruction at $n = 4$:** At $n = 4$, $|\mathrm{NC}_4| = 14$ ($1$ bottom, $6$ atoms, $6$ coatoms, $1$ top) and $D_4 = 2^{12} \cdot 3^4 = 331{,}776$. Using both an elementary bipartite telescoping identity over the $6! = 720$ coatom orderings (grouped into $9$ explicit $D_4$-symmetry neighborhood profiles) and Birkhoff's order-ideal dynamic programming recurrence over the $234$ lower sets of $\mathrm{NC}_4$, we prove
   $$e(\mathrm{NC}_4) = 1{,}399{,}200 = 2^5 \cdot 3 \cdot 5^2 \cdot 11 \cdot 53.$$
   Because $53$ is prime and $53 \gt 14 = |\mathrm{NC}_4|$:
   - $e(\mathrm{NC}_4) \nmid m!$ for **every** $m \lt 53$ (including $|\mathrm{NC}_4| = 14$, $|\mathrm{NC}_4|-2 = 12$, and $2n = 8$). Thus **no** integer-valued function $h : \mathrm{NC}_4 \to \mathbb{Z}_{\ge 1}$ whatsoever satisfies $|\mathrm{NC}_4|! = e(\mathrm{NC}_4) \prod_{\pi \in \mathrm{NC}_4} h(\pi)$.
   - Since $53 \mid e(\mathrm{NC}_4) \cdot D$ for every $D \ge 1$ (including $D_4$, the block-factorial product $\prod |B|!$, and the principal ideal/filter product $\prod |I(\pi)|$), **no** finite product of positive integers bounded by $52$ (in particular bounded by $|\mathrm{NC}_4| = 14$ or $2|\mathrm{NC}_4| = 28$) can equal $e(\mathrm{NC}_4) \cdot D$.
4. **Full partition lattice $\Pi_n$ and $n = 5$ irregular primes:** Even on the unrestricted Bell-number partition lattice $\Pi_n$, $\Pi_3 = \mathrm{NC}_3$ fails at $n = 3$, and at $n = 4$ ($|\Pi_4| = 15$), $e(\Pi_4) = 10{,}368{,}000 = 2^{10} \cdot 3^4 \cdot 5^3$ satisfies $15! \ne e(\Pi_4) D(\Pi_4)$ and $e(\Pi_4) \nmid 13!$. At $n = 5$ ($|\mathrm{NC}_5| = 42$), $e(\mathrm{NC}_5)$ is divisible by both a $10$-digit prime ($5{,}273{,}727{,}821$) and a $20$-digit prime ($71{,}064{,}201{,}736{,}056{,}904{,}919$).

---

## Package Contents

```text
package/
├── .gitignore                      # Ignores .lake/, *.aux, *.log (except verification/*.log), *.out, __pycache__/
├── SOURCE.md                       # Byte-for-byte copy of conjectures/00000004768.md (SHA-256 verified)
├── README.md                       # Package overview, reproduction commands, and formal coverage table
├── main.tex                        # Self-contained mathematical paper (LaTeX source)
├── main.pdf                        # Compiled mathematical paper (0 errors, 0 overfull/underfull boxes)
├── verify.py                       # Independent Python 3.12 verifier (lattice axioms, 3 linext methods, primes)
├── lean/
│   ├── lean-toolchain              # leanprover/lean4:v4.19.0
│   ├── lakefile.toml               # Self-contained Lake config (-DwarningAsError=true, zero dependencies)
│   ├── lake-manifest.json          # Lake manifest (zero external packages)
│   └── Main.lean                   # Complete Core Lean 4.19.0 formalization + #print axioms checks
└── verification/
    ├── lean-version.log            # Lean 4.19.0 and Lake version output
    ├── lake-build.log              # Clean scratch build log (exit 0, zero warnings)
    ├── lean-axioms.log             # Axiom audit output (lake env lean -DwarningAsError=true Main.lean)
    ├── pdf-build.log               # Clean two-pass pdflatex build log summary
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

## Formal Coverage Summary (`lean/Main.lean`, Namespace `Conjecture4768`)

All definitions and proofs are developed from first principles in Core Lean `4.19.0` with `-DwarningAsError=true` and zero external dependencies (`packages = []`). Every `#print axioms` check depends exclusively on subsets of `{propext, Classical.choice, Quot.sound}` (with zero `sorry`, `admit`, `native_decide`, custom `axiom`, `unsafe`, `implemented_by`, `extern`, or `opaque`).

| Concept / Theorem | Lean 4 Declaration(s) | Role |
|---|---|---|
| Exact finite cardinality & uniqueness | `HasCardinality`, `hasCardinality_unique` | Bijection-equivalent duplicate-free exhaustive enumeration (`\|α\| = n`), proved unique via pigeonhole induction |
| Primality of $53$ & Gauss–Euclid descent | `IsPrime`, `isPrime_53`, `IsPrime.dvd_mul`, `IsPrime.not_dvd_factorial`, `IsPrime.not_dvd_listProd_bounded` | First-principles primality certificate for $53$, Euclid's lemma, and prime-divisor bounds on factorials and bounded products |
| Posets, lattices, & linear extensions (list and bijection models) | `Poset`, `Lattice`, `IsLinearExtension`, `HasLinearExtensionCount`, `LinearExtensionBij`, `linearExtensionToBij`, `bijToLinearExtension` | Standard partial orders, lattices, and explicit equivalence between list linear extensions and order-preserving bijections $P \to \mathrm{Fin} N$ |
| Certified order-ideal DP engine | `verifyPosetLinExtCount`, `verifyPosetLinExtCount_sound` | Proves in `Prop` that layer-by-layer lower-set recurrence $e(I) = \sum_{z \in \max(I)} e(I \setminus \{z\})$ certifies exact linear extension counts via pure kernel `decide` |
| Set partitions, noncrossing condition, & refinement lattices | `SetPartition`, `IsNoncrossing`, `NCPartition`, `Refines`, `setPartitionLattice`, `ncPartitionLattice` | Canonical set partitions of `Fin n`, Kreweras $a \lt b \lt c \lt d$ noncrossing condition, equivalence-relation extensionality, and universal bounded lattice instances for all `n : Nat` |
| Exact Catalan/Bell cardinalities & linear extension counts | `nc1_card`..`nc5_card`, `pi4_card`, `nc1_linExt`..`nc4_linExt`, `pi4_linExt` | Certifies $\|\mathrm{NC}_1\|=1, \|\mathrm{NC}_2\|=2, \|\mathrm{NC}_3\|=5, \|\mathrm{NC}_4\|=14, \|\mathrm{NC}_5\|=42, \|\Pi_4\|=15$, $e(\mathrm{NC}_1)=1, e(\mathrm{NC}_2)=1, e(\mathrm{NC}_3)=6, e(\mathrm{NC}_4)=1{,}399{,}200, e(\Pi_4)=10{,}368{,}000$ |
| Non-vacuity positive witnesses ($n = 1, 2$) | `nc1_positive_witness`, `nc2_positive_witness` | Certifies that both `SatisfiesNCBlockSizeHookFormula n` and `HasIntegerHookFormula (NCPartition n)` hold non-vacuously at $n = 1$ and $n = 2$ |
| Disproof of block-size denominator formula ($n = 3, 4$) | `disproof_blockSize_hook_n3`, `disproof_blockSize_hook_n4` | Refutes $\|\mathrm{NC}_n\|! = e(\mathrm{NC}_n) \cdot D_n$ at $n = 3$ ($120 \ne 144$) and $n = 4$ ($53 \mid e(\mathrm{NC}_4) D_4$, $53 \nmid 14!$) |
| Universal integer hook-length & bounded-numerator impossibility | `nc4_linExt_not_dvd_factorial_lt53`, `nc4_no_integer_hook_formula`, `nc4_no_bounded_product_over_denominator`, `nc4_no_bounded_product_over_blockSizes` | Refutes $m! = e(\mathrm{NC}_4) \cdot D$ for all $m \lt 53$ and $\lparen \prod a_i) = e(\mathrm{NC}_4) \cdot D$ for all bounded positive factor lists ($a_i \lt 53$) |
| Complete multi-clause disproofs ($\mathrm{NC}_n$ and $\Pi_n$) | `disproof_conjecture4768_standard`, `disproof_conjecture4768_generalized`, `disproof_conjecture4768_fullPartitionLattice` | Unconditionally refutes the full conjecture (for arbitrary `PolyTimeComputable`) under standard, generalized, and unrestricted-partition interpretations |
