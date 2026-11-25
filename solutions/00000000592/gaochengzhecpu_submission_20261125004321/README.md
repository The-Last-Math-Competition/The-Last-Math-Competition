# Conjecture 00000000592 — Disproof and Formal Verification

## Verdict: **FALSE**

Conjecture `00000000592` asserts that for the graded canonical module $\omega$ of a semigroup $\mathbb{Z}$-graded ring $R = k[S]$, (1) the minimal number of homogeneous generators $\mu_R(\omega)$ equals the type of $R$, and (2) the set of degrees of a minimal homogeneous generating set of $\omega$ equals the set of pseudo-Frobenius numbers plus an additive constant, $\mathrm{PF}(S) + c$.

While assertion (1) holds for all Cohen–Macaulay semigroup rings, **assertion (2) is FALSE** already for $1$-dimensional Cohen–Macaulay numerical semigroup rings at embedding dimension $4$ (and genus $4$, multiplicity $4$, Frobenius number $5$), because graded Matlis duality **negates** degrees:

$$\mathrm{Deg}_{\min}\bigl(\omega_{k[S]}(-c)\bigr) = -\mathrm{PF}(S) + c = \{-f + c : f \in \mathrm{PF}(S)\}.$$

Moreover, if Cohen–Macaulayness is not assumed for higher-rank positively $\mathbb{Z}$-graded affine semigroup rings, **assertion (1) also fails** (already at Krull dimension $2$ and embedding dimension $4$).

---

## Summary of Counterexamples and Positive Regimes

### 1. Primary Counterexample (Numerical Semigroup Ring, $\dim R = 1$, $\mathrm{edim}\, R = 4$)

Let $S = \langle 4, 6, 7, 9 \rangle = \mathbb{N} \setminus \{1, 2, 3, 5\}$ and $R = k[S] = \bigoplus_{s \in S} k t^s$ over any field $k$.

- **Invariants:** Krull dimension $\dim R = 1$ (Cohen–Macaulay), embedding dimension $e(S) = 4$, multiplicity $m(S) = 4$, genus $g(S) = 4$, Frobenius number $F(S) = 5$, and Cohen–Macaulay type $\mathrm{type}(R) = 3$.
- **Pseudo-Frobenius numbers:** $\mathrm{PF}(S) = \{2, 3, 5\}$, with consecutive gap vector $\bigl(3 - 2, 5 - 3\bigr) = \bigl(1, 2\bigr)$.
- **Canonical module minimal generator degrees:** By Goto–Watanabe local duality, $\omega_R = \underline{\mathrm{Hom}}_k\bigl(H^1_{\mathfrak{m}}(R), k\bigr) \cong \bigoplus_{-d \notin S} k t^d$, and any shifted canonical module $\omega = \omega_R(-c)$ ($c \in \mathbb{Z}$) has $\mu_R(\omega) = 3 = \mathrm{type}(R)$ and exact minimal generator degree set
  $$\mathrm{Deg}_{\min}\bigl(\omega_R(-c)\bigr) = \{-5 + c, -3 + c, -2 + c\},$$
  whose consecutive gap vector is $\bigl(2, 1\bigr) \ne \bigl(1, 2\bigr)$. Hence **no constant $c' \in \mathbb{Z}$** satisfies $\mathrm{Deg}_{\min}(\omega) = \mathrm{PF}(S) + c'$.
- **Higher-Krull-dimension Cohen–Macaulay extensions:** Adjoining $d - 1$ degree-$1$ polynomial variables gives Cohen–Macaulay semigroup $\mathbb{Z}$-graded domains $R_d = k[S \times \mathbb{N}^{d-1}]$ of **every Krull dimension $d \ge 1$** whose minimal canonical generator degrees $\{-5 + d - 1, -3 + d - 1, -2 + d - 1\}$ (up to shift) preserve the reflected gap vector $\bigl(2, 1\bigr) \ne \bigl(1, 2\bigr)$.

### 2. Why Small or Structured Test Suites Appeared to Confirm the Conjecture

The true degree set $-\mathrm{PF}(S) + c$ coincides with $\mathrm{PF}(S) + c'$ for some $c' \in \mathbb{Z}$ if and only if $\mathrm{PF}(S)$ is reflection-symmetric. This symmetry holds automatically for:

- **Every numerical semigroup with $\mathrm{type}(S) \le 2$** (since any set $\{f_1\}$ or $\{f_1, f_2\}$ of size $\le 2$ satisfies $-\{f_1, f_2\} = \{f_1, f_2\} - (f_1 + f_2)$), which by Herzog's theorem (1970) includes **100% of numerical semigroups of embedding dimension $e(S) \le 3$** and **100% of multiplicity $m(S) \le 3$**, as well as all symmetric and pseudo-symmetric semigroups in every dimension;
- **All numerical semigroups of genus $g(S) \le 3$ and all Frobenius numbers $F(S) \le 4$** ($S = \langle 4, 6, 7, 9 \rangle$ is the unique genus-$4$ counterexample);
- **All arithmetic-progression generator semigroups** $\langle a, a + d, \dots, a + k d \rangle$ ($\gcd(a, d) = 1$), whose $\mathrm{PF}(S)$ is always an arithmetic progression.

### 3. Non-Cohen–Macaulay Counterexample ($\dim R = 2$, $\mathrm{edim}\, R = 4$)

For Macaulay's smooth rational quartic curve semigroup $S_{\mathrm{Mac}} = \langle (4,0), (3,1), (1,3), (0,4) \rangle \cong \langle (1,0), (1,1), (1,3), (1,4) \rangle \subseteq \mathbb{N}^2$ (standard $\mathbb{Z}$-graded by the first coordinate, $\dim R = 2$, $\mathrm{depth}\, R = 1$):

- $\mathrm{PF}(S_{\mathrm{Mac}}) = \{(1, 2)\}$ has size $1$, matching $\mathrm{type}(R) = \dim_k \mathrm{Ext}^1_R(k, R) = 1$;
- Yet $\omega_R = \underline{\mathrm{Hom}}_k\bigl(H^2_{\mathfrak{m}}(R), k\bigr)$ requires **$\mu_R(\omega_R) = 3 \ne 1$** minimal homogeneous generators $\{(1,1), (1,2), (1,3)\}$ in $\mathbb{Z}$-degree $1$.

---

## Package Contents and Reproduction

| Path | Description |
| :--- | :--- |
| `SOURCE.md` | Original verbatim problem statement (English and Chinese) |
| `main.tex`, `main.pdf` | Self-contained mathematical paper and compiled PDF |
| `verify.py` | Standalone exact-arithmetic Python verification script (exits `0`) |
| `lean/lean-toolchain` | Pinned Lean toolchain (`leanprover/lean4:v4.19.0`) |
| `lean/lakefile.toml` | Self-contained Core Lean 4 Lake configuration (`-DwarningAsError=true`) |
| `lean/lake-manifest.json` | Zero-dependency Lake manifest |
| `lean/Main.lean` | Complete Core Lean 4 formalization of $\omega_S(c)$, alignment for $\mathrm{type} \le 2$, and both counterexamples |
| `verification/` | Build, axiom check, version, PDF compilation, Python check logs, and `SELF_REVIEW.md` |

### Verification Commands

1. **Lean 4 formalization** (from `lean/`):
   ```bash
   lake build
   ```
2. **Independent Python check**:
   ```bash
   python3 verify.py
   ```
3. **LaTeX paper compilation**:
   ```bash
   pdflatex -interaction=nonstopmode -halt-on-error main.tex
   pdflatex -interaction=nonstopmode -halt-on-error main.tex
   ```
