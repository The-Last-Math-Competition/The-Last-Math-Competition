# Resolution of Conjecture 00000007617

## Problem Statement

> **English.** Definition: Projective geometric algebra as the Grassmann exterior algebra. Conjecture: The intersection formula of the Plucker embedding is unique; and the correction of the formula is the sign factor. (Plucker intersection-formula sign correction)
>
> **中文。** 定义：射影几何代数为格拉斯曼外代数。猜想：Plücker 嵌入的交公式唯一；且公式的修正为符号因子。（Plucker 交公式符号修正）

## Verdict: **FALSE (Refuted)**

Conjecture `00000007617` is **false** in general across every standard formulation of Grassmann--Cayley algebra and Projective Geometric Algebra (PGA), while admitting a rigorous **positive transverse regime and rigidity theorem** that explain its origin.

Let $V = K^n$ ($n \ge 3$) be an $n$-dimensional vector space over a field $K$ (or commutative integral domain $R$) with exterior algebra $\Lambda\bigl(V\bigr) = \bigoplus_{k=0}^n \Lambda^k V$ and Plücker embedding $\iota_r : \mathrm{Gr}\bigl(r, V\bigr) \hookrightarrow \mathbb{P}\bigl(\Lambda^r V\bigr)$ sending $U = \mathrm{span}\{u_1, \dots, u_r\}$ to $[u_1 \wedge \dots \wedge u_r]$. For any volume form $\omega \in \Lambda^n V \setminus \{0\}$ with bracket $[\,\cdot\,]_\omega : \Lambda^n V \to K$ and Poincaré complement star $\star_\omega : \Lambda^k V \to \Lambda^{n-k} V$, the Grassmann--Cayley regressive product (meet) of $A \in \Lambda^r V$ and $B \in \Lambda^s V$ ($r + s \ge n$, $d := r + s - n$) is

$$
A \vee_\omega B = \star_\omega^{-1}\bigl(\star_\omega A \wedge \star_\omega B\bigr) \in \Lambda^d V.
$$

---

## Main Mathematical Findings

### 1. Positive Transverse Regime and Bilinear Rigidity (Non-Vacuity)

- **Exact Shuffle Equivalence and Transverse Meet (`Cl.regressive_basisBlade`, `Cl.positive_transverse_basis_meet`, `Cl.p2_lagrange_grassmann_meet`):** Across all dimensions $n \ge 2$ and grades $r + s \ge n$, the inverse-star dual-wedge meet $A \vee_\omega B$ agrees identically with the coordinate-free Barnabei--Brini--Rota shuffle meet $A \vee_\omega^{\mathrm{sh}} B$. Whenever $U + W = V$ (transverse subspaces), choosing an adapted basis $\mathcal{B} = \bigl(x_1, \dots, x_{n-s}, z_1, \dots, z_d, y_1, \dots, y_{n-r}\bigr)$ with $C = z_1 \wedge \dots \wedge z_d$ representing $U \cap W$ yields

$$
A \vee_\omega B = \det_\omega\bigl(\mathcal{B}\bigr)\, C \neq 0,
$$

so $\iota_d\bigl(U \cap W\bigr) = [A \vee_\omega B]$. On transverse coordinate basis blades ($I \cup J = \{0, \dots, n-1\}$), $e_I \vee_\omega e_J = \pm e_{I \cap J}$ has a pure sign coefficient in $\{+1, -1\}$.
- **Convention Sign-Correction Laws (`Cl.positive_convention_sign_corrections`):** Switching between the inverse-star meet $A \vee_\omega B$, the forward-star meet $A \vee_\omega^{\mathrm{fwd}} B = \star_\omega\bigl(\star_\omega A \wedge \star_\omega B\bigr)$, and the reversed-dual meet $A \vee_\omega^{\mathrm{rev}} B = \star_\omega^{-1}\bigl(\star_\omega B \wedge \star_\omega A\bigr)$ multiplies the output by the explicit grade-dependent signs $\bigl(-1\bigr)^{d\bigl(n-d\bigr)}$ and $\bigl(-1\bigr)^{\bigl(n-r\bigr)\bigl(n-s\bigr)} \in \{+1, -1\}$.
- **Transverse Bilinear Rigidity (`Cl.p2_transverse_bilinear_rigidity`):** Over **every** commutative ring $R$, any $R$-bilinear map $M : \Lambda^2\bigl(R^3\bigr) \times \Lambda^2\bigl(R^3\bigr) \to \Lambda^1\bigl(R^3\bigr)$ sending unimodularly transverse $2$-blade pairs into $U \cap W$ satisfies $M\bigl(A, B\bigr) = c\,\bigl(A \vee_{\omega_3} B\bigr)$ for a unique scalar $c \in R$.

### 2. Three Independent Refutations of the Unqualified Conjecture

1. **Refutation R1 — Non-Uniqueness Beyond $\{\pm 1\}$ and Non-Unit Sine/Determinant Conversion Factor:**
   - **Bracket-Scaling Non-Uniqueness (`Cl.r1_bracket_scaling_nonunique`):** On the Grassmann exterior algebra $\Lambda\bigl(V\bigr)$, no canonical volume bracket is distinguished; rescaling $\omega \mapsto \lambda\omega$ ($\lambda \in K^\times \setminus \{\pm 1\}$) scales $\vee_{\lambda\omega} = \lambda^{-1}\vee_\omega$ across a $1$-parameter $K^\times$-family of valid meet operators outside $\{\pm \vee_\omega\}$.
   - **Unit-Normalized Rational Plücker Counterexample (`Cl.r1_unit_plucker_blades_non_sign_factor`):** Even with a fixed Euclidean inner product, unit orientation $\omega_3$, and **unit-norm** Plücker $2$-blades $\|A\| = \|B\| = 1$ over $\mathbb{Q}^3$, taking $A = e_0 \wedge e_1$ and $B = \frac{3}{5}\bigl(e_0 \wedge e_1\bigr) + \frac{4}{5}\bigl(e_0 \wedge e_2\bigr)$ gives

$$
A \vee_{\omega_3} B = \frac{4}{5}\,e_0, \qquad \langle A \vee_{\omega_3} B, A \vee_{\omega_3} B \rangle = \frac{16}{25} \neq 1.
$$

   The conversion factor required to reach a unit Plücker $1$-blade $\pm e_0$ of $U \cap W = \mathrm{span}\{e_0\}$ is $\pm \frac{5}{4} = \pm \bigl(\sin\theta\bigr)^{-1} \notin \{+1, -1\}$, a continuous geometric angle/volume factor rather than a sign factor.
   - **Universal Bilinear Unit-Norm Impossibility (`Cl.r1_no_unit_preserving_bilinear_meet`):** Using the three strictly transverse unit $2$-blades $B_1 = e_0 \wedge e_2$ and $B_{2,3} = \pm\frac{3}{5}\bigl(e_0 \wedge e_1\bigr) + \frac{4}{5}\bigl(e_0 \wedge e_2\bigr)$ satisfying $B_2 + B_3 = \frac{8}{5}B_1$, bilinearity would force $5\bigl(\epsilon_2 + \epsilon_3\bigr) = 8\epsilon_1$ for $\epsilon_i \in \{\pm 1\}$, which is impossible ($\{-10, 0, +10\} \cap \{-8, +8\} = \emptyset$). Thus **no** bilinear map on $\Lambda^2\bigl(\mathbb{Q}^3\bigr)$ preserves unit norm on transverse unit blades.

2. **Refutation R2 — Identical Vanishing on Non-Transverse Intersections and Polynomial/Bilinear Impossibility:**
   - **Identical Vanishing (`Cl.r2_nontransverse_basis_vanish`, `Cl.r2_coinciding_lines_p2_vanish`, `Cl.r2_distinct_planes_k4_vanish`):** Whenever $\dim\bigl(U + W\bigr) \lt n$ ($r + s \ge n$), $A \vee_\omega B = 0$ identically—for example, coinciding lines $U = W = \mathrm{span}\{e_0, e_1\}$ in $\mathbb{P}^2$ ($n = 3, r = s = 2$) and **distinct** coplanar lines $U = \mathrm{span}\{e_0, e_1\}$, $W = \mathrm{span}\{e_0, e_2\}$ in $\mathbb{P}^3$ ($n = 4, r = s = 2$) meeting in the unique projective point $\mathbb{P}\bigl(U \cap W\bigr) = [e_0]$. Since $c \cdot 0 = 0$, no sign or scalar factor multiplying $A \vee_\omega B$ can recover $U \cap W$.
   - **Arbitrary-Degree Polynomial Impossibility (`Cl.r2_no_polynomial_intersection_k4`, `Cl.r2_no_bilinear_intersection_q4`):** Over any infinite integral domain $R$ ($\mathbb{Z}, \mathbb{Q}, \mathbb{R}, \mathbb{C}$), along the skew pencil $A = e_0 \wedge e_1$, $B_t = \bigl(e_0 + t e_3\bigr) \wedge e_2$, we have $U \cap W_t = \{0\}$ for all $t \neq 0$. By Bezout synthetic root counting at $D + 1$ nonzero points, **every** polynomial map $F : \Lambda^2\bigl(R^4\bigr) \times \Lambda^2\bigl(R^4\bigr) \to R^4$ of degree $\le D$ satisfying $F\bigl(A, B\bigr) \in U \cap W$ must satisfy $F\bigl(e_0 \wedge e_1, e_0 \wedge e_2\bigr) = 0$.
   - **Incident-Only Bilinear Impossibility (`Cl.r2_no_incident_only_bilinear_intersection_k4`):** Even with **zero** hypothesis on skew pairs ($U \cap W = \{0\}$), **no** bilinear map $F : \Lambda^2\bigl(R^4\bigr) \times \Lambda^2\bigl(R^4\bigr) \to R^4$ can output a nonzero vector in $U \cap W$ for all coplanar line pairs ($\dim\bigl(U \cap W\bigr) = 1$): if $F\bigl(e_0 \wedge e_1, e_0 \wedge e_2\bigr) = c_2 e_0 \neq 0$ and $F\bigl(e_0 \wedge e_1, e_0 \wedge e_3\bigr) = c_3 e_0$, then $w = -c_3 e_2 + c_2 e_3 \neq 0$ defines an incident plane $W_w = \mathrm{span}\{e_0, w\}$ with $F\bigl(e_0 \wedge e_1, e_0 \wedge w\bigr) = 0$.

3. **Refutation R3 — Degenerate Metric Collapse in Euclidean PGA $\mathrm{Cl}_{m, 0, 1}$:**
   - **Nilpotent Null Ideal and Collapse (`Cl.r3_pga_metricStar_sq_eq_zero`, `Cl.r3_pga_metricStar_wedge_eq_zero`, `Cl.r3_pga_origin_lines_obstruction`):** In Euclidean PGA $\mathrm{Cl}_{m, 0, 1}$ ($e_0^2 = 0$, $e_1^2 = \dots = e_m^2 = 1$), the ideal $\mathcal{J} = \bigl(e_0\bigr)$ satisfies $\mathcal{J} \cdot_q \mathcal{J} = \mathcal{J} \wedge \mathcal{J} = \{0\}$ and contains $\omega_{m+1} = e_0 e_1 \dots e_m$. Consequently, $\star_q\bigl(x\bigr) = \widetilde{x} \cdot_q \omega_{m+1} \in \mathcal{J}$ for **all** $x$, forcing $\star_q\bigl(\star_q\bigl(x\bigr)\bigr) = 0$ and $\star_q\bigl(A\bigr) \wedge \star_q\bigl(B\bigr) = 0$ identically across the entire algebra, as well as $\bigl(L_1 \cdot_q A \cdot_q R_1\bigr) \wedge \bigl(L_2 \cdot_q B \cdot_q R_2\bigr) = 0$ on the orthogonal origin lines $A = e_0 \wedge e_1$, $B = e_0 \wedge e_2$ in $\mathrm{Cl}_{2, 0, 1}$. Thus metric Clifford duality cannot be fixed by any sign factor and requires extrinsic non-metric Poincaré duality.

---

## Package Contents and Verification

- `SOURCE.md` — Unmodified competition problem statement.
- `main.tex`, `main.pdf` — Self-contained mathematical paper proving the positive transverse regime, transverse bilinear rigidity, and all three independent refutations.
- `verify.py` — Standalone Python 3 verification suite using exact rational arithmetic (`fractions.Fraction`) across dimensions $2 \le n \le 5$, checking $854$ basis-blade meet pairs, $1$D transverse rigidity in $\mathbb{P}^2$ and $\mathbb{P}^3$, Pythagorean unit-blade families, the $136/144$ incident-only classification in $\mathbb{Q}^4$, and degenerate PGA $\mathrm{Cl}_{m,0,1}$ ($1 \le m \le 3$).
- `lean/` — Zero-dependency Core Lean `v4.19.0` formalization (`-DwarningAsError=true`, zero `sorry`, zero custom axioms):
  - `Conjecture00000007617/Ring.lean` — `CRing`, `IDomain`, `Int` and quotient `QRat` instances, and Bezout synthetic polynomial root counting (`evalPoly_eq_zero_of_roots`).
  - `Conjecture00000007617/Exterior.lean` — Constructive $2^n$-dimensional Grassmann exterior and Clifford algebras `Cl R n`, grading `HasGrade`, universal vector alternation `wedge_vec_self_eq_zero`, and degenerate PGA nilpotent ideal `inNullIdeal`.
  - `Conjecture00000007617/PluckerMeet.lean` — Metric-free Poincaré star `pStar`/`pStarInv`, `[x ∧ ⋆y] = ⟨x, y⟩`, regressive product conventions, sign-correction laws, and general-dimension basis-blade theorem `regressive_basisBlade`.
  - `Conjecture00000007617/Main.lean` — Positive transverse theorems, $\mathbb{P}^2$ bilinear rigidity, Refutations R1, R2, R3, master negation `conjecture_00000007617_false`, and `#print axioms` checks.
- `verification/` — Build and verification logs (`lean-version.log`, `lake-build.log`, `lean-axioms.log`, `pdf-build.log`, `python-verify.log`, and `SELF_REVIEW.md`).
