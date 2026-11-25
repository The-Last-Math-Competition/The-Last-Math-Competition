# Conjecture 00000007609 — Disproof and Complete Structural Analysis

## Conjecture Statement (`SOURCE.md`)

- **English:** *Definition: Reflection decomposition with the reflection-representation counting of rotations. Conjecture: The conversion constant is the reflection count of rotations, the minimal reflection count being angle-type; the counting is finite with parity given by the determinant; and the minimization is realized by geodesic decomposition. (reflection-counting conversion)*
- **Chinese:** *定义：反射分解：旋转的反射表示计数。猜想：换算常数为旋转的反射计数且最少反射数为角度型；计数有限且计数的奇偶由行列式；最少的实现为测地分解。（反射计数换算常数结构）*

---

## Final Verdict: **FALSE (Refuted)**

Conjecture `00000007609` is **false** across every standard mathematical formulation of orthogonal reflection decompositions in Euclidean, pseudo-Euclidean, rational, real, and finite-field orthogonal geometry. While its classical parity sub-clause ($\det(r_1 \cdots r_k) = (-1)^k$, away from characteristic $2$) holds, all three substantive structural claims fail simultaneously:

1. **Refutation of Claim B1 ("the counting is finite") — Infinite Minimal-Length Reflection-Operator Counting & Dieudonné's $\mathbb{F}_2^4$ Exception:**
   - Over any formally real field $F$ (in particular $F = \mathbb{R}$ and $F = \mathbb{Q}$), let $\mathcal{R}\bigl(F^2, Q_{2,0}\bigr)$ denote the set of orthogonal reflection operators on the Euclidean plane. For **every** non-identity planar rotation $R \in \mathrm{SO}_2(F) \setminus \{I_2\}$ and **every** slope parameter $t \in F$, the vector $u_t = \bigl(1, t\bigr)^\top$ satisfies $Q_{2,0}(u_t) = 1 + t^2 \neq 0$, the reflection operators $r_{u_t}$ satisfy $r_{u_t} = r_{u_s} \iff t = s$, and $r'_t := r_{u_t} R \in \mathcal{R}\bigl(F^2, Q_{2,0}\bigr)$ yields a minimal-length ($k = 2$) factorization $R = r_{u_t} \circ r'_t$ with $r_{u_t} \neq r'_t$. Thus every $R \in \mathrm{SO}_2(F) \setminus \{I_2\}$ possesses **infinitely many** pairwise distinct minimal-length ordered *and* unordered reflection-operator decompositions.
   - Allowing general reflection words, $r_u^2 = I$ produces valid decompositions of unbounded even lengths $2 + 2m$ ($m \in \mathbb{N}$), and across dimensions $2m$, $\ell_{\mathrm{ref}}(-I_{2m}) = 2m \to \infty$ is unbounded.
   - Conversely, on the split space $\bigl(\mathbb{F}_2^4, x_0 x_1 + x_2 x_3\bigr)$, reflections generate an index-$2$ subgroup $\langle \mathcal{R} \rangle \cong S_3 \times S_3$ of order $36$ inside $\lvert \mathrm{O}^+(4, \mathbb{F}_2) \rvert = 72$, leaving $18$ rotations in Dickson's special orthogonal group $\mathrm{SO}^+(4, \mathbb{F}_2)$ — including Dieudonné's coordinate-reversal rotation $D\bigl(x_0, x_1, x_2, x_3\bigr) = \bigl(x_3, x_2, x_1, x_0\bigr)$ — with **zero** reflection decompositions over $\mathbb{F}_2$ (even though its integral lift $\widetilde{D} \in \mathrm{SO}(2, 2; F)$ has $\ell_{\mathrm{ref}}(\widetilde{D}) = 2$).

2. **Refutation of Claim A ("the minimal reflection count being angle-type") — Discrete Rank Invariant & Scherk's Indefinite Rank Jump:**
   - In Euclidean $\mathrm{SO}_n(F)$, $\ell_{\mathrm{ref}}(R) = \mathrm{rank}(I_n - R) = 2s$ is twice the number of active rotation $2$-planes (a discrete rank/support invariant completely insensitive to continuous rotation angles): the infinite Cayley family $R_{t_n} = \frac{1}{1+t_n^2}\begin{pmatrix}1-t_n^2 & -2t_n\\ 2t_n & 1-t_n^2\end{pmatrix} \in \mathrm{SO}_2(F)$ ($t_n = n + 1$) has pairwise distinct rotation traces $\mathrm{tr}(R_{t_m}) \neq \mathrm{tr}(R_{t_n})$ yet identical $\ell_{\mathrm{ref}}(R_{t_n}) = 2$.
   - In $\mathrm{SO}_4(\mathbb{Z}) \subseteq \mathrm{SO}_4(F)$, $R_1 = \mathrm{diag}(-1, -1, 1, 1)$ (eigenangles $\bigl(\pi, 0\bigr)$) and $R_2 = \mathrm{diag}(J, J)$ (eigenangles $\bigl(\frac{\pi}{2}, \frac{\pi}{2}\bigr)$) share identical trace $\mathrm{tr}(R_1) = \mathrm{tr}(R_2) = 0$, identical squared Frobenius chordal distance $\lVert I_4 - R_1 \rVert_F^2 = \lVert I_4 - R_2 \rVert_F^2 = 8$, and identical $L^1$ total rotation angle $\pi + 0 = \frac{\pi}{2} + \frac{\pi}{2} = \pi$, yet $\ell_{\mathrm{ref}}(R_1) = 2 \neq 4 = \ell_{\mathrm{ref}}(R_2)$. Similarly, in $\mathrm{SO}(4; \mathbb{R})$, eigenangles $\bigl(\pi, 0\bigr)$ and $\bigl(\frac{3\pi}{5}, \frac{4\pi}{5}\bigr)$ share identical Riemannian $L^2$ geodesic distance $\sqrt{2}\,\pi$ yet have $\ell_{\mathrm{ref}} = 2 \neq 4$.
   - In split signature $\mathrm{SO}(2, 2; F)$, Scherk's unipotent null rotation $N$ satisfies $\bigl(I_4 - N\bigr)^2 = 0$, $\mathrm{tr}(N) = 4$ (zero rotation angle), and $\mathrm{rank}(I_4 - N) = 2$ with totally isotropic image, forcing $\ell_{\mathrm{ref}}(N) = 4 = \mathrm{rank}(I_4 - N) + 2 \gt 2$.

3. **Refutation of Claim C ("the minimization is realized by geodesic decomposition") — Indefinite Disconnectedness & Non-Commuting / $\mathbb{Q}^4$-Irreducible Euclidean Counterexamples:**
   - In Lorentzian $\mathrm{SO}(1, 1; F)$, $-I_2 = r_{e_0} \circ r_{e_1}$ has minimal reflection count $\ell_{\mathrm{ref}}(-I_2) = 2$, yet lies outside the square/exponential subgroup $\mathrm{SO}^+(1, 1; F)$ (over $\mathbb{R}$, **zero** continuous curves and **zero** Lie-group geodesics $\exp(t X)$ connect $I_2$ to $-I_2$).
   - In compact Euclidean $\mathrm{SO}_4(F)$, reflections have $\det(r_u) = -1 \notin \mathrm{SO}_4(F)$, and the $B_4$-Coxeter rotation $R_{\mathrm{Cox}} = \bigl(r_{e_0} r_{e_0+e_1}\bigr)\bigl(r_{e_1+e_2} r_{e_2+e_3}\bigr) = P_1 P_2 \in \mathrm{SO}_4(\mathbb{Z})$ ($R_{\mathrm{Cox}}^4 = -I_4$, eigenangles $\frac{\pi}{4}, \frac{3\pi}{4}$, possessing a *unique* minimal Riemannian geodesic in $\mathrm{SO}(4; \mathbb{R})$) has minimal reflection count $\ell_{\mathrm{ref}}(R_{\mathrm{Cox}}) = 4$ whose planar factors **fail to commute** ($P_1 P_2 \neq P_2 P_1$, angle sum $\frac{7\pi}{6} \gt \pi$), and over $F = \mathbb{Q}$ preserves **no** $2$-dimensional subspace of $\mathbb{Q}^4$ whatsoever.

4. **Positive Non-Vacuity & Cartan–Dieudonné Theorems:**
   For every non-degenerate quadratic space $\bigl(F^n, Q\bigr)$ formalized in dimensions $2$ and $4$ over any formally real field $F$, every reflection $r_u$ ($Q(u) \neq 0$) is an involutive isometry with $\det(r_u) = -1$, every reflection word $g = r_1 \cdots r_k$ satisfies $\det(g) = (-1)^k$ and $\mathrm{im}(I - g) \subseteq \mathrm{span}_F(u_1, \dots, u_k)$ ($\mathrm{rank}(I - g) \le k$), and Euclidean $\mathrm{O}_2(F)$ satisfies the complete classification $\ell_{\mathrm{ref}}(g) \in \{0, 1, 2\}$.

---

## Package Structure & Verification Artifacts

- `SOURCE.md` — Original bilingual problem statement (unmodified).
- `main.tex` / `main.pdf` — Complete mathematical paper proving the positive parity/rank theorems, all refutations across signatures and characteristics, and the formal verification correspondence.
- `verify.py` — Standalone Python 3.12 symbolic verification script using exact `fractions.Fraction` and $\mathbb{F}_2$ arithmetic (zero floating-point approximations).
- `lean/` — Core Lean `v4.19.0` formalization (`moreLeanArgs = ["-DwarningAsError=true"]`, zero external dependencies, zero `sorry`/`admit`/`native_decide`, zero custom `axiom` declarations):
  - `Conjecture00000007609/FieldFoundation.lean` — `FormallyRealField F`, pure-`Bool` reflective polynomial normalizer `RExpr`, constructive rational witness `QField`, and infinite-descent proof `QField.no_sqrt_two`.
  - `Conjecture00000007609/PlanarAndLorentz.lean` — $2$D Euclidean & Lorentzian reflections, parity law `reflCount2_parity_iff`, $\mathrm{O}_2(F)$ classification, `so2_infinite_reflection_counting`, `so2_infinite_distinct_angles_same_minReflCount`, and `lorentz_negOne_minRefl_two_yet_not_geodesic`.
  - `Conjecture00000007609/FourDimCounterexamples.lean` — $4$D Sylvester rank-$1$ determinant perturbation `Mat4.det4Cols_pert`, parity & span bound `reflDecomp4_sub_in_span`, `so4_same_trace_and_chord_diff_minReflCount`, `scherk_null_rotation_rank_two_minRefl_four`, `coxeter_so4_noncomm_and_minRefl_four`, `rcox_no_2d_invariant_subspace_QField`, and `dieudonne_f2_counterexample`.
  - `Conjecture00000007609.lean` — Root master theorems `cartan_dieudonne_positive_theorems`, `conjecture_00000007609_refuted`, and `conjecture_00000007609_ground_witness`.
- `verification/` — Build and verification logs (`lake-build.log`, `lean-axioms.log`, `lean-version.log`, `pdf-build.log`, `python-verify.log`, `SELF_REVIEW.md`).
