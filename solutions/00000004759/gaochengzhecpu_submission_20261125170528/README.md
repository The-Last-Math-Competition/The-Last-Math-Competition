# Conjecture 00000004759 — Disproof and Complete Structural Resolution

## Source Statement

> **English.** Definition: Operator-valued free probability is the free theory with values in a subalgebra. Conjecture: The convolution recursion is always given by the weighted count of nested noncrossing partitions, and polynomials of depth at most three are computable. (nested recursion of operator-valued convolution)
>
> **中文。** 定义：算子值自由概率指取值于子代数的自由理论。猜想：卷积递推恒由嵌套非交叉分拆的加权计数给出；且深度三内多项式可算。（算子值卷积嵌套递推）

## Verdict: **Disproved (False as Stated, with Exact Structural Characterization of Both Clauses)**

Conjecture `00000004759` is **false**: its universal first clause (*"The convolution recursion is always given by the weighted count of nested noncrossing partitions"* / *"卷积递推恒由嵌套非交叉分拆的加权计数给出"*) fails across every mathematical formalization of a weighted partition count over noncrossing partitions $NC(n)$. In genuine operator-valued free probability $\bigl(\mathcal{A}, E \colon \mathcal{A} \to B, B\bigr)$ (Voiculescu 1995; Speicher 1998), nested blocks do **not** contribute scalar weights or factorized block products; instead, inner $B$-valued expectations sit *inside* the arguments of outer $B$-bimodule multilinear maps via nested operator composition.

### 1. Disproof of Clause 1 Across All Weighted-Count Formalizations

On the concrete two-generator full Fock space realization $\mathcal{A} = M_2(\mathcal{F})$ over $B = M_2(\mathbb{Z})$ (with entrywise vacuum conditional expectation $E$ and proved all-order Voiculescu $B$-freeness):

1. **Failure of single-variable moment/cumulant partition weightings (already at $n = 3$, nesting depth $2$):**
   Let $X = I_2 \otimes s_0$ and $\tilde{X} = \sigma_x \otimes s_0$, where $\sigma_x = \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}$. Because $\sigma_x^2 = I_2$, $X$ and $\tilde{X}$ have **identical** un-inserted power moments $E(X^k) = E(\tilde{X}^k)$ and un-inserted cumulants $\kappa_k^X(I_2, \dots, I_2) = \kappa_k^{\tilde{X}}(I_2, \dots, I_2)$ for **all** $k \in \mathbb{N}$.
   - With deterministic $B$-free partner $Y_{\det} = E_{11} \in B$, additive convolution agrees at $n = 1, 2$ (depth $1$, where $NC(1)$ and $NC(2)$ have zero nested partitions) and **fails at $n = 3$** (the minimal $n$ with a nested partition $\{\{1,3\},\{2\}\} \in NC(3)$):
     $$E\bigl((X + E_{11})^3\bigr) = \begin{pmatrix} 4 & 0 \\ 0 & 0 \end{pmatrix} \neq \begin{pmatrix} 3 & 0 \\ 0 & 1 \end{pmatrix} = E\bigl((\tilde{X} + E_{11})^3\bigr),$$
     while multiplicative convolution fails already at $n = 2$: $E\bigl((X E_{11})^2\bigr) = E_{11} \neq 0 = E\bigl((\tilde{X} E_{11})^2\bigr)$.
   - With strictly centered semicircular $B$-free partner $Y_{\mathrm{semi}} = E_{11} \otimes s_1$ ($E(X) = E(\tilde{X}) = E(Y_{\mathrm{semi}}) = 0$), additive convolution agrees at $n = 1, 2, 3, 5$ and **fails at $n = 4$** (depth $2$) and **$n = 6$** (depth $3$):
     $$E\bigl((X + Y_{\mathrm{semi}})^4\bigr) = \begin{pmatrix} 8 & 0 \\ 0 & 2 \end{pmatrix} \neq \begin{pmatrix} 7 & 0 \\ 0 & 3 \end{pmatrix} = E\bigl((\tilde{X} + Y_{\mathrm{semi}})^4\bigr),$$
     $$E\bigl((X + Y_{\mathrm{semi}})^6\bigr) = \begin{pmatrix} 40 & 0 \\ 0 & 5 \end{pmatrix} \neq \begin{pmatrix} 30 & 0 \\ 0 & 12 \end{pmatrix} = E\bigl((\tilde{X} + Y_{\mathrm{semi}})^6\bigr).$$
   - Restricting to the **commutative** diagonal subalgebra $D_2(\mathbb{Z}) \cong \mathbb{Z}^2 \subseteq M_2(\mathbb{Z})$ preserves $D_2(\mathbb{Z})$-freeness of both pairs, proving that commutativity of $B$ alone is insufficient without centrality ($X b = b X$).

2. **Universal No-Go Theorem against un-nested block-evaluation weightings (even given all $B$-insertions and full covariance map $\eta_{\mathrm{swap}}$):**
   Let $X_{\mathrm{swap}} \in M_2(\mathcal{F})$ be the self-adjoint operator with covariance $\eta_{\mathrm{swap}}(B) = E(X_{\mathrm{swap}} B X_{\mathrm{swap}}) = \mathrm{diag}(b_{22}, b_{11})$.
   - At $\bigl(B_1, B_2, B_3\bigr) = \bigl(E_{12}, E_{11}, E_{21}\bigr)$, we have $B_1 B_2 B_3 = 0$, $\eta_{\mathrm{swap}}(B_1) = \eta_{\mathrm{swap}}(B_3) = 0$, and every linear combination of all $13$ order-preserving un-nested trilinear operators has $\bigl(2,2\bigr)$-entry $0$, whereas $\mu_4^{X_{\mathrm{swap}}}(E_{12}, E_{11}, E_{21}) = \eta_{\mathrm{swap}}\bigl(E_{12}\eta_{\mathrm{swap}}(E_{11})E_{21}\bigr) = E_{22} \neq 0$.
   - Across **all $6 \times 13 = 78$** permuted single-layer trilinear operators $\{U_{\sigma, p}\}$ (allowing arbitrary permutations $\sigma \in S_3$ of $\bigl(B_1, B_2, B_3\bigr)$), their rational span has dimension $32$, and an explicit $12$-term $\pm 1$ linear functional $\Phi$ satisfies $\Phi(U_{\sigma, p}) = 0$ for all $78$ operators while $\Phi\bigl(\eta_{\mathrm{swap}}(B_1 \eta_{\mathrm{swap}}(B_2) B_3)\bigr) = \Phi(\mu_4^{X_{\mathrm{swap}}}) = 1 \neq 0$.
   - Moreover, for $B$-free $X_1 = E_{11} \otimes s_0$ and $Y_1 = E_{22} \otimes s_1$ at $\bigl(E_{21}, E_{11}, E_{12}\bigr)$, both pure fourth moments and both flat pairings vanish identically, yet the fourth convolution moment equals $E_{22} \neq 0$.

### 2. Central-Commutative Boundary and Resolution of Clause 2 (Depth/Degree $\le 3$ Computability)

1. **Exact Central-Commutative Factorization Boundary:**
   Over any commutative ring $B$, whenever all block cumulants act centrally as $\kappa_{r+1}(u_1, \dots, u_r) = u_1 \cdots u_r \, c(r + 1)$, Speicher's nested evaluation collapses to the weighted partition product $\bigl(\prod_{i=1}^{n-1} b_i\bigr) \prod_{V \in \pi} c(|V|)$.

2. **Computability of Polynomials of Depth/Degree at Most Three:**
   - **Given genuine $B$-multilinear moment oracles $\mu_k^X, \mu_k^Y \colon B^{k-1} \to B$ (Positive Theorem):** Over *every* abstract operator-valued probability space $\bigl(\mathcal{A}, B, \iota, E\bigr)$ and *every* $B$-free pair $\bigl(X, Y\bigr)$, all polynomials $P \in B\langle X, Y \rangle$ of degree $\le 3$ (via the universal identity $E(X \iota(b_1) Y \iota(b_2) X) = E(X \iota(b_1 E(Y) b_2) X)$) and all convolution/mixed moments of nesting depth $\le 3$ ($n \le 6$, $|NC(6)| = 132$, including the depth-$3$ rainbow pairing $\{\{1,6\},\{2,5\},\{3,4\}\}$) are constructively computable by Speicher's nested recursion.
   - **Given only un-inserted moments $\{E(X^k), E(Y^k)\}_{k \ge 1}$ (Sharp Failure at Degree $3$):** Polynomials of degree $\le 2$ ($E(X+Y)$, $E(XY) = E(X)E(Y)$, $E((X+Y)^2)$) are computable, whereas $\bigl(X + Y\bigr)^3$ is already underdetermined.

## Package Contents

- `SOURCE.md` — Original bilingual conjecture statement (unmodified).
- `main.tex`, `main.pdf` — Self-contained mathematical paper with complete proofs and summary tables.
- `lean/` — Core Lean `v4.19.0` formalization (`zero` external dependencies, `-DwarningAsError=true`, zero `sorry`/`admit`/`native_decide`/custom axioms):
  - `Conjecture00000004759/Basic.lean` — `AssocRing`, `CommAssocRing`, `OpValProbSpace`, `IsBFree`, `isBFree_iotaSubalg`, `exp_XY_bfree`, `exp_add_sq_bfree`, and `exp_XYX_bfree`.
  - `Conjecture00000004759/FockModel.lean` — `Mat2`, `FockOp`, `scalar_isBFree`, `mat2FockSpace`, and all-order $B$-freeness `mat2Fock_isBFree`.
  - `Conjecture00000004759/Counterexamples.lean` — `all_power_moments_eq`, `conv_det_n3_ne`, `mul_conv_det_n2_ne`, `conv_semi_n4_ne`, `conv_semi_n6_ne`, and `no_uninserted_moment_convolution_recursion`.
  - `Conjecture00000004759/NoUnnestedWeightedCount.lean` — `opXswap_covariance`, `phiOrd_comb_id_zero`, `no_unnested_weighted_count_all78`, and `pure_moments_vanish_yet_conv_nonzero`.
  - `Conjecture00000004759/NestedRecursion.lean` & `Conjecture00000004759.lean` — `nc_catalan_and_depth_counts`, `central_commutative_weighted_count`, `poly_deg_le_3_universal_soundness`, `speicher_depth3_n6_verified`, and `conjecture_00000004759_resolution`.
- `verify.py` — Standalone Python 3.12 verification suite checking $NC(n)$ bijections and depth histograms ($n \le 7$), Fock and $8$D Rademacher counterexamples, the $78$-operator linear span, and Speicher's general nested recursion up to $n = 6$.
- `verification/` — Recorded verification logs (`lake-build.log`, `lean-axioms.log`, `lean-version.log`, `pdf-build.log`, `python-verify.log`, `SELF_REVIEW.md`).
