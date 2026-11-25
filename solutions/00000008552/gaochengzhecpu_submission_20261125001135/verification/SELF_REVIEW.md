# Self-Review & Semantic Audit (`00000008552`)

## 1. Conjecture Statement Fidelity
- **Source (`SOURCE.md`):** Byte-for-byte identical to `conjectures/00000008552.md`.
- **Statement:** *"Definition: Order polynomials count order-preserving maps. Conjecture: The number of order-preserving maps of a chain product lattice is an explicit product of multinomial coefficients; the product is of MacMahon type. (order-preserving map counting)"*
- **Verdict:** **DISPROVED (FALSE)** across all standard mathematical interpretations.

## 2. Semantic Coverage Audit (No Convention Escape Hatches)
To guarantee that no interpretation of "number of order-preserving maps of a chain product lattice", "product of multinomial coefficients", or "MacMahon type" is left open, `lean/Main.lean`, `main.tex`, and `verify.py` formalize and refute **all four mathematical readings**:

1. **Order-Polynomial / MacMahon Polynomial Reading (`OrderPolyCounts` & Hierarchy):**
   - `chainProdLattice dims` formalizes arbitrary direct products of finite chains $C_{a_1} \times \dots \times C_{a_d}$ with proved partial-order and lattice axioms (`inf_le_left`, `inf_le_right`, `le_inf`, `le_sup_left`, `le_sup_right`, `sup_le`).
   - `HasCard α n` is defined via a constructive bijection `Equiv α (Fin n)` with proved cardinality uniqueness `HasCard.unique : HasCard α m → HasCard α n → m = n`.
   - Multinomial coefficients are defined recursively with proved factorial specification `multinomial_spec : multinomial ks * prodFact ks = fact (listSum ks)`.
   - Three nested formula classes are formalized (`pure_imp_macmahon`, `macmahon_imp_rationalLinear`):
     - `IsPureMultinomialPolyProd`: finite products of multinomial coefficients with linear top entries $a_r m + b_r$.
     - `IsMacMahonMultinomialQuotient`: quotients of finite products of polynomial multinomial coefficients (capturing MacMahon's 2-chain box formula $\prod_{i=1}^a \frac{\binom{m+b+i-2}{b}}{\binom{b+i-1}{b}}$).
     - `IsRationalLinearRatio`: functions eventually equal on $m \ge M_0$ to a rational constant times a quotient of products of integer linear factors $(\alpha_r m + \beta_r)$.
   - For $L = C_2 \times C_2 \times C_2$ (`dims = [2, 2, 2]`), `omegaCube_card` proves `HasCard (OrderHom (C_2^3) C_m) (omegaCube m)` for **all** $m \in \mathbb{N}$, `omegaCube_poly_identity` proves $1680 \cdot \Omega(C_2^3, m) = m(m+1)(m+2)(m+3)(2m^4 + 12m^3 + 25m^2 + 21m + 10)$, `homQuartic_sos_identity` / `homQuartic_pos` prove $8 Q_{\mathrm{hom}}(g, z) = (4z^2 + 12gz + 7g^2)^2 + 31g^4 \ge 31 > 0$ for all $g \ne 0$, and `conjecture_00000008552_order_polynomial_disproved` refutes all three hierarchy levels.

2. **Pointwise / Fixed-Parameter Multinomial & Bounded Quotient Reading (`conjecture_00000008552_pointwise_disproved`):**
   - At $L = C_2 \times C_2 \times C_2$ and $m = 4$, `omega_222_at_4` proves $|\operatorname{Hom}_{\le}(C_2^3, C_4)| = 887$, and `isPrime_887` proves $887$ is prime.
   - Consequently, $887$ admits no nontrivial integer product $a \cdot b$ ($a, b > 1$), equals no finite product of genuine (non-edge) multinomial coefficients (`no_genuine_multinomial_prod_eq_887`), and equals no quotient of multinomial products with top entries $< 887$ (`no_bounded_multinomial_quotient_of_prime_dvd`, proved via Gauss's elementary Euclid's lemma `prime_dvd_mul`).

3. **Naive $d$-Dimensional MacMahon Rank-Box Generalization (`naive_macmahon_box_disproved`):**
   - Proves that $\prod_{x \in L} \frac{m + \operatorname{rk}(x)}{1 + \operatorname{rk}(x)}$ fails even to be an integer both on $C_2^3$ at $m = 3$ ($\frac{144000}{864} = \frac{500}{3} \ne 168$) and on $C_2^4$ at $m = 2$ ($\frac{500}{3} \ne 168 = M(4)$, via `omega_2222_at_2`).

4. **Order-Preserving Endomorphism Reading (`conjecture_00000008552_endomorphism_disproved`):**
   - Using universal product decomposition (`orderHomConsCodomainEquiv`) and solid-partition box conjugation (`orderHomChainSwapEquiv`), `orderEnd_223_card` proves $|\operatorname{Hom}_{\le}(C_2 \times C_2 \times C_3,\, C_2 \times C_2 \times C_3)| = 50 \cdot 50 \cdot 887 = 2{,}217{,}500 = 2^2 \cdot 5^4 \cdot 887$, whose prime factor $887 \gg |L| = 12$ refutes any bounded multinomial product or quotient.

## 3. Non-Vacuity and Positive Witnesses
- `omegaChain2_isPureMultinomial`: proves $\Omega(C_2, m) = \binom{m+1}{2}$ satisfies `IsPureMultinomialPolyProd`.
- `macmahon_holds_for_two_chains_witness`: proves `[2, 2]` ($C_2 \times C_2$) satisfies `ValidChainDims [2, 2]`, `OrderPolyCounts [2, 2] omegaSq` (for all $m \ge 1$), `IsMacMahonMultinomialQuotient omegaSq` ($\Omega(C_2^2, m) = \frac{\binom{m+1}{2}\binom{m+2}{2}}{\binom{2}{2}\binom{3}{2}}$), and `IsRationalLinearRatio omegaSq`.

## 4. Technical & Build Hygiene Audit
- **Lean Toolchain:** `leanprover/lean4:v4.19.0` (Core Lean only, zero external packages).
- **Compiler Flags:** `moreLeanArgs = ["-DwarningAsError=true"]`; zero warnings or errors.
- **Forbidden Constructs:** Zero `sorry`, `admit`, `native_decide`, custom `axiom`, `unsafe`, `extern`, or `implemented_by`.
- **Kernel Axioms (`lean-axioms.log`):** Every main theorem depends solely on standard Lean kernel axioms (`[propext, Quot.sound]` and `[propext, Classical.choice, Quot.sound]`).
- **LaTeX (`main.tex` -> `main.pdf`):** Compiled twice with `pdflatex -interaction=nonstopmode -halt-on-error main.tex`; zero errors, zero undefined references, zero overfull/underfull `\hbox`es.
- **Python (`verify.py`):** Independently verifies brute-force map counts, DP counts, polynomial identities, quartic irreducibility over $\mathbb{Q}[m]$, Pascal-simplex bounds, naive MacMahon box ratios, and endomorphism counts; exits with code `0`.
- **Cleanliness:** `.lake/`, `main.aux`, `main.log`, `main.out`, and `__pycache__/` removed from `package/`.
