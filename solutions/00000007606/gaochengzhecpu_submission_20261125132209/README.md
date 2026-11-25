# Conjecture 00000007606 — Disproof and Repaired Spin Double-Cover Analysis

## Verdict: **FALSE** (as stated; true after repairing rotor definition, target group, and field/signature hypotheses)

### Source Statement (`SOURCE.md`)

> **English.** Definition: Rotors as unit elements of the even subalgebra. Conjecture: The kernel of the double cover of the spin group over the orthogonal group is two; and the realization of the cover is the adjoint map. (adjoint-realized kernel-two double cover)
>
> **中文。** 定义：转子为偶子代数的单位元结构。猜想：旋群到正交群的双覆盖的核为二；且覆盖的实现为 Adjun 映射。（双覆盖核二伴随实现）

---

## Summary of Mathematical Resolution

As written, Conjecture `00000007606` is **false** on three independent mathematical grounds:

1. **Target Group Error — $\mathrm{Spin}\bigl(V, Q\bigr)$ Covers $\mathrm{SO}\bigl(V, Q\bigr)$, Never the Full Orthogonal Group $\mathrm{O}\bigl(V, Q\bigr)$ ($n \ge 1$, $\mathrm{char}\bigl(K\bigr) \ne 2$):**
   In every nondegenerate quadratic space $\bigl(V, Q\bigr)$ of dimension $n \ge 1$ over a field $K$ with $\mathrm{char}\bigl(K\bigr) \ne 2$, every even Clifford element $x \in \mathrm{Cl}\bigl(V, Q\bigr)^+$ commutes with the pseudoscalar $\omega = e_1 \cdots e_n$. Consequently, whenever an invertible even element $x \in \bigl(\mathrm{Cl}\bigl(V, Q\bigr)^+\bigr)^\times$ stabilizes $V$ under the ordinary adjoint map $\mathrm{Ad}_x\bigl(v\bigr) = x v x^{-1}$, it satisfies $x \omega x^{-1} = +\omega$, forcing $\det\bigl(\mathrm{Ad}_x|_V\bigr) = +1$. Hence no hyperplane reflection $r_u \in \mathrm{O}\bigl(V, Q\bigr) \setminus \mathrm{SO}\bigl(V, Q\bigr)$ (which has $\det\bigl(r_u\bigr) = -1$) lies in the image of $\mathrm{Spin}\bigl(V, Q\bigr)$ or $\bigl(\mathrm{Cl}\bigl(V, Q\bigr)^+\bigr)^\times$. Moreover, when $n = 2m + 1$ is **odd**, $\omega$ is central in the *entire* Clifford algebra $\mathrm{Cl}\bigl(V, Q\bigr)$, so **not even $\mathrm{Pin}\bigl(V, Q\bigr)$ or $\mathrm{Cl}\bigl(V, Q\bigr)^\times$** can cover $\mathrm{O}\bigl(V, Q\bigr)$ via $\mathrm{Ad}_x\bigl(v\bigr) = x v x^{-1}$; covering $\mathrm{O}\bigl(V, Q\bigr)$ requires $\mathrm{Pin}\bigl(V, Q\bigr)$ together with Atiyah–Bott–Shapiro's **twisted** adjoint map $\widetilde{\mathrm{Ad}}_x\bigl(v\bigr) = \alpha\bigl(x\bigr) v x^{-1}$.

2. **Rotor Definition Error — "Unit Elements of the Even Subalgebra" Fails Under Both Readings:**
   - **Algebraic units $\bigl(\mathrm{Cl}\bigl(V, Q\bigr)^+\bigr)^\times$:** Every nonzero scalar $c \cdot 1$ ($c \in K^\times$) belongs to $\bigl(\mathrm{Cl}\bigl(V, Q\bigr)^+\bigr)^\times$ and acts trivially under $\mathrm{Ad}$, so the kernel contains $K^\times$ (infinite over $\mathbb{Q}$ and $\mathbb{R}$, of cardinality $\gt 2$ whenever $|K| \gt 3$). Worse, for $n \ge 4$, generic invertible even elements fail even to preserve $V$: in $\mathrm{Cl}_{4,0}\bigl(K\bigr)^+$, $x = 1 + 2 e_{1234}$ has exact inverse $-\frac{1}{3}\bigl(1 - 2 e_{1234}\bigr)$, yet
     $$\mathrm{Ad}_x\bigl(e_1\bigr) = -\frac{5}{3} e_1 + \frac{4}{3} e_{234} \notin V.$$
   - **Unit-norm even elements $\{x \in \mathrm{Cl}\bigl(V, Q\bigr)^+ : x \widetilde{x} = 1\}$:** By the Chevalley–Porteous phenomenon at $n = 6$ (where $\dim \mathrm{U}\bigl(4\bigr) = 16 \gt 15 = \dim \mathrm{Spin}\bigl(6\bigr)$), unit Clifford norm inside $\mathrm{Cl}^+$ still fails to preserve $V$: in $\mathrm{Cl}_{6,0}\bigl(K\bigr)^+$, $x = \frac{3}{5} + \frac{4}{5} e_{123456}$ satisfies $x \widetilde{x} = \widetilde{x} x = 1$, yet
     $$\mathrm{Ad}_x\bigl(e_1\bigr) = -\frac{7}{25} e_1 - \frac{24}{25} e_{23456} \notin V.$$

3. **Characteristic $2$ and Indefinite Signature Obstructions:**
   - Over $\mathrm{char}\bigl(K\bigr) = 2$ (e.g., $\mathbb{F}_2$), $+1 = -1$ in $\mathrm{Cl}\bigl(V, Q\bigr)$, collapsing $\{\pm 1\}$ to a singleton of cardinality $1 \ne 2$.
   - Over ordered fields in indefinite Lorentzian signature $\bigl(1, 1\bigr)$, unit-norm even rotors $\{x \in \mathrm{Cl}_{1,1}^+ : x \widetilde{x} = 1\} = \mathrm{Spin}^+\bigl(1, 1\bigr)$ satisfy $\bigl(\mathrm{Ad}_x\bigr)_{11} = a^2 + b^2 \ge 1 \gt 0$, covering only the orthochronous identity component $\mathrm{SO}^+\bigl(1, 1\bigr)$ and missing $-I_2 \in \mathrm{SO}\bigl(1, 1\bigr)$ as well as $\mathrm{O}\bigl(1, 1\bigr) \setminus \mathrm{SO}\bigl(1, 1\bigr)$.

4. **Repaired Classical Positive Theorem ($\mathrm{Spin}\bigl(n\bigr) \twoheadrightarrow \mathrm{SO}\bigl(n\bigr)$):**
   Defining $\mathrm{Spin}\bigl(V, Q\bigr) = \{x \in \mathrm{Cl}\bigl(V, Q\bigr)^+ : x V x^{-1} \subseteq V \text{ and } x \widetilde{x} = \widetilde{x} x = 1\}$, for *all* $n \ge 0$ and all nondegenerate signatures over any field with $\mathrm{char}\bigl(K\bigr) \ne 2$, $\mathrm{Ad} : \mathrm{Spin}\bigl(V, Q\bigr) \to \mathrm{SO}\bigl(V, Q\bigr)$ has exact kernel $\{+1, -1\}$ of cardinality $2$; and over $\mathbb{R}$ with positive-definite $Q$ ($n \ge 1$), $\mathrm{Ad} : \mathrm{Spin}\bigl(n\bigr) \twoheadrightarrow \mathrm{SO}\bigl(n\bigr)$ is a **surjective** $2$-to-$1$ double cover.

---

## Package Structure

- `SOURCE.md` — Original bilingual problem statement (unmodified).
- `main.tex` / `main.pdf` — Complete mathematical paper proving both the classical positive theorem and all three refutations.
- `verify.py` — Standalone Python 3 exact computational verification suite across $\mathrm{Cl}_{1,0}$ through $\mathrm{Cl}_{6,0}$, $\mathrm{Cl}_{1,1}$, and $\mathbb{F}_2$.
- `lean/` — Zero-dependency **Core Lean 4.19.0** formalization (`leanprover/lean4:v4.19.0`, `-DwarningAsError=true`, zero `sorry` / `native_decide` / custom axioms):
  - `Conjecture00000007606/Field.lean` — Self-contained field hierarchy (`FieldK`, `FieldCharNeTwo`, `OrderedFieldK`, `EuclideanFieldK`) and concrete instances `F2` ($\mathbb{F}_2$), `RatQ` ($\mathbb{Q}$), and `QSqrt2` ($\mathbb{Q}\bigl(\sqrt{2}\bigr)$).
  - `Conjecture00000007606/Clifford.lean` — Recursive $2^n$-dimensional Clifford algebra `Cl K sig` for arbitrary dimension $n$ and signature, proving `Cl.adjoint_preserves_quadForm`, `Cl.even_unit_never_covers_orthogonal_reflection`, `Cl.odd_dim_no_clifford_unit_covers_reflection`, and the all-dimension `Cl.spin_adjoint_kernel_eq_pm_one`.
  - `Conjecture00000007606/LowDimCovers.lean` — Complete $\mathrm{Spin}_1 \twoheadrightarrow \mathrm{SO}_1$ and $\mathrm{Spin}_2\bigl(E\bigr) \twoheadrightarrow \mathrm{SO}_2\bigl(E\bigr)$ double covers, rational Pythagorean fibers, rational spinor-norm obstruction on $90^\circ$ rotation and lift over $\mathbb{Q}\bigl(\sqrt{2}\bigr)$, infinite scalar kernel in $\bigl(\mathrm{Cl}_{2,0}\bigl(\mathbb{Q}\bigr)^+\bigr)^\times$, $\mathbb{F}_2$ collapse, and Lorentzian $\mathrm{Cl}_{1,1}$ obstruction.
  - `Conjecture00000007606/HigherDimCounterexamples.lean` — Formal proofs that $1 + 2 e_{1234} \in \bigl(\mathrm{Cl}_{4,0}^+\bigr)^\times$ and $\frac{3}{5} + \frac{4}{5} e_{123456} \in \{x \in \mathrm{Cl}_{6,0}^+ : x \widetilde{x} = 1\}$ fail to preserve $V$.
- `verification/` — Complete build, axiom-audit, version, PDF, Python, and self-review logs.
