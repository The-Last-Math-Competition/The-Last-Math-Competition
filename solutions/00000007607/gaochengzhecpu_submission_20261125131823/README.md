# Conjecture 00000007607 — Rotor Logarithm-Sum Angle Additivity

## Verdict: **FALSE** in General ($n \ge 3$); **TRUE** for Coplanar Rotations ($n = 2$)

Conjecture `00000007607` states (in parallel English and Chinese formulations in `SOURCE.md`):

> **Definition:** The exponential law of rotor formulas. **Conjecture:** The logarithm sum of generators gives the rotation angle; the spectrum of the sum is angle additivity; and the verification of the angle additivity is the Lie bracket identity. (*rotor logarithm-sum angle additivity*)

We prove that all three clauses of Conjecture `00000007607` are **false in general across every Euclidean dimension $n \ge 3$**, while **identically true in dimension $n = 2$** (and more generally if and only if two nontrivial simple rotors share the same oriented $2$-plane $u_1 = u_2$).

---

## Mathematical Resolution Summary

In the Euclidean Clifford (geometric) algebra $\mathrm{Cl}_{n,0}(\mathbb{R})$, a simple rotor rotating an oriented unit $2$-plane $u \in \bigwedge^2 \mathbb{R}^n$ ($u^2 = -1$) by angle $\theta \in (0, \pi]$ is given by Euler's rotor formula

$$R(\theta, u) = \exp\!\left(-\frac{\theta}{2} u\right) = \cos\frac{\theta}{2} - \sin\frac{\theta}{2}\, u, \qquad B = -\frac{\theta}{2} u \in \mathfrak{spin}(n).$$

The geometric product of any two bivectors $B_1, B_2 \in \bigwedge^2 \mathbb{R}^n$ decomposes canonically by grade as

$$B_1 B_2 = -\langle B_1, B_2 \rangle_{\mathrm{Euc}} + \frac{1}{2}[B_1, B_2] + B_1 \wedge B_2.$$

Each grade component governs a distinct aspect of rotor composition and angle additivity:

1. **Positive Planar Regime ($n = 2$, $\mathrm{Spin}(2) \subset \mathrm{Cl}_{2,0}^+ \cong \mathbb{C}$):**
   Since $\dim \bigwedge^2 \mathbb{R}^2 = 1$ and $\bigwedge^4 \mathbb{R}^2 = \{0\}$, every pair of bivectors $B_1 = -\frac{\theta_1}{2} e_{12}$, $B_2 = -\frac{\theta_2}{2} e_{12}$ satisfies $[B_1, B_2] = 0$ identically, $\exp(B_1)\exp(B_2) = \exp(B_1 + B_2) = R(\theta_1 + \theta_2, e_{12})$, and $\bigl(B_1 + B_2\bigr)^2 = -\frac{(\theta_1 + \theta_2)^2}{4}$, confirming all three clauses when $n = 2$ (witnessed over $\mathbb{Q}$ by non-central Pythagorean rotors $R_1 = \frac{4}{5} - \frac{3}{5}e_{12}$ and $R_2 = \frac{12}{13} - \frac{5}{13}e_{12}$ with $R_1 R_2 = \frac{33}{65} - \frac{56}{65}e_{12}$).

2. **Three-Way Separation & Exact Characterizations in $n = 3$ ($\mathrm{Spin}(3) \subset \mathrm{Cl}_{3,0}^+ \cong \mathbb{H}$):**
   - **Master Identities:** For unit bivectors $u_1, u_2 \in \mathfrak{spin}(3)$, $R_k = c_k - s_k u_k$, and $B_k = -a_k u_k$,
     $$2\bigl(\langle R_1 R_2 \rangle_0 - (c_1 c_2 - s_1 s_2)\bigr) = s_1 s_2 \|u_1 - u_2\|_{\mathrm{Euc}}^2, \qquad (a_1 + a_2)^2 - \|B_1 + B_2\|_{\mathrm{Euc}}^2 = a_1 a_2 \|u_1 - u_2\|_{\mathrm{Euc}}^2,$$
     and $\|[B_1, B_2]\|_{\mathrm{Euc}}^2 = 4\bigl(\|B_1\|_{\mathrm{Euc}}^2 \|B_2\|_{\mathrm{Euc}}^2 - \langle B_1, B_2 \rangle_{\mathrm{Euc}}^2\bigr)$. Thus for nontrivial rotors ($s_1, s_2 \neq 0$, $a_1, a_2 \neq 0$), $[u_1, u_2] = 0 \iff u_1 = \pm u_2$, while both rotor composition angle additivity and generator-sum spectral angle additivity hold **if and only if** $u_1 = u_2$ (with strict inequality $\Theta \lt \theta_1 + \theta_2$ and $2\|B_1 + B_2\|_{\mathrm{Euc}} \lt \theta_1 + \theta_2$ whenever $\theta_1, \theta_2 \in (0, \pi]$ and $u_1 \neq u_2$).
   - **Orthogonal $90^\circ$ Counterexample ($\theta_1 = \theta_2 = \frac{\pi}{2}$):** Taking $R_1 = \frac{1 - e_{12}}{\sqrt{2}}$ and $R_2 = \frac{1 - e_{23}}{\sqrt{2}}$ yields $R_1 R_2 = \frac{1 - e_{12} - e_{23} + e_{13}}{2}$ with $\bigl(R_1 R_2\bigr)^3 = -1$, permuting $\bigl(e_1, e_2, e_3\bigr) \mapsto \bigl(e_2, e_3, e_1\bigr)$ by composite angle $\Theta = \frac{2\pi}{3} = 120^\circ$, whereas the generator-sum spectral angle is $2\|B_1 + B_2\|_{\mathrm{Euc}} = \frac{\pi}{\sqrt{2}} \approx 127.28^\circ$, the naive angle sum is $\theta_1 + \theta_2 = \pi = 180^\circ$, $\exp(B_1)\exp(B_2) \neq \exp(B_1 + B_2)$, and $[e_{12}, e_{23}] = 2e_{13} \neq 0$ is the Baker–Campbell–Hausdorff obstruction.
   - **Pure Integer & Rational Counterexamples:** $180^\circ$ rotors $R_1 = -e_{12}, R_2 = -e_{23}$ satisfy $R_1 R_2 = e_{13} \neq \pm 1$ ($\Theta = \pi \neq 2\pi$); rational generators $B_1 = -\frac{3}{2}e_{12}, B_2 = -2e_{23}$ satisfy $\|B_1 + B_2\|_{\mathrm{Euc}}^2 = \frac{25}{4} \neq \frac{49}{4}$ (spectral angle $5 \neq 3 + 4 = 7$).

3. **Higher-Dimensional Commuting Non-Simplicity Obstruction ($n = 4$ and All $n \ge 3$):**
   - In $\mathrm{Cl}_{4,0}^+$, disjoint orthogonal planes $B_1 = -a_1 e_{12}$ and $B_2 = -a_2 e_{34}$ ($a_1, a_2 \neq 0$) **commute** ($[B_1, B_2] = 0$, so $\exp(B_1)\exp(B_2) = \exp(B_1 + B_2)$ holds), **yet** $\bigl(B_1 + B_2\bigr)^2 = -(a_1^2 + a_2^2) + 2a_1 a_2 e_{1234}$ has a nonzero grade-$4$ wedge component, producing a double rotation on $\mathbb{R}^4$ with vector spectrum $\{\pm i\theta_1, \pm i\theta_2\}$ rather than single-angle additivity. Thus vanishing of the Lie bracket is not even sufficient when $n \ge 4$.
   - Canonical embedding $\mathbb{R}^3 \hookrightarrow \mathbb{R}^n$ extends all three failures uniformly to **every** dimension $n \ge 3$.

---

## Package Contents

- `SOURCE.md` — Unmodified problem statement (`00000007607`).
- `main.tex`, `main.pdf` — Self-contained mathematical paper proving all characterizations, positive planar results, and counterexamples.
- `lean/` — Zero-dependency Core Lean `4.19.0` formalization (`-DwarningAsError=true`, zero `sorry`/`admit`/`native_decide`/custom `axiom`):
  - `Conjecture00000007607/RingBase.lean` — `CommRing`, kernel-verified polynomial normalizer `Poly`, and `comm_ring` tactic.
  - `Conjecture00000007607/Ring.lean` — `StrictOrderedCommRing`, sum-of-squares theory, and concrete instances `Int`, `QRat` ($\mathbb{Q}$), and `QSqrt2` ($\mathbb{Q}[\sqrt{2}]$).
  - `Conjecture00000007607/Clifford2.lean` — $\mathrm{Cl}_{2,0}(R)$ positive abelian theorems and $\mathrm{Spin}(2, \mathbb{Q})$ non-vacuity.
  - `Conjecture00000007607/Clifford3.lean` — $\mathrm{Cl}_{3,0}(R)$ Lagrange identity, master rotor/spectral characterizations, subalgebra obstruction, and $90^\circ$/$180^\circ$/Pythagorean counterexamples.
  - `Conjecture00000007607/HigherDim.lean` — $\mathrm{Cl}_{4,0}^+(R)$ / $\mathfrak{so}(4)$ commuting disjoint-plane refutation and uniform `DimN.universal_refutation_ge_3` for all $n \ge 3$.
  - `Conjecture00000007607.lean` — Top-level synthesis theorems `positive_planar_spin2` and `conjecture_00000007607_disproved`.
- `verify.py` — Standalone exact & numerical Python 3 verification suite (exits `0`).
- `verification/` — Build and audit logs (`lake-build.log`, `lean-axioms.log`, `lean-version.log`, `pdf-build.log`, `python-verify.log`, `SELF_REVIEW.md`).
