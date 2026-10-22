# Proof of conjecture 00000006640

Two symmetric two-state master equations have generators
Q₁=[[-1,1],[1,-1]] and Q₂=[[-2,2],[2,-2]]. They have the same full
static kernel {(a,a)} and the same unique stationary probability vector
(1/2,1/2), but generator spectra {0,-2} and {0,-4}. Their explicit
stochastic propagators have spectra {1,exp(-2t)} and {1,exp(-4t)}, which
differ at every positive time. Both systems satisfy detailed balance
for the same stationary vector.

## Mathematical and formal scope

The state space is Fin 2, probability vectors are real coordinate functions,
and the generators and propagators are actual Mathlib real matrices. The
proof verifies generator conditions, Hermitian symmetry, detailed balance,
both normalized static sets and full kernels, actual algebraic matrix spectra,
stochasticity and the semigroup law, the initial condition, and actual
HasDerivAt master equations. For every initial probability vector it proves
the propagated vector stays probabilistic and solves the differential equation.

No list of numbers is substituted for a spectrum. Spectral membership is
Mathlib `spectrum`, proved through invertibility and determinant factorization.
The propagators are verified directly; equality with a separately defined
general matrix exponential and general ODE uniqueness are not used or claimed.
Time units are fixed in the comparison; the source imposes no quotient by
time rescaling. The construction covers both generator and propagation
interpretations of time spectra and is symmetric/reversible.

The main theorem is:

```lean
theorem conjecture_6640_true : SeparationClaim
```

`SeparationClaim` existentially quantifies over two actual generators,
two stochastic fundamental solutions, and a common detailed-balance
probability vector. It asserts equality of the normalized static sets and
full kernels, inequality of the generator spectra, and inequality of the
propagation spectra for every positive real time. All mathematical claims
needed for this strengthened source statement are formalized.

## Reproduction and review

Lean 4.19.0, Mathlib commit
`c44e0c8ee63ca166450922a373c7409c5d26b00b`, with public-Git pinned metadata.
In `lean/`, run:

```text
lake env lean -DwarningAsError=true Main.lean
lake build
```

Compile `main.tex` using Tectonic or a compatible LaTeX engine.
The author strict Lean check passes, and audited main/bridge theorems use
only propext, Classical.choice, and Quot.sound.

Developed by a delegated AI agent with a self-review; the coordinating agent
reviews it separately. Review mode: agent development with parent adversarial
review; no external independent review. The coordinator performs the fresh
project build and PDF inspection before deciding whether to publish.

`SOURCE.md` is the exact bilingual upstream source at commit
`b355e42906e6eaf52bc7e9d005e0ef02d8aa7400`. The current source/history snapshot
records no earlier PR or solution for this conjecture.
