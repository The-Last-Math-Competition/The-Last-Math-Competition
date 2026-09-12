# Disproof of Conjecture 00000001231

**Verdict: FALSE.**

## The conjecture

|Jac(J(n,k))| = (C(n-2,k-1))^{C(n,k)-1} · ∏_i f(i), where f(i) = (i²−i+1)^{e_i} is an
"explicit small-factor polynomial"; the formula allegedly follows from the matrix-tree
theorem for complete graphs restricted to Young subgroups.

## The refutation in one paragraph

Take J(4,1). The Johnson graph J(n,1) is exactly the complete graph K_n, so J(4,1) = K_4.
By the matrix-tree theorem (which the conjecture itself invokes), the number of spanning
trees of K_4 is τ(K_4) = 4^{4-2} = 16; this is verified directly as the determinant of the
3×3 principal minor

    det [[3,-1,-1], [-1,3,-1], [-1,-1,3]] = 16

of the Laplacian of K_4. The conjecture's leading factor at (n,k) = (4,1) is
C(2,0)^{C(4,1)-1} = 1^3 = 1, so the conjecture asserts

    16 = ∏_i (i²−i+1)^{e_i}.

But i²−i+1 = i(i−1)+1, and i(i−1) is a product of two consecutive integers, hence even;
so i²−i+1 is **odd for every integer i**. Any product of odd numbers is odd, so the
right-hand side is odd and cannot equal 16. Contradiction.

## Corroborating instance

J(4,2) is the line graph of K_4, i.e. the octahedral graph (6 vertices, 12 edges). Its
Laplacian minor determinant gives τ(J(4,2)) = 384. The conjecture's leading factor is
C(2,1)^{C(4,2)-1} = 2^5 = 32, leaving 384/32 = 12, which is again **even** — impossible
for a product of odd factors. (Independently, τ = 384 ≠ 2^5 · (odd) = 32 · odd also fails
because 384 = 2^7·3.)

## What is and is not claimed

- We refute only the **literal formula** of the conjecture, at the concrete point
  (n,k) = (4,1) (and corroborate at (4,2)).
- The matrix-tree theorem itself is of course true and is used as a tool against the
  conjecture, not disputed.
- We do not speculate about what "corrected" formula the author intended; the stated
  formula is false as written.

## Contents

- `main.tex`, `build/main.pdf` — formal write-up (J(n,1)=K_n; τ(K_4)=16 via the 3×3
  Laplacian minor; parity lemma; contradiction).
- `reproduce.py` — standalone script (no absolute paths, pure standard library):
  rebuilds the K_4 and J(4,2) Laplacians, computes τ = 16 and τ = 384 by exact
  fraction-Gaussian elimination, checks the leading factors 1 and 32, and verifies
  i²−i+1 is odd for all i in 0..100.
- `lean4/` — Lean 4 project (toolchain `leanprover/lean4:v4.33.1`, core only) proving,
  with **zero axioms and zero `sorry`**:
  - `tau_K4 : tau = 16` (explicit 3×3 integer determinant expansion),
  - `f_odd : ∀ i : ℕ, (i*i - i + 1) % 2 = 1` (two-stage induction),
  - `prod_odd_not_16 : (List.finRange 4).prod f = 21 ∧ 21 % 2 = 1 ∧ 16 % 2 = 0`
    — a concrete odd-product value together with the parity of 16,
  - `refute` : the parity-incompatible instance `¬((finRange 4).prod f = 16 ∧ tau = 16)`.

Run `python3 reproduce.py` and, in `lean4/`, `lake build && lake env lean Check.lean`.
