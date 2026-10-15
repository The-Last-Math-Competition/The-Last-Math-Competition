# Conjecture 00000007973: disproved

Take the standard evaluation AG code on `P^1(F_3)` with
`D = P_0 + P_1 + P_2` and `G = P_infinity`.
The Riemann-Roch space is exactly `{a*t+b : a,b in F_3}`; its complete
evaluation code is `{(b,a+b,2a+b)}`. Its minimum nonzero Hamming weight is
**2**, whereas the conjectured formula `deg(D)-g` is **3**.
The weight enumerator is `1 + 6 z^2 + 2 z^3`.

中文：在三元域上的射影直线取三个有限有理点为求值点、无穷远点为极点除子。
一次多项式的求值码是 `[3,2,2]_3` Reed-Solomon 码，最小非零重量为 2；
题目声称的 `deg D - g` 则等于 3，因此原猜想的这一明确子断言为假。
该例满足 `0 < deg G < deg D`、求值点互异、两除子支集不交等标准条件。

## Files

- `proof.tex`, `proof.pdf`: complete mathematical argument and formalization scope.
- `lean4/`: self-contained Lean 4.24.0 project.
- `verify.py`: independent exhaustive check of all nine words.
- `verification.md`: reproducibility and checks.

## Reproduce

```console
cd lean4
lake build
lake env lean Conjecture7973.lean
lake exe verify
```

Run `python verify.py` from this submission directory. To rebuild the PDF,
run `pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error proof.tex` twice.

Lean checks the modulo-three field operations, linearity and injectivity of
the evaluation map, every nonzero codeword's weight lower bound, a weight-two
witness, and the complete enumerator. The report supplies the elementary
geometric identification `L(P_infinity)=span{1,t}` on the genus-zero projective
line. The Lean theorem is explicitly the necessary concrete instance, not
a claimed formalization of general algebraic geometry.
