# Conjecture 00000001064 — minimal Kakeya sets in AG(2,q), q odd

**Statement.** Let `F = F_q` with `q` odd. A *Kakeya set* `K ⊆ F²` is a set containing an
affine line in every one of the `q+1` directions (slopes `m ∈ F` for lines `y = m x + b`, plus the
vertical direction `x = c`). Then

    min |K|  =  q(q+1)/2 + (q−1)/2 .

(Both terms are integers; `⌊(q−1)/2⌋ = (q−1)/2` for odd `q`.)

**Source.** A. Blokhuis, F. Mazzocca, *The finite field Kakeya problem*, in: Building Bridges
(Bolyai Soc. Math. Stud. 19), Springer 2008, 205–218; arXiv:0911.4370.  Their lower bound uses
(i) Faber's incidence formula, (ii) a parity argument producing a blocking set out of the
"odd-multiplicity" points, (iii) Jamison / Brouwer–Schrijver (`|blocking set of AG(2,q)| ≥ 2q−1`),
(iv) the Bichara–Korchmáros theorem (a `(q+2)`-set has ≤ 2 internal nuclei for `q` odd).
Below everything is re-derived from scratch in affine coordinates; (iv) is replaced by an
elementary product computation that suffices for the bound, and (iii) is proved by the
Brouwer–Schrijver polynomial argument in the form actually needed.

---

## 0. Reduction to line systems

If `K` is Kakeya, choose for every slope `m` an intercept `b(m)` with `L_m := {(x, m x + b(m))} ⊆ K`
and a `c` with `L_∞ := {(c, y)} ⊆ K`.  Call `𝓛 = {L_d : d ∈ F ∪ {∞}}` a *line system*;
`|K| ≥ |⋃ 𝓛|`, so it suffices to bound `|⋃𝓛|` from below.  Conversely the construction in §4 is a
union of such lines.

Basic facts: `|L_d| = q`; two lines of different directions meet in exactly one point
(`L_m ∩ L_{m'} = {(x₀, m x₀ + b(m))}` with `x₀ = (b(m') − b(m))/(m − m')`; `L_m ∩ L_∞ = {(c, mc+b(m))}`);
two distinct parallel lines are disjoint.

For a point `A ∈ F²` let `n(A) := #{d : A ∈ L_d}` (its *multiplicity*).

## 1. Double counting

* (C1) `Σ_A n(A) = Σ_d |L_d| = q(q+1)`.
* (C2) `Σ_A n(A)(n(A)−1) = #{(d,d',A) : d ≠ d', A ∈ L_d ∩ L_{d'}} = (q+1)q` (ordered pairs of
  distinct directions, each contributing exactly one point).

Consequently `Σ_A n(A)(n(A)−2) = 0`.  (★)

## 2. Faber's formula and the easy bound `q(q+1)/2`

For every integer `n ≥ 0`:  `2·[n ≥ 1] = 2n − n(n−1) + [n ≥ 1](n−1)(n−2)`
(check `n = 0`; for `n ≥ 1` the right side is `2n − n² + n + n² − 3n + 2 = 2`).
Summing over `A` and using (C1),(C2):

    2 |⋃𝓛| = 2q(q+1) − q(q+1) + 2σ = q(q+1) + 2σ,     σ := Σ_{n(A) ≥ 1} (n(A)−1)(n(A)−2)/2 ≥ 0.

Hence `|⋃𝓛| ≥ q(q+1)/2`, and `|⋃𝓛| = q(q+1)/2 + σ`.

## 3. The refinement for odd `q`: `σ ≥ (q−1)/2`

Let `𝒪 := {A : n(A) odd}` and `τ := |𝒪|`.

**3a. `τ ≤ 4σ`.**  Pointwise, for `n ≥ 0`:
`[n odd] ≤ [n ≥ 1]·2(n−1)(n−2) − n(n−2)`  (n=0: 0≤0; n=1: 1≤1; n=2: 0≤0; n=3: 1≤1;
n≥4: RHS = (n−2)² ≥ 4).  Summing and using (★): `τ ≤ 4σ − 0`.

**3b. Parity.**  Let `L` be any affine line.
* If `L ∉ 𝓛`: exactly one `L_d` is parallel to `L` (and disjoint from it), every other `L_{d'}`
  meets `L` in one point, so `Σ_{A∈L} n(A) = q`, which is odd. Since `|L| = q`, some `A ∈ L` has
  `n(A)` odd, i.e. `L ∩ 𝒪 ≠ ∅`.
* If `L = L_d ∈ 𝓛`: `Σ_{A∈L} (n(A) − 1) = q` (the other `q` lines each meet `L` once).  If `L ∩ 𝒪 = ∅`
  then every `n(A) − 1` (`A ∈ L`) is odd and `≥ 1`, and `q` such terms summing to `q` forces
  `n(A) = 2` for all `A ∈ L`.  Call such a line *all-2*.

**3c. At most one non-vertical line of `𝓛` is all-2.**  Suppose `L_{m₀}, L_{m₁}` (`m₀ ≠ m₁`) are
both all-2.  Let `P* = (x*, y*) = L_{m₀} ∩ L_{m₁}`.  For `m ∉ {m₀, m₁}` put
`γ(m) := m x* + b(m)` (the height at which `L_m` crosses the vertical line through `P*`) and
`u(m) := (b(m₀) − b(m))/(m − m₀)`, `v(m) := (b(m₁) − b(m))/(m − m₁)` (the abscissae of
`L_m ∩ L_{m₀}` and `L_m ∩ L_{m₁}`).  One computes

    u(m) − x* = (y* − γ(m))/(m − m₀),      v(m) − x* = (y* − γ(m))/(m − m₁).

Because `L_{m₀}` is all-2, the `q` points `L_m ∩ L_{m₀}` (`m ≠ m₀`) and `L_∞ ∩ L_{m₀}` are pairwise
distinct, so `m ↦ u(m)` is a bijection `F∖{m₀} → F∖{c}` sending `m₁ ↦ x*`; hence on
`S := F∖{m₀,m₁}` it is a bijection onto `F∖{c, x*}`.  Likewise `v : S → F∖{c,x*}` is a bijection.
Therefore `Π_{m∈S}(u(m) − x*) = Π_{w ∈ F∖{c,x*}} (w − x*) = Π_{m∈S}(v(m) − x*)`, and all factors are
nonzero.  Cancelling the common nonzero numerators `Π_S (y* − γ(m))` gives
`Π_{m∈S}(m − m₀) = Π_{m∈S}(m − m₁)`.  Both products are `W/(m₁−m₀)` and `W/(m₀−m₁)` respectively,
where `W = Π_{w≠0} w ≠ 0` (substitute `w = m − m₀`, resp. `w = m − m₁`).  So `m₀ − m₁ = m₁ − m₀`,
i.e. `2(m₀−m₁) = 0`, impossible since `q` is odd and `m₀ ≠ m₁`.

(The vertical line may also be all-2; we do not need to exclude that.  Blokhuis–Mazzocca quote
Bichara–Korchmáros for "≤ 2 nuclei"; the computation above is the special case we need.)

**3d. A blocking set.**  Choose a point `E` as follows: if some `L_{m₀}` is all-2 (unique by 3c)
let `E := L_∞ ∩ L_{m₀} = (c, m₀c + b(m₀))`; otherwise let `E := (c, 0) ∈ L_∞`.
Then `B := 𝒪 ∪ {E}` meets every affine line: a line not in `𝓛`, or a line of `𝓛` that is not all-2,
meets `𝒪` (3b); an all-2 line is `L_∞` or `L_{m₀}`, both containing `E`.  So `B` is a blocking set
of `AG(2,q)` and `|B| ≤ τ + 1`.

**3e. Jamison's theorem.**  *Every blocking set `B ⊆ F²` (meeting all `q²+q` affine lines) has
`|B| ≥ 2q − 1`.*

Proof (Brouwer–Schrijver, dualised).  Translating, assume `(0,0) ∈ B`.  Put
`f(X,Z) := Π_{(a,b)∈B, (a,b)≠(0,0)} (1 − aX + bZ) ∈ F[X,Z]`, of total degree `≤ |B| − 1`.
* `f(0,0) = 1`.
* `f(x,z) = 0` for `(x,z) ≠ (0,0)`: if `z ≠ 0`, `B` meets the line `y = (x/z)·x' − 1/z`, giving
  `(a,b) ∈ B` with `bz = ax − 1`, i.e. `1 − ax + bz = 0`; if `z = 0` then `x ≠ 0` and `B` meets the
  vertical line `x' = 1/x`, giving `(1/x, b) ∈ B`, a factor `1 − (1/x)x = 0`.  In both cases
  `(a,b) ≠ (0,0)`.
* Hence `Σ_{(x,z)∈F²} f(x,z) = f(0,0) = 1`.  On the other hand, writing
  `f = Σ_e c_e X^{e₁}Z^{e₂}`, `Σ_{(x,z)} f(x,z) = Σ_e c_e (Σ_x x^{e₁})(Σ_z z^{e₂})`, and
  `Σ_{x∈F} x^e = 0` whenever `e < q − 1` (including `e = 0`, as `q = 0` in `F`).  If
  `deg f < 2(q−1)` every monomial has `e₁ < q−1` or `e₂ < q−1`, so the whole sum is `0 ≠ 1`.
Therefore `|B| − 1 ≥ deg f ≥ 2(q−1)`.  ∎

**3f. Conclusion.**  `τ + 1 ≥ |B| ≥ 2q − 1`, so `4σ ≥ τ ≥ 2q − 2`, `σ ≥ (q−1)/2`, and by §2

    |K| ≥ |⋃𝓛| = q(q+1)/2 + σ ≥ q(q+1)/2 + (q−1)/2.

## 4. Construction attaining the bound (dual conic + one vertical line)

Let `q` be odd, so `2` and `4` are invertible in `F`.  Define

    K := { (x,y) ∈ F² : x² − y is a square in F }  ∪  { (0,y) : y ∈ F }.

* Slope `m`: the line `y = m x − m²/4` lies in `K`, since `x² − (mx − m²/4) = (x − m/2)²`.
  (These `q` lines are the tangents `y = 2t x − t²` to the parabola `y = x²`; together with the
  line at infinity they form the dual conic.)
* Vertical: `x = 0` lies in `K`.
* Counting: the number of squares in `F` (including `0`) is `(q+1)/2` (the squaring map is 2-to-1
  on `F*` since `−1 ≠ 1`; equivalently `Σ_a χ(a) = 0` for the quadratic character).  For each of the
  `q` values of `x` the first set contains exactly `(q+1)/2` points `(x, x² − s)`, `s` a square:
  `q(q+1)/2` points.  The vertical line adds the points `(0,y)` with `−y` a non-square:
  `q − (q+1)/2 = (q−1)/2` new points.  Total `q(q+1)/2 + (q−1)/2`.

Hence the minimum is exactly `q(q+1)/2 + (q−1)/2`.  (Sanity: `q=3 → 7`, `q=5 → 17`, `q=7 → 31`,
`q=11 → 71`, matching brute force.)
