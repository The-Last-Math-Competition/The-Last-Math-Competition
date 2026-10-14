# Bilingual statement alignment

Fixed official source commit: `1e3f7c25616e84b611350a412febceabad75b56a`.
Blob: `f3b4d50ec9eff42aca2fb9eb75236574a3896b4f`.
Raw UTF-8 SHA-256: `101debe6d45749a2d172873c60e9afb03f2461412091529484c0b729ea285272`.
`source.md` retains both original languages byte-for-byte.

Both languages call the factorial ratio a count of the named rational parking
functions; the Chinese explicitly asserts this counting formula. The English
calls positivity a strengthening of the counting formula. We preserve this
enumerative condition, not just the unrelated existence of a positive q-analogue
of a numeral. Any genuine enumerative refinement must recover the object count
at q=1, regardless of the chosen statistic. Nonnegative coefficients are modeled
by a list of natural numbers and Horner evaluation; evaluation at one is their sum.

We follow Armstrong, Loehr and Warrington, *Rational Parking Functions and Catalan
Numbers*, arXiv:1403.1845v1, Sections 3.1 and 3.2, height-first convention. The
proof does not import their cardinality formula as an axiom. For width W=2 and
height H=3, north-step columns c_0,c_1,c_2 are weakly increasing and satisfy
`3*c_i <= 2*i`. They are therefore either `(0,0,0)` or `(0,0,1)`.
Insert the prescribed east runs between north steps and after the final north
step. On a horizontal run the right endpoint gives the smallest diagonal margin;
the next north step increases it. The last run has y=H and ends at x=W, so all
vertices are above the diagonal and the endpoint and final east run are retained.
The Lean `above` recursion explicitly checks every vertex, including the endpoint.

| Source requirement | Mathematical object | Lean evidence |
|---|---|---|
| Rational paths at positive coprime parameters | Width 2, height 3; three north and two east steps | `coprime`, `word_universe`, `dyck_words_exact` |
| Actual Dyck path, not just column numbers | Every vertex satisfies 3x <= 2y; endpoint steps exact | `pathGood`, `wordGood`, `raw_word_bridge`, `path_injective`, `path_sorted_bridge` |
| Parking-function labels | Each of three north steps receives a different label, increasing within a column | `labelGood`, `labels_exhaustive` |
| Complete object universe | All 8 column triples and 27 label triples examined | `universe_complete`, `universe_nodup`, `parking_membership` |
| Actual count | Four distinct valid objects, not repeated records | `parking_exact`, `parking_nodup`, `parking_count` |
| Equivalent preference description | Read each label's north-step column | `preference_image`, `preferences_injective` |
| Stated factorial ratio | Height-first (m,n)=(3,2), value 12 | `ratio_height_first`, `necessary_count_clause_false` |
| Enumerative positive q-refinement | Evaluation at one must be both count and stated formula | `eval_at_one`, `no_positive_refinement_at_witness`, `expanded_specialization_negation` |

The final witness disproves a universally proposed refinement by its necessary
specialization; it does not prescribe an absent q-statistic. A shuffle restriction
would restrict objects, not increase this count to 12. Extra decorations or a
Frobenius characteristic would require a different source statement; they are
not silently substituted. The formal proof uses the declared height-first pair;
discussion of other conventions does not expand the advertised Lean theorem set.
