# Statement Alignment: 00000009679

The complete bilingual source is `source.md`, Git blob
`541b54697f4283123781a066f17e9b0a7e3ec223`, raw UTF-8 SHA-256
`e3fd65548a676ba5dcee0340d2f9dd1aae6c2a069273e9d61799e4bba712b639`,
at source commit `b355e42906e6eaf52bc7e9d005e0ef02d8aa7400`.
No organizer text or hypothesis is altered.

## Necessary Clause

Both languages universally quantify over nonzero cusp modular forms of
weight at least two and algebraic upper-half-plane points outside imaginary
quadratic fields, and conclude transcendence of the value. Neither language
requires algebraic Fourier coefficients, a coefficient field, a normalized
first Fourier coefficient or a Hecke eigenform. Standard analytic cusp forms
are complex vector spaces. Restricting the asserted class to level-one
weight-12 forms is legitimate for a counterexample, not a replacement of the
universal goal by an unrelated claim.

| Source condition or conclusion | Actual mathematical and Lean bridge |
|---|---|
| A modular form that is a cusp form | `CuspForm.discriminant` is an actual level-one weight-12 cusp form. Its complex scalar multiple `normalized` remains in the same actual `CuspForm` type. |
| Weight at least two | The witness has integer weight 12, and `12 >= 2` is proved in the final negation. |
| Form is not identically zero | `normalized_value` proves value one at `tau`; `normalized_nonzero` derives nonzero status from that value. |
| Point in the upper half-plane | `point = sqrt(2) + i`; `point_im_pos` gives imaginary part one and constructs actual `tau : UpperHalfPlane`. |
| Point algebraic | `point_algebraic` proves actual `IsAlgebraic Rat point`, using algebraicity of the square-root and imaginary-unit components and closure under addition; `tau_algebraic` transports it. The paper independently gives `X^4 - 2X^2 + 9`. |
| Outside every imaginary quadratic field | `quadratic_relation_trivial` proves rational coefficient independence of `1,point,point^2`. `point_not_mem_quadratic` excludes membership in every actual `IntermediateField Rat Complex` of `finrank` two, by the three-independent-vectors dimension bound. `OutsideImaginaryQuadratic` quantifies over such fields with a nonreal element, and the stronger theorem proves it. |
| Evaluation rescaling is defined | `ModularForm.discriminant_ne_zero`, through the actual cusp-form coercion, proves the denominator is nonzero. No nonvanishing assumption is added. |
| Alleged transcendental value | `normalized_value` gives exactly one, `normalized_value_algebraic` proves algebraicity, and `normalized_value_not_transcendental` proves the opposite of the source conclusion. |
| Universal quantifiers and their negation | `LevelOneValueAssertion` states the necessary clause on actual level-one cusp forms, with all source premises explicit; `level_one_value_assertion_false` is a closed negation, and `actual_counterexample` existentially packages a genuine form and point. |

## Boundaries

This is a fixed pair `(f,tau)`, even though the construction selects `tau`
before rescaling the form. This is valid when negating `forall f forall tau`.
Rescaling at a point is not Fourier/Hecke normalization. No claim is made
that the resulting first Fourier coefficient is one or algebraic. If such an
additional arithmetic convention is imposed in a different version, the
present argument is not advertised as solving that version.

The later CM-period and class-number assertions are not separately proved
or refuted. The source conjunction is refuted by its necessary first clause.
This does not contradict Nesterenko's theorems. The dictionary between
embedded imaginary quadratic fields and the degree-two/nonreal definition
is standard mathematics reviewed here, not a new general Lean embedding
classification. All field exclusion is stronger than this dictionary needs.

The 19 public theorems are audited by actual types and axiom closures. There
is no new axiom, assumed counterexample, artificial Boolean evaluation,
`sorry`, `admit`, `native_decide` or unsafe evaluation. Python checks only
supplementary exact algebra and bounded diagnostics; it is not a replacement
for the Lean argument. Independent preflight or core review is not by itself
a frozen-package review or current publication authorization.
