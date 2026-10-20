# Independent review of TLMC 00000005207

Review date: 20 October 2026 UTC.

## Verdict

The mathematical counterexample, final Lean package, LaTeX report and PDF are
approved. The exact posted multiplicativity clause fails for the rational skew-symmetric 3 by 3 matrix
space and the scalar 1 by 1 space. The initial source-only compile, all-theorem
axiom audit, kernel replay, and independent exact calculations passed.
The frozen final six-file package was copied independently without build
artifacts, rebuilt and checked successfully. Every page of the exact final
three-page PDF was visually inspected and is clean. No mathematical or
formal-source correction remains outstanding.

## Source and interpretation

The conjecture was fetched independently through the GitHub connector:

https://github.com/The-Last-Math-Competition/The-Last-Math-Competition/blob/main/conjectures/00000005207.md

Source blob SHA: 74afbaf0aafcb8c077141a71b1232932418e3031.

The English and Chinese statements each assert multiplicativity of the
difference between noncommutative and commutative rank under tensor products.
Ordinary multiplicativity means Delta(X tensor Y) = Delta(X) Delta(Y). The
source places matrix sizes at most three in scope, and the proposed example
has factor sizes three and one and product size three. Nothing in the source
excludes a scalar factor or requires both gaps to be positive.

The additional phrase about a multiplicative deficit is not defined. No
meaning is assigned to it in this review. It does not justify silently
replacing the explicitly stated multiplicativity law by an unstated corrected
formula. The disproof addresses that literal law and hence the conjunction,
not the independent low-size gap classification or minimality statements.

## Mathematical review

Let S consist of matrices [[0,a,b],[-a,0,c],[-b,-c,0]] over Q, and let U be
the full 1 by 1 rational matrix space. Every scalar S determinant is zero,
and its leading 2 by 2 minor at (a,b,c) = (1,0,0) has determinant one.
Thus the commutative rank is exactly two.

The coefficient matrices X0, X1, X2 are the three displayed skew-symmetric
basis matrices. Substituting the 2 by 2 matrices

- T0 = [[1,0],[0,0]],
- T1 = [[0,1],[1,0]],
- T2 = [[0,0],[0,1]]

gives an actual Kronecker blowup sum of Xi tensor Ti with determinant one.
Its six rows are reproduced and independently checked in
`independent-check.log`. Hence its rank is six, and normalized blowup rank
is at least three. Every d-blowup matrix has size 3d, providing the universal
upper bound three. The noncommutative rank is therefore exactly three.

Both ranks of U are one by dimension and the witness [1]. The genuine
coefficient tensor product with U has coefficients Xi tensor [1] = Xi.
Consequently its gap stays one, while the product of factor gaps is zero.
All three matrix sizes remain at most three. This is a nonzero example, not
a degeneracy involving a zero tensor.

The rank interpretation was checked against the primary reference:

Harm Derksen and Visu Makam, On non-commutative rank and tensor rank,
Definitions 1.3, 1.5, 1.9 and Lemmas 1.4, 1.8:
https://sites.lsa.umich.edu/hderksen/wp-content/uploads/sites/614/2018/05/A.I.a.53.pdf

That reference gives the ordinary maximum matrix-space rank and maximum
normalized blowup characterization, and identifies them with generic
commutative and free-skew-field ranks over an infinite field. Its Example
1.6 contains the classical skew-space blowup underlying this witness.
The arXiv identifier in the report was separately verified:
https://arxiv.org/abs/1606.06701.

## Formal semantic review

The source imports Std only. The definitions were inspected in full, rather
than judging the theorem by its name or its numeric conclusion.

1. Matrices are represented as rational-valued functions of two natural-number indices.
   The explicit size parameters restrict all minors and substitutions to
   the intended finite initial blocks. Values outside those blocks are
   irrelevant to rank. This encoding does not weaken the finite statements.
2. The determinant is the usual recursive Laplace expansion along the first
   row. The sign and the deletion of the selected column are correct.
3. IndexSelection requires every selected index to be in bounds and requires
   strict increase on the entire selected range. Thus all ordered minors,
   not merely principal minors, are available.
4. RankLE quantifies over every possible minor size strictly above the bound,
   with every permitted row and column selection. RankGE requires an actual
   nonzero minor and an in-bounds size. These are the conventional
   nonsingular-minor rank criteria, not a hand-selected certificate table.
5. CommutativeRank supplies a rank bound for every rational scalar evaluation
   and an attaining evaluation. No rank value is inserted by definition.
6. NoncommutativeRank quantifies over every positive integer blowup size and
   every rational matrix substitution, and includes an attaining blowup.
   Its upper bound is not restricted to size two or a finite test set.
7. The quotient/remainder indices in blowup implement the ordinary block
   Kronecker product. Those in tensor implement the full coefficient tensor
   product with lexicographic indexing in all three indices.
8. tensor_unit proves actual coefficient equality. Tensor ranks are then
   transported by this proved equality, not by an unproved rank invariant.
9. MultiplicativeGap is universally quantified in the pencils and ranks,
   requires all six rank predicates, and even restricts the product matrix
   size to three. The final theorem negates this law using the concrete
   established ranks; it does not simply define the conjecture to be false.
10. Natural-number subtraction is harmless for this witness: the checked
    ranks are three minus two and one minus one, both nonnegative.

The formalization deliberately takes the standard tensor-blowup definition
of noncommutative rank. It does not construct free skew fields or formalize
the general equivalence theorem, nor a general matrix-rank library bridge.
The LaTeX report states this limit accurately and cites the conventional
correspondence. All actual witness calculations, universal rank bounds,
tensor equality and final contradiction are proved in Lean. No weaker
surrogate or hardcoded rank conclusion was found.

## Executed verification

Toolchain: Lean 4.31.0, commit 68218e876d2a38b1985b8590fff244a83c321783.

Initial independently copied source SHA256:
82ea630282f512ea114dbf7fb4bfaae8a923f7a199c076671eeb1fb5b2e01a1c.

- Source-only compile with `lean -DwarningAsError=true -o RankGap.olean RankGap.lean`: passed.
- Automatically enumerated all 17 theorem declarations and ran
  `#print axioms` for each: passed. The only dependencies are propext,
  Classical.choice and Quot.sound; two elementary selection lemmas use none.
- `leanchecker -v RankGap`: passed, replaying the module into its imported
  environment. This is a Lean-kernel replay check, not a separate external
  implementation of the kernel.
- Source scan for sorry, admit, custom axiom, unsafe, implemented_by,
  native_decide and elaborator injection: no matches.
- Independent symbolic determinant, ordinary coefficient Kronecker product,
  2 by 2 witness and a Leibniz-formula 6 by 6 determinant: passed. This
  independent calculation uses a different determinant algorithm from Lean.

The preliminary source snapshot and logs were retained only as local review
records. They are not promised as submission files. The final verification
repeats the applicable source checks and its included logs are listed below.
The supplemental independent calculation is included as
`independent_check.py` and `independent-check.log`. That optional Python
script uses SymPy; the Lean project itself requires only Lean and Std.

## Final package verification

The frozen final six-file package was copied into a fresh local review
directory, with no imported oleans, lake build directory or manifest. All
six frozen package files were checked byte for byte against this reviewed
copy. The temporary build directory is local review evidence, not part of
the submission.

Executed successfully on that clean copy:

- `lake build`, creating the project's manifest and object files from source;
- `lake env lean -DwarningAsError=true RankGap.lean`;
- `lake env lean -DwarningAsError=true Audit.lean`, auditing all 17 theorems;
- `lake env leanchecker -v RankGap`.

The final source has the same SHA256 quoted above. Logs are
`final-build.log`, `final-strict.log`, `final-axioms.log` and
`final-kernel.log`. The complete all-theorem audit input is `Audit.lean`.
Full final artifact hashes are in `final-hashes.sha256`; those entries refer
to the six files at the submission root, not this verification subdirectory.

The README's mathematical descriptions, theorem map and formal-scope
statements match the source. Its claim about prior repository submission
searches is selection-stage provenance supplied by the author, not a search
independently repeated as part of this mathematical review.

## LaTeX and PDF review

The full initial LaTeX source was read and its matrices, rank definitions,
universal bounds, determinant values, tensor-unit argument, theorem statement,
and formal-scope disclosures match the checked Lean development.

Two initial overfull lines, a long GitHub URL and an inline checking command,
were reported to the author and corrected. The final author build log has no
overfull, underfull, undefined-reference or other warning matches.

The exact final PDF SHA256 is:
15b04c47d77b4832ff07f0a6c83e9b79797a48b7d2f3589526b621c522e391d7.

Its matching LaTeX SHA256 is:
907cfc2e6a950cacf9529764f1b65994c4ba85b2e54b3266e06f6ac646c033d7.

The reviewer independently ran pdfinfo, pdftotext and pdftoppm. The PDF has
three US-Letter pages, no encryption or JavaScript, and all pages rendered
successfully at 120 dpi. Each complete page image was opened and inspected:

- Page 1: title, abstract, literal source interpretation, rank conventions,
  equations, citations and source footnote are readable with no clipping.
- Page 2: all skew matrices and the 6 by 6 block matrix match the checked
  witness, determinant and rank arguments are complete, and the final
  inequality is correctly displayed. No overlaps or missing symbols.
- Page 3: formal coverage, explicit scope limitation, reproducibility
  command and bibliography are readable and correctly rendered.

Rendered page images and extracted text were retained as local review
records only; they are not promised as submission files. Final PDF approval
covers the exact hash above; substantive changes require a renewed affected
check.

The reviewer also rebuilt the final LaTeX twice independently with
`pdflatex -output-format=pdf -no-shell-escape -interaction=nonstopmode
-halt-on-error`, using the existing cached format and installed font paths.
Both passes succeeded. The second-pass log contains no overfull, underfull,
undefined-reference or warning matches. The rebuilt PDF text is byte-identical
to the final PDF's extracted text, and every rendered page PNG is
byte-identical to the inspected final-PDF page. The independent LaTeX logs
are included as `first-pass.log` and `second-pass.log`. The temporary rebuild
output and page images remain local review records, not submission files.
No software installation was needed.


## Included verification evidence

This report and the following files are packaged together under
`verification/independent/`. All evidence filenames in this report refer to
that directory unless explicitly stated otherwise.

- `SUBMISSION-REVIEW.md`: this independent review and verdict.
- `final-build.log`: fresh source-only Lake build.
- `final-strict.log`: direct warning-as-error Lean check.
- `Audit.lean` and `final-axioms.log`: every theorem's axiom dependency check.
- `final-kernel.log`: explicit RankGap kernel replay.
- `final-hashes.sha256`: hashes of the six approved root-level artifacts.
- `independent_check.py` and `independent-check.log`: supplemental exact
  algebraic checks, including a Leibniz determinant computation.
- `first-pass.log` and `second-pass.log`: independent LaTeX rebuild logs.

To repeat the included theorem audit from the submission root after
`lake build`, run
`lake env lean -DwarningAsError=true verification/independent/Audit.lean`.
The local temporary source snapshots, build directories, PDF text extractions
and PNG renderings are not needed for any of the supplied Lean proofs.
