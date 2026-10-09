# Independent semantic review records

These records document the source-first review of the author's original frozen project. At that stage the author's inspection module was named `Audit`; the personal submission preserves it unchanged as `lean/AuthorAudit.lean` and adds a separate production `lean/Audit.lean` for the portable verifier.

`ReviewAudit.lean` was compiled against that original project. To reproduce its exact module context from the submission directory, using a new scratch directory:

```sh
mkdir /tmp/tlmc1569-original-review
cp lean/Solution.lean lean/lake-manifest.json lean/lean-toolchain /tmp/tlmc1569-original-review/
cp lean/AuthorAudit.lean /tmp/tlmc1569-original-review/Audit.lean
cp verification/author-original-lakefile.toml /tmp/tlmc1569-original-review/lakefile.toml
cp verification/semantic-review/ReviewAudit.lean /tmp/tlmc1569-original-review/
cd /tmp/tlmc1569-original-review
lake exe cache get
lake build
lake env lean -t0 -DwarningAsError=true ReviewAudit.lean
```

Use Lean 4.19.0 and the manifest's exact dependencies. The original project's `Solution` declarations are the same byte-identical mathematics used by the final portable verifier. This independent audit adds explicit endpoints and checks ownership, safety and axioms; the final production audit additionally traverses the full transitive type/value dependency graph. The reviewer also independently ran the final portable verifier and all control tests, separately from these original-project records.
