# TLMC 00000009361: permutation records

## Result

For an actual permutation p of 0,...,n-1, its upper-record indicator at chronological position k (one-based) is true exactly when its entry is greater than every earlier entry. For every length-n Boolean pattern b, the number of permutations with that record pattern is

product over k=1,...,n of (if b[k] then 1 else k-1).

There are n! permutations. Position-exchangeability forces uniformity on this finite transitive sample space, so division by n! gives mutually independent Bernoulli(1/k) indicators. The total record count has the distribution of their sum.

The report states the positional exchangeability convention explicitly. Conjugation invariance of a permutation as a group element is insufficient, and repeated labels are outside the theorem.

## Files

- `main.pdf`, `main.tex`: self-contained mathematical proof and formalization scope.
- `Permutations.lean`: insertion/deletion inverses; actual permutation validity; exhaustive duplicate-free enumeration and factorial cardinality.
- `RecordSemantics.lean`: record comparisons; independent chronological scan; reversal bridge; strictly increasing relabeling; insertion record criterion; exhaustive chronological enumeration.
- `RecordsCount.lean`: exact Boolean-pattern count and normalized rational Bernoulli product identity.
- `source.md`: exact official statement and verified source blob SHA.
- `verification/independent.py`: supplemental direct Python enumeration in chronological order for n=0 through n=8, checking all 511 Boolean patterns across those sizes.

## Formal sample-space correspondence

`Valid n p` requires `p.Nodup` and `forall x, x in p iff x < n`. Its equivalence to `p.Perm (List.range n)` is proved. This is not a rank-code sample-space surrogate.

The construction stores lists in reverse chronological order: adding the final entry is a cons. `perms_complete` proves every actual permutation occurs, and `perms_nodup` proves it occurs once. `chronologicalPerms` is their map by list reversal; its completeness and duplicate-freeness are also proved. `chronologicalRecords` scans a list from left to right, appending each entry to the list of earlier entries. `recs_chronological` proves exact agreement with the recursively defined reverse-storage record vector.

The insertion map raises every old value at least r by one, then appends final value r. The inverse removes that final value and lowers all greater values by one. Both inverse identities and the exact label ranges are proved, and strict monotonicity proves record preservation. The final entry is a record exactly for r=n.

The Lean theorem is a complete finite counting identity. The normalized rational uniform-probability product identity is also formalized. The probability argument converting positional exchangeability to uniformity and interpreting this product as independence is written out in the report; a general Lean probability API is not claimed.

## Toolchain and verification

Lean 4.31.0 with bundled Std only, no external package dependencies or installations. Run `./VERIFY.sh` with the pinned Lean toolchain on PATH; it builds all modules, checks warnings, audits axioms, and independently runs `leanchecker`. The local source modules currently pass with `-DwarningAsError=true`. No `sorry`, `admit`, `native_decide`, custom axioms, unsafe theorem machinery, or kernel bypass is used.

`build_pdf.sh` takes an optional existing TeX-format directory for minimal TeX installations. On an ordinary installation run it with no argument. The optional directory changes only TeX search paths; it does not download or install software.

## Eligibility

Official source checked on 2026-10-16, blob SHA `3c1e3568c9aa81b24440aa69a23149d953e1b4d4`. Current metadata has `proven=false`, `disproven=false`. The refreshed all-state 1022-PR historical index has no 9361 or matching record-topic submission, and the live solution directory was absent. Eligibility must be checked again immediately before any publication.

## Main theorem interfaces

- `chronologicalPatternCount_exact n flags hlen`: the count of genuine chronological permutations whose actual left-to-right record vector equals flags is `patternWeight flags.reverse`.
- `patternWeight (b::bs) = (if b then 1 else bs.length) * patternWeight bs`; since this list is reversed, `bs.length` is precisely the number of entries before the corresponding chronological position.
- `independent_bernoulli_joint_law n flags hlen`: the exact rational uniform pattern probability is `bernoulliProduct flags.reverse`. Its reverse-list head factor is `1/(bs.length+1)` for true and `bs.length/(bs.length+1)` for false.
- Empty lists have weight and Bernoulli product one, and `factorial 0=1`.
