RE05 actual orthonormal fold and leverage trace
=============================================

This is a deterministic prerequisite for the unchanged RE05 query algorithm.
It proves properties of the existing `LinearFamilyQuery.orthonormalList`,
`orthonormalMember`, and `leverage`. It does not prove the probability bound,
the complete query bound, `OriginalClaim`, `SourceCompanion`, or the full
`Target`, and makes no CI, Comparator, or status-promotion claim.

The three new files are `NLA/Proofs/RE05/OrthonormalCore.lean`,
`OrthonormalFold.lean`, and `OrthonormalFamily.lean`. Their 33 declarations
occupy 308 lines. The source freeze is `SOURCE_FREEZE.json` in this directory,
SHA256 `64b42dd7002731447b0cbbc36d7ea909fbde08947bfe56aecc7a0385558423a6`.
The original 18-input RE05 lock and the previously accepted prerequisite
closure are checked before and after replay. The permanent 217-ID registry,
original README/TeX/PDF, model, reviewed statement, and target are unchanged.

The model uses a finite list fold in supplied index order. At every step it
subtracts a projection sum over `accepted.toFinset`, then appends its normalized
residual, with an explicit zero branch. This proof retains that fold. It first
identifies the frozen `matrixVector` coordinates with the actual entrywise
inner product and norm. The literal `Independent P` implies linear independence
of those coordinates. Normalized ordered Gram--Schmidt vectors are therefore
orthonormal and injective. Thus converting each accepted prefix to a finset
discards no entries. A direct finite-prefix induction proves exact equality
between the model's fold prefix and the normalized vectors at precisely the
same supplied indices. No different basis is selected.

`orthonormalMember_eq_orderedMember` discharges the optional list lookup by the
exact prefix length. `orthonormalMember_orthonormal` proves orthonormality of
the actual model members. Both the flattened and literal matrix spans equal
the supplied matrix span. `orthonormalMember_inner` gives the literal
Kronecker inner-product identity. Reordering the actual finite double sums
then proves `leverage_trace`: the sum of diagonal entries of the literal
leverage matrix is `(q + 1 : ℝ)`.

All these final results have only the original `Independent P` hypothesis.
They impose no extra positive dimension, rank, nonzero residual, orthogonality
promise, or chosen-basis hypothesis. The zero normalization branch is handled
explicitly, including for arbitrary zero matrices. The actual-member span
identity also holds in the original matrix vector space, through the proved
injectivity of the fixed entry flattening.

Development producer builds and the final development consumer passed
LeanCert kernel mode with only `propext`, `Classical.choice`, and `Quot.sound`.
The first consumer preflight had optional-list-lookup syntax and a `Fin 1`
index simplification error. The second corrected the syntax but encountered
opaque `Fin 1` singleton instance synthesis. The third uses an explicit finite
index proof and passes. Both failed preflight inputs and raw logs are retained
under `development/`; the first input was reconstructed from the exact
consumer-only correction recorded in the tool history. Those development
checks reuse private development objects and are not fresh acceptance evidence.

The separate fresh replay starts with no project output objects, snapshots all
ten ordinary local producer sources, and checks a 43-assertion literal consumer.
The consumer covers all 33 authored declarations, actual fold lookup, actual
orthonormality, raw matrix span, expanded leverage trace, zero normalization,
and a concrete independent one-generator family. It checks the unchanged
reviewed full-target identity only; it supplies no full-target proof. A separate
intentionally unresolved `False` control must be rejected by kernel trust with
`sorryAx`. `final/result.json` is authoritative for the terminal replay result;
this author review by itself makes no independent source-review claim.
