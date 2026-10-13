# RA-10 ordered PSD Loewner eigenvalue comparison: independent final review

**Accepted for aggregate import.** I independently reviewed frozen
`NLA/Proofs/RA10/OrderedPSDLoewnerEigenvalue.lean` at SHA-256
`66a356e2ebc291b2d0c7b272ad770041414e1b2a66330acf46f23f1bdbe0fc73`
against the approved exact precontract and frozen RA-10 predicates.

The single public theorem preserves arbitrary supplied ordered PSD
decompositions of the actual `G` and `H`, assumes the complete frozen
quadratic-form `PositiveSemidefinite (G-H)`, and proves same-index
`eigenvaluesH a ≤ eigenvaluesG a` with coefficient one. Its proof uses
the audited strict prefix/suffix intersection with `QH,QG` in the
correct order, corresponding lower/upper Rayleigh bounds, the literal
double-sum difference, and a strictly positive common sum of squares.
It covers ties and zero eigenvalues; the `Fin 0` case is vacuous. No
entrywise order, common eigenbasis, or spectral-gap premise appears.

The separate imported exact-signature audit
`/private/tmp/ra10-ordered-psd-loewner-independent-audit.lean`, SHA-256
`209e9f4e82d57c7e3088b7e6ac4ba5152a193f504110de98a11d8c9ac8792233`,
passed pinned Lean 4.33.1 and LeanCert `kernel`. `#print axioms`
reported only `[propext, Classical.choice, Quot.sound]`; the source
contains no `sorry`, `admit`, `native_decide`, `unsafe`, or new axiom.
The Gram order, nuclear ideal inequalities, Eq. (14), and full RA-10
Target remain open.
