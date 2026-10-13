# RA-10 ordered PSD Loewner eigenvalue comparison: independent pre-review

**Disposition:** approved for implementation of the exact displayed
theorem. I independently reviewed
`ORDERED_PSD_LOEWNER_EIGENVALUE_PRE_REVIEW.md` at SHA-256
`0e4f1e484e5ccc93b212d95b5c642356b6d5585d7914788c7c85caf79445db7b`
and verified all seven source locks against the repository.

The sign orientation is correct: frozen `PositiveSemidefinite (G-H)` gives
`xᵀHx≤xᵀGx`. The audited intersection theorem applied with `QC=QH`
and `QA=QG` supplies one nonzero `x` with H coordinates after `a`
and G coordinates before `a` zero. The audited prefix lower and suffix
upper Rayleigh bounds yield `h(a)Σx²≤xᵀHx` and
`xᵀGx≤g(a)Σx²`. Since the same `Σx²` is strictly positive, exact
coefficient-one cancellation proves `h(a)≤g(a)` for each original
zero-based `a`, including ties and zero eigenvalues. At `n=0` there is
no index. No simultaneous basis, entrywise order, or spectral gap is
assumed.

This review approves the generic eigenvalue comparison only. A
separate frozen implementation, imported exact-signature audit,
LeanCert-kernel check, and axiom review are required before aggregate
import. The Gram order, nuclear ideal inequalities, Eq. (14), and
the full RA-10 Target remain open.
