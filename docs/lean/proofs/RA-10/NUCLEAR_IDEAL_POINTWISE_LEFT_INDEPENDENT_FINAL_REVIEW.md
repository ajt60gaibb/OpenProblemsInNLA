# RA-10 pointwise left singular-value ideal bound: independent final review

**Disposition:** approved for aggregate import. The summed frozen nuclear-norm inequality, right ideal inequality, Eq. (14), and full RA-10 Target remain open.

I independently inspected `NuclearIdealPointwiseLeft.lean` at SHA-256 `6b5755933e43c3c244bee7be4e80ed2fdf2841212e491ddb852f2585353f6a27` against the approved RA-10 singular-value precontract and frozen statement. For every `n`, real square `X,Y`, and **every** `i:Fin n`, the public theorem bounds the actual `singularValues(toEuclideanLin (X*Y),i.val)` by the scoped Euclidean operator norm `‖X‖` times the actual singular value of `Y` at the same index. The factor is exactly one; no rank, positivity, gap, or nonzero-dimension premise is added.

The private scalar-decomposition helper preserves the ordered Gram basis and multiplies each eigenvalue by `s=‖X‖²≥0`. The source applies the audited PSD Gram difference in the correct order, then the audited same-index ordered Loewner and Gram/singular-square bridges. With nonnegative singular values and operator norm, square comparison yields the unsquared bound, including zero factors, tied values, and `Fin 0`.

Separate imported audit `/private/tmp/ra10-pointwise-left-independent-audit.lean` at SHA-256 `89ee9210c8e5b145f6f45d821c819e176a73a062ef22008fbda315f5395d3079` restated the exact signature and passed pinned Lean 4.33.1 with LeanCert `kernel`. `#assert_trust` passed; `#print axioms` lists only `propext`, `Classical.choice`, and `Quot.sound`. Source scan found no `sorry`, `admit`, `native_decide`, `unsafe`, or custom axiom.
