# RA-05 independent final Lean-boundary review

Reviewer: `/root/infra_audit`, OpenAI Codex AI agent independent of specification and implementation author `/root`. Phase: `lean-boundary`. Verdict: **approve**.

I read the entire canonical original, approved specification, live and frozen definitions, final notes and retained author receipt. The original snapshot is byte-identical; both independent preimplementation reports bind the current specification. The historical classification and credits remain unchanged.

Projector is actual transpose symmetry, matrix idempotence and Mathlib rank at most k. In the pinned library rank is the real finite dimension of the range of mulVecLin. Over real finite Euclidean spaces these are exactly the orthogonal projectors onto all allowed subspaces, including zero and lower rank. No selected bases or abstract geometric oracle restrict the domain.

RowCost computes the full row residual A_i-A_i P with the correct matrix orientation, finite sum of all squared real coordinates, square root, then genuine real p-th power. The pinned real-power zero convention gives zero for p>2. This is Euclidean residual distance, with no function-space supremum norm or squared-distance substitution.

StrongCoreset uses one nonnegative real weight per original row before all allowed projectors and both non-strict relative inequalities. Arbitrary fractional weights, zero rows, zero costs and empty row sets are included. SupportSize counts the exact nonzero-weight index set; it is not total weight, rank or repeated copies.

MinimumSupport takes the least feasible natural support budget. On the target domain the all-one vector gives a feasible budget n, so the infimum is attained and cannot exploit the empty-set convention. WorstSupport uses the complete extended nonnegative-real supremum over all finite n, every d>k and every real matrix. This preserves unboundedness rather than replacing it with a real-supremum default.

EvenPower captures exactly the even integers at least four in the p>2 domain. The rate contains both precise even branches under one minimum, and the noneven single branch. All exponent arithmetic is real. The logarithm is exactly log(2k/epsilon), positive and greater than one on the stated domain. Lower log loss zero versus 5p/2+3 and common upper loss p+5 agree term for term with the preapproved source answer.

Classification chooses positive finite real c and C>=c after p and before all integer k>=1 and every epsilon in (0,1/2). Both ENNReal bounds use the same unrestricted WorstSupport. No all-dimensions, near-even-exponent, low-rank, all-accuracy or logarithmic dependency is lost.

AdditiveProposal retains the original two summands, full real logarithmic exponent, positive constants fixed before every data matrix and accuracy, and an actual nonnegative original-row coreset witness. OriginalAdditiveConjecture preserves the literal universal p>2 proposal. NegativeAnswer negates its whole quantifier structure separately for every p>2. Target combines the complete resolved classification and that negative answer, without conjoining the false original proposal or mislabelling its source.

Every one of Classification, OriginalAdditiveConjecture, NegativeAnswer and Target has closed Prop checks and explicit LeanCert kernel trust. I independently compiled fresh Infrastructure, live RA05 and frozen RA05 in a separate build, then checked actual reflexive equalities for all four names and printed all four axiom closures. Every command passed; the only axioms were propext, Classical.choice and Quot.sound.

No theorem asserting any target is supplied, and no numerical computation is required for this universal existence/classification statement. Projector equivalence, minimum/supremum correspondence and the credited coreset bounds remain mathematical proof obligations. Independently passing frozen identities and source review do not prove them.

This review records independent mathematical/source correspondence and independently executed local macOS kernel evidence. It does not claim external human peer review, a proof of the targets, a re-audit of the source proofs, or a Linux Comparator result.

## Bound inputs

- `docs/lean/statements/RA-05/IMPLEMENTATION_NOTES.md`: `8ad7b1c06221e8fa13b8b26437b0596f7fcfb83bbd3fa51daea20bbffdd05bf8`
- `docs/lean/statements/RA-05/NUMERICAL_TARGETS.md`: `23a9cb637b7b1456fe0a0f06f3ee414c3c7dbcfc5c80a69fc303b7e347166ac5`
- `docs/lean/statements/RA-05/ORIGINAL.md`: `6e03461d0079b656779e5b87d5faa91f198c4c90ea63beb613732226e678181c`
- `docs/lean/statements/RA-05/reviews/lean-boundary-infra-audit-evidence/Identity.lean`: `6904ebceadd03c21b0e61c86966a0b38cd429be1d681c9c03dd72ff6a12b6baf`
- `docs/lean/statements/RA-05/reviews/lean-boundary-infra-audit-evidence/NLA-Statements-Infrastructure.log`: `2a3954627795f50423fd88b74045fed1aa6fcc709aa93aa4113bc4d4ac5d9a30`
- `docs/lean/statements/RA-05/reviews/lean-boundary-infra-audit-evidence/NLA-Statements-RA05.log`: `a9113431debd4e064e52337814976a3086b066f5b108978d118575c3e0dc5f32`
- `docs/lean/statements/RA-05/reviews/lean-boundary-infra-audit-evidence/Reviewed-RA05.log`: `379e56f94e95849d4009de92e37dd0b0d788540ed100dd0d7dd1227f3cba1423`
- `docs/lean/statements/RA-05/reviews/lean-boundary-infra-audit-evidence/identity.log`: `444877cc97ebe701659d5ede91bb398ffc6969f4684c33a63b9ac1f10e51f57f`
- `docs/lean/statements/RA-05/reviews/lean-boundary-infra-audit-evidence/result.json`: `3e1e441c306f7514dca85124dd65945251d8a36b9f5008780517a17f5632d61c`
- `docs/lean/statements/RA-05/source-lock.json`: `d222ee4017511ce05172f25cc71730c4f810bfabf0145052b75aa98a2db56c06`
- `lean-statements/NLA/Statements/Infrastructure.lean`: `8e019f11ea18ec66b50563648c39af76e41881912a3fb5f56002adf1850fcc37`
- `lean-statements/NLA/Statements/RA05.lean`: `3438fe4ca2bcf313f3336c94f6a2105b83ee918b5d266009efc0c4f76c121e1e`
- `lean-statements/Reviewed/RA05.lean`: `11bf3da749f66e792c01f3c1f1047bf69dea0f4fbb3110f663fae74af67c435a`
- `lean-statements/lake-manifest.json`: `a19377882192a9dbfc01c4d4e73edd887a8de91f735edabaeff2dfa38a4b4ec8`
- `lean-statements/lakefile.toml`: `1e061d7d0521587189437bc8a07b43fcc684889e70ca2e4a03e537e42b7b3a40`
- `lean-statements/lean-toolchain`: `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71`
- `randomized-and-low-rank-approximation/RA-05/README.md`: `6e03461d0079b656779e5b87d5faa91f198c4c90ea63beb613732226e678181c`
