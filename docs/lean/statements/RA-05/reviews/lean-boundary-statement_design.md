# RA-05: independent final Lean-boundary review

Reviewer: /root/statement_design (OpenAI Codex AI agent), 2026-09-28.
Verdict: **approve** for these bound bytes.

## Fidelity reasoning

1. The complete canonical README, exact independently preapproved specification, live/frozen definitions and implementation notes were inspected. Classification answers the original unrestricted joint size question; OriginalAdditiveConjecture preserves the complete literal subsidiary proposal; NegativeAnswer negates that proposal separately for each real p>2; Target conjoins both resolved answers. None is presented as a proved theorem.

2. Projector is exactly real symmetry, idempotence and actual Matrix.rank<=k. The pinned rank is finrank of the matrix multiplication range. Real symmetric idempotents are precisely Euclidean orthogonal projections, including zero and every lower dimension, so the quantification covers all original subspaces rather than a chosen test family.

3. RowCost expands every component of the original row residual A_i-A_i*P, sums all squared real components, takes Real.sqrt, then the genuine real p-th power. StrongCoreset requires one vector of arbitrary nonnegative real weights and both non-strict relative inequalities simultaneously for every allowed projector. Cost and weighted cost sum all rows; zero cost, negative matrix entries and fractional weights remain.

4. SupportSize counts actual nonzero row indices using a finite filter. MinimumSupport is the natural infimum of feasible support budgets. On every target input, all-one weights give exact equality and budget n, so the set is nonempty and the natural infimum is its least element. A witness at that least budget must have exactly the minimum support. Empty rows remain legitimate.

5. WorstSupport uses the actual complete lattice supremum in ENNReal over all natural n,d with k<d and every real matrix. A potentially unbounded family retains infinity; no real conditional-supremum default weakens the lower bound. Natural supports embed exactly, and ENNReal.ofReal is applied only to positive finite rate expressions on the target domain.

6. EvenPower is exactly existence of a natural s>=2 with p=2*s. Rate preserves both even branches inside a minimum and the non-even single branch. Every exponent including (p+1)/2 and p/2-1 is real, with divisions and addition in the specified order. LowerLogLoss is exactly zero or 5*p/2+3; the common upper logarithmic exponent is p+5.

7. Classification quantifies each real p>2 before positive finite c,C with c<=C, then every k>=1 and every 0<epsilon<1/2. LogScale is log(2*k/epsilon)>1 on this full domain. Both bounds compare the same unrestricted WorstSupport, with no rank, ambient dimension, conditioning or accuracy cutoff.

8. AdditiveProposal chooses its two positive real constants before all n,d,k,A,epsilon. Its bound is exactly C*(k^(p/2)/epsilon+k/epsilon^2)*log(2*k/epsilon)^c. OriginalAdditiveConjecture universally quantifies p>2, whereas NegativeAnswer universally negates the whole fixed-p proposal, including all attempted constants. This retains every fixed real exponent and is not merely one p=4 counterexample.

9. The actual local import closure adds only Infrastructure beyond pinned external definitions. All four named propositions are closed and separately checked by #assert_statement and #assert_trust kernel under the explicit global kernel option. There is no target axiom, supplied cost semantic parameter or target proof.

10. Frozen bytes differ only by the standard frozen comment and namespace. The retained root author-local receipt source hashes match the reviewed live/frozen files. Its logs show successful elaboration and actual rfl identities for all four named propositions, with only propext, Classical.choice and Quot.sound. This reviewer inspected retained author-executed results, without claiming independent execution or Linux Comparator validation.

## Pinned external definitions inspected

- Mathlib/LinearAlgebra/Matrix/Rank.lean: 67b4fa7bee02c1806f29562718bfb34c0e1f40af5ec6a91ef91cc33610657491
- Mathlib/Data/ENNReal/Real.lean: d0a0778e60ecadea09e8233f5a9228f0aa1b94e85745b4d86f59268ce4b863fd
- Mathlib/Analysis/SpecialFunctions/Pow/Real.lean: 1f4e64fc28a20f4e19291a94dafd68daa82588b46f6ee5b9203df373ba595fa3

## Bound inputs

- docs/lean/statements/RA-05/IMPLEMENTATION_NOTES.md: 8ad7b1c06221e8fa13b8b26437b0596f7fcfb83bbd3fa51daea20bbffdd05bf8
- docs/lean/statements/RA-05/NUMERICAL_TARGETS.md: 23a9cb637b7b1456fe0a0f06f3ee414c3c7dbcfc5c80a69fc303b7e347166ac5
- docs/lean/statements/RA-05/ORIGINAL.md: 6e03461d0079b656779e5b87d5faa91f198c4c90ea63beb613732226e678181c
- docs/lean/statements/verification/2026-09-28-coreset-classification/CheckRA05.lean: 83422ac9b8ca36f22b727640612ae4e623bea05022814474073c25d10bc47d60
- docs/lean/statements/verification/2026-09-28-coreset-classification/CheckRA05.log: 40987f42ba89e51d66ec30d413e25f1450eace6bca3c001232401d9ac46ca1aa
- docs/lean/statements/verification/2026-09-28-coreset-classification/NLA-Statements-RA05.lean.log: 5982602a1ad405247f67a8e18077e37b1d756d8dacc9d6c9cf57b50bd1652c5c
- docs/lean/statements/verification/2026-09-28-coreset-classification/Reviewed-RA05.lean.log: 32b5c79fbe92766a7f0416e3b158134aa050f0a3a7fce5632c7fa93f6ef038ab
- docs/lean/statements/verification/2026-09-28-coreset-classification/receipt.json: a3001c78959517645765e94b3f5778db75858d09d242e25fd040527131ecc457
- lean-statements/NLA/Statements/Infrastructure.lean: 8e019f11ea18ec66b50563648c39af76e41881912a3fb5f56002adf1850fcc37
- lean-statements/NLA/Statements/RA05.lean: 3438fe4ca2bcf313f3336c94f6a2105b83ee918b5d266009efc0c4f76c121e1e
- lean-statements/Reviewed/RA05.lean: 11bf3da749f66e792c01f3c1f1047bf69dea0f4fbb3110f663fae74af67c435a
- lean-statements/lake-manifest.json: a19377882192a9dbfc01c4d4e73edd887a8de91f735edabaeff2dfa38a4b4ec8
- lean-statements/lakefile.toml: 1e061d7d0521587189437bc8a07b43fcc684889e70ca2e4a03e537e42b7b3a40
- lean-statements/lean-toolchain: 3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71
- randomized-and-low-rank-approximation/RA-05/README.md: 6e03461d0079b656779e5b87d5faa91f198c4c90ea63beb613732226e678181c

## Limits

Independent AI-agent source-level final review, independent of specification and implementation author /root. Approval concerns fidelity of these exact definitions and source bytes. Author-local kernel evidence was inspected, not independently executed by this reviewer. Neither target truth, supporting correspondence theorems, computational certification nor Linux CI is asserted.
