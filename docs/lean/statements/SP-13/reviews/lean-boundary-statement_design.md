# SP-13: independent final Lean-boundary review

Reviewer: /root/statement_design (OpenAI Codex AI agent), 2026-09-28.
Verdict: **approve** for these bound bytes.

## Exact fidelity

1. The actual closed target retains arbitrary dependent complex n-by-n sequences H,E, the same real symbol f, Hermitian H at every n, the original spectral-distribution premise and only nuclear(E_n)/n -> 0. E and H+E are not assumed normal or bounded.

2. Hermitian expands to conjugate symmetry. NuclearNorm sums exactly the first n singular values of the complex Euclidean linear map, using zero-based Fin n indices. The pinned API includes multiplicities and zero padding; this is the trace norm, not an entrywise or Frobenius norm.

3. Empirical divides in Complex by n and sums the complete characteristic-root multiset after mapping F. The imported characteristic polynomial is det(tI-A), monic of degree n. Over Complex its n roots include algebraic multiplicity; no simple-spectrum or diagonalizability premise is introduced.

4. Distributed quantifies every Complex->Complex continuous compactly supported F. Its limit uses complex nhds and atTop on natural n. The n=0 value is immaterial to either atTop limit; Hermitian symmetry at size zero is vacuous.

5. SymbolIntegral uses the real symbol embedded in Complex, and genuine Lebesgue volume restricted to Icc 0 1. Target only requires AEMeasurable relative to that same measure. Null modifications and arbitrary exterior values remain irrelevant, with no hidden Borel measurability or integrability requirement on f itself.

6. Continuous compactly supported tests are bounded and measurable. Their composition with the a.e.-measurable real symbol is integrable on the finite interval, so the Bochner integral is the intended integral rather than its nonintegrability fallback.

7. Quantifier order, both limits, same f, non-strict norm-small limiting condition and full complex test domain match the approved final specification. No sampled or stronger known special case was substituted.

8. Complete original/specification and implementation notes were compared to the actual source. The frozen copy is mechanically identical except the documented leading comment and namespace rename. The hash bindings include the transitive local source closure, pins and notes.

9. The source defines, rather than proves, Target. Global kernel trust and both statement/trust assertions are present. The retained pinned macOS live/frozen logs report the standard three axioms; the author-local root receipt reports exit zero for these modules and rfl identity checks. This reviewer inspected those records but did not independently rerun Lean or Linux Comparator.

## Pinned external definitions inspected

- Mathlib/Analysis/InnerProductSpace/SingularValues.lean: ce8193fcd5d226845a71f66b8ca7ad385358916a6e0e688745410ac412ed5c81; Zero-indexed eigenvalue square roots of the adjoint composition, multiplicities retained and zero-padded after domain dimension.
- Mathlib/Analysis/InnerProductSpace/PiL2.lean: 1f9827b2db67213c725a2dcc3fec52a87772966d1fbd3fc6857a019dbd7a6053; Matrix.toEuclideanLin is Matrix.toLpLin 2 2, with Euclidean domain/codomain.
- Mathlib/Algebra/Polynomial/Roots.lean: 162d86710afc10cc3ed158236994ed020e589f7fa15d5b39a30bd3e1f153080c; roots is the full root multiset with multiplicity.
- Mathlib/LinearAlgebra/Matrix/Charpoly/Basic.lean: 584eb12d39eacb591155c98cfa2089479d88cfdea8eb5f31ba5ed687de200a9a; charpoly is det(tI-A), through charmatrix.
- Mathlib/LinearAlgebra/Matrix/Charpoly/Coeff.lean: 465ebaa7462113f8c411a1bbfb582309a0224786c69ff381db8b78ed986e6eef; charpoly_natDegree_eq_dim and charpoly_monic ensure degree n and nonzero monic polynomial.
- Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean: d12213c6a6b65c3c7f8086d2cde7e1d287696a0992954b02dc00650c25c5fff1; AEMeasurable means equality almost everywhere to a measurable representative.
- Mathlib/Topology/Algebra/Support.lean: aab196644260f0c77d8aab52c3151df9c49880c1e9b8ee08cb97193a6ef994a9; HasCompactSupport is the additive version of compactness of the topological support.

## Bound inputs

- docs/lean/statements/SP-13/IMPLEMENTATION_NOTES.md: 2860c32cd0e97149cbc967f3859b618d0cd785cdc66c4da88d6af4651134fbc3
- docs/lean/statements/SP-13/NUMERICAL_TARGETS.md: 5f10905d6e0acfc2469a470321b310038e8d30ddb66d58bdf4b560b733fa7e60
- docs/lean/statements/SP-13/ORIGINAL.md: 3db39d15a2d3879c0e72a983dd78197bcc8b99ac256a07fcaeee5b6f0962a57a
- docs/lean/statements/verification/2026-09-28-spectral-hankel/CheckSpectralHankel.lean: 59a4c13e5624787c2af2cf7c07fa7e98db574bfed2fecacf924e8433a7ab0a41
- docs/lean/statements/verification/2026-09-28-spectral-hankel/CheckSpectralHankel.log: 1797afd3028dada80af15ade3887c347c346978237cd707a058d188fb3f2b412
- docs/lean/statements/verification/2026-09-28-spectral-hankel/NLA-Statements-SP13.lean.log: 92a7d7f26a2939678b592687f8520f16aeb7eb1b3558c83b550410f6bc45fa94
- docs/lean/statements/verification/2026-09-28-spectral-hankel/Reviewed-SP13.lean.log: be873456de4999ca5516e06405e1a4c436ed7b90aad60b07afe67fa76bcae16f
- docs/lean/statements/verification/2026-09-28-spectral-hankel/receipt.json: 0fd2fe5b25646c0794268333e35e0815dc617c397fc38d6eba125ad9095f0881
- eigenvalues-and-inverse-problems/SP-13/README.md: 3db39d15a2d3879c0e72a983dd78197bcc8b99ac256a07fcaeee5b6f0962a57a
- lean-statements/NLA/Statements/Infrastructure.lean: 8e019f11ea18ec66b50563648c39af76e41881912a3fb5f56002adf1850fcc37
- lean-statements/NLA/Statements/SP13.lean: 59b9796c201eb0991479586d4372bbaf4500ad26fcfadd2bb5691c29653b089b
- lean-statements/Reviewed/SP13.lean: d1af51cd8b565dbcaee8ed9e73764cb0816955038dcffb3862abfe0ce37bcb9c
- lean-statements/lake-manifest.json: a19377882192a9dbfc01c4d4e73edd887a8de91f735edabaeff2dfa38a4b4ec8
- lean-statements/lakefile.toml: 1e061d7d0521587189437bc8a07b43fcc684889e70ca2e4a03e537e42b7b3a40
- lean-statements/lean-toolchain: 3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71

## Limits

Independent AI-agent source-level final boundary review, independent of /root, who authored the specification and implementation. It approves mathematical/model correspondence of the exact definition bytes, not the truth of the catalog problem. Author-local root compile receipts were inspected as evidence; no independent execution or Linux Comparator pass is asserted here.
