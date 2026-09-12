# IE-26 submission and verification record

**Author:** George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA.

**Affirmative resolution prepared:** 12 September 2026 (UTC). The complete proof passed a separate independent agent audit for both retained targets; canonical status is Solved under the repository's informal-review definition.

The [complete manuscript](../../linear-systems-and-elimination/IE-26/solution.md) addresses both bounds in the retained [IE-26 statement](../../linear-systems-and-elimination/IE-26/README.md): the uniform Lebesgue estimate for all `0 < alpha < 1/2`, and the square normalized Fourier inverse-norm estimate for every fixed `1/4 < alpha < 1/2`. The second assertion has no logarithmic loss. No endpoint assertion at `alpha=1/4` is made. The first constant is absolute, and the second may depend on the fixed alpha.

## Attribution and review level

Austin and Trefethen formulated the two conjectures; Austin's thesis records their norm conventions and parameter dependence. Chen, Lin, and Zhang's August 2026 preprint supplies the prior upper bound with a logarithm for the second target. Laugesen's periodic Hilbert-transform weak `(1,1)` theorem is the one external harmonic-analysis estimate used by the new proof; its precise application is explained in Lemma 4. Primary references and theorem/page locators are in the manuscript. No priority claim is made.

The argument was prepared with substantial AI assistance. The originating agent was `/root/review_aa01`. The coordinating agent `/root` contributed an overlapping first-bound derivation before the source was frozen, so its [coordinating mathematical check](verification/IE-26-coordinating-math-check.md) is explicitly not an independent audit. The separate agent `/root/prepare_manuscripts` returned [full-target PASS](verification/independent-review/IE-26-independent-review.md), with no mathematical correction. Its report is 18,070 bytes, SHA-256 `995aa6144f2e8875c9e330d84230786ee46be45a18e5e28cef0b6fc6fef4ce92`. The [review manifest](verification/independent-review/manifest.json), candidate/target snapshots, source notes and exact supplement are retained unchanged. Agent review is informal mathematical checking, not external human peer review or formal verification.

## Exact frozen source and provenance

- [Original candidate](verification/RESULT.md): 20,755 bytes, SHA-256 `5ce6d660bb1b22f0c4dec439934e883b3e014708e49a63de2dba2760c939d295`.
- Its mathematical Sections 1–7: 16,618 bytes, SHA-256 `0f9222764933df1602163748f6d8c8755f7e45ab9e25139733d2b92851879f55`. This complete body is retained byte-for-byte in the publication Markdown.
- [Original canonical statement](verification/canonical-statement.md): 5,051 bytes, SHA-256 `c7d4e909081c37d0e7ea7e7b97c17c39a45e794e55f3165b09a34e4519fd185b`.
- [Original source manifest](verification/manifest.json) and [coordinating check](verification/IE-26-coordinating-math-check.md) are preserved unchanged. The original candidate's pending-review language is historical provenance; the final publication's review notice records the later outcome separately.

Presentation and verification metadata outside Sections 1–7 may change during packaging. The original statement, evidence, references, and dated search history beginning with `## Statement` in the canonical README are retained exactly. The entire permanent 217-ID registry is unchanged.

## Eligibility evidence

The [sanitized public-network snapshot](verification/network-check.json) preserves the audit at `2026-09-12T01:36:52.722173+00:00`: all 40 public branch heads across five repositories, the canonical versions and inspected text fingerprints. Existing canonical pages were Open. The matching PR111 is the admission record, not a resolution. The [read-only audit script](verification/audit_public.py) records the bounded path/discussion search and supports `GH` or GitHub CLI on `PATH`.

The private original snapshot's SHA-256 is `2fd9a18c2fae1029e4fcef36cb6232922ec78f872ad8137f22021b3fdec91098`. Unrelated discussion bodies, account metadata, and contact details are omitted from the public copy. The search excludes private, deleted, unpublished, and unidentifiably named material; it is not a universal priority certificate.

The [final broader audit](verification/final-public-audit/README.md), completed at **2026-09-12 02:10:34 UTC**, checked all five public repositories and 40 heads, 38 unique trees, 108 selected text blobs and 32 PR-review bodies through 34 endpoints, including broad relevant issue/PR/comment searches. IE-26 was Open on 11 heads and absent on 29 older heads; it was Open on current upstream `1f22006bdaa4659fcaa0bb775a887685cd3cc566`. Only admission PR111 matched, with no competing resolution. The sanitized record has SHA-256 `c63bb31d6d76736e49c264cf276c9ae2d4c02a7086e683b6bf7fd18411f84d29`. The earlier narrower snapshot is retained separately; no date or coverage claim is retroactively changed.

## Supplementary checks

The [identity diagnostic](verification/check_identities.py) and [frozen output](verification/identity-checks.json) test three deterministic floating-point instances of the residue, positive-real, and Fourier/cardinal identities. They do not prove the quantified estimates, certify optimal constants, or replace the analytic argument. Their limitation is explicit in the frozen source and publication manuscript.

The independent reviewer also supplied a [Gaussian-rational exact checker](verification/independent-review/exact_algebra_check.py) and [output](verification/independent-review/exact-algebra-output.json) covering 12 grouped identities. That finite supplement does not certify the all-grid estimates; the signed report supplies the analytic audit. The coordinating agent separately reran the independent exact checker; its [output](verification/root-exact-check-rerun.json) also passes the same 12 grouped identities. This is a reproducibility check, not an additional independent all-grid proof. [Document checks](verification/document-checks.md), [exact artifact checkpoints](verification/source-checkpoints.json), and the [portable submission checker](verification/check_submission.py) record the final conversion, identifiers, links, attribution and all-page PDF inspection. No third-party PDF, page image, or extracted source text is included in this submission.

## Final publication-conversion check

The [coordinating conversion addendum](verification/coordinating-conversion-review.md) records the final source comparison, all 12 individually inspected PDF pages and exact author/affiliation checks. It is separate from the independent mathematical audit because the coordinator contributed to the proof. [Final consistency results](verification/coordinator-final-checks.json) include the three status tests in addition to the 17 permanent-ID tests.
