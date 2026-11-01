# IE-11 — Ma–Wu global-bound manuscript and provenance

**Authors:** Qianli Ma (Zhejiang University; WUJIE AI) and Chao Wu (Zhejiang University).
**Catalog report:** 1 November 2026. **First public release:** 12 September 2026.

This contribution reports the authors' complete affirmative resolution of the exact real fifth complete-pivoting growth-factor problem. It preserves credit to Chen, Edelman and Urschel for the degree-61 constant and attaining construction. The Ma–Wu contribution is the matching global upper bound, including every legal pivot-tie choice. The original IE-11 target is retained on the [canonical page](../../linear-systems-and-elimination/IE-11/README.md).

## Manuscript and exact-target correspondence

- [Concise main article](manuscript.pdf): 26 pages; Theorem 1.2, p. 2, states the exact maximum; Section 10, p. 25, composes the global proof.
- [Essential complete proof supplement](full-proof-supplement.pdf): 52 pages, supplying detailed analytic arguments and the proof-dependency links used by the concise article.
- [Supplementary index](supplementary-index.pdf): 9 pages, mapping the mathematical responsibilities to source, certificates and verifier entry points.

Theorem 1.2 concerns real 5 × 5 matrices, exact arithmetic, maximum element growth over the entire elimination path and every legal complete-pivoting choice, including ties. It therefore covers the displayed IE-11 supremum over nonsingular real matrices and all admissible paths. Combined with Chen–Edelman–Urschel's attaining construction, the reported upper bound gives the requested equality. This is a full global claim, rather than a numerical candidate, local maximum or result restricted to one equality pattern.

These three PDF copies reflect the concise exposition as of **1 November 2026**. They are not represented as the bytes of the September deposits. [FILE_HASHES.json](FILE_HASHES.json) identifies the retained copies.

## Dated public record

| Record | Public date | Stable link |
| --- | --- | --- |
| First public source and exact-certificate release, GitHub v1.0.0 | 12 September 2026, **10:37:12 UTC** | [Fixed release](https://github.com/hkjtsgmc79-boop/rho5-proof/releases/tag/v1.0.0) |
| Revised publication files, GitHub v1.0.1 | 12 September 2026, **15:27:15 UTC** | [Fixed release](https://github.com/hkjtsgmc79-boop/rho5-proof/releases/tag/v1.0.1) |
| First archived manuscript and supplementary index, Zenodo v1.0.1 | **12 September 2026** | [10.5281/zenodo.22727368](https://doi.org/10.5281/zenodo.22727368) |
| Expanded manuscript, Zenodo v1.0.2 | **30 September 2026** | [10.5281/zenodo.23057256](https://doi.org/10.5281/zenodo.23057256) |
| Expanded exposition, exact-replay records and further partial Lean source, GitHub v1.0.2 | 30 September 2026, **12:40:12 UTC** | [Fixed release](https://github.com/hkjtsgmc79-boop/rho5-proof/releases/tag/v1.0.2) |

The dates identify the authors' public releases and manuscript versions; the catalog-report date is separate. The earliest manuscript DOI is retained explicitly rather than replaced with only a link to the later revision.

## Verification and review scope

The proof combines written analytic arguments with external exact rational certificates. [The source repository](https://github.com/hkjtsgmc79-boop/rho5-proof) provides the verifier code, certificate download manifests, checksums, dependency information and reproduction instructions. Start with its [verification guide](https://github.com/hkjtsgmc79-boop/rho5-proof/blob/v1.0.2/docs/VERIFY.md); immutable large certificate assets remain under [v1.0.0](https://github.com/hkjtsgmc79-boop/rho5-proof/releases/tag/v1.0.0), with revised publication materials and replay documentation under [v1.0.2](https://github.com/hkjtsgmc79-boop/rho5-proof/releases/tag/v1.0.2).

The Lean development is **partial**. The final sharp equality retains the named mathematical premises `XGlobalSafety` and `RootEndpointSafety`; the entire unconditional theorem and the external Python/C++ acceptor implementations have not been formally verified in Lean. Passing partial Lean builds or checking artifact hashes does not establish a complete Lean proof of IE-11.

The manuscript discloses substantial AI assistance, the authors' oversight and their responsibility for the claims, code, data and text. This contribution does not assert journal acceptance, external human peer review or a new independent mathematical audit by this catalog. The proposed **Solution claimed** status follows the repository's definition for a primary manuscript reporting a complete resolution pending independent verification here. It is distinct from **Lean verified** and from a partially resolved mathematical target.
