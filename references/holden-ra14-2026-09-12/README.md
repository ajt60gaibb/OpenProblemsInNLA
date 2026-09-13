# RA-14 partial research submission — Sidney Holden

**Author:** Sidney Holden. **Affiliation:** Biological Transport Networks, Center for Computational Biology, Flatiron Institute, Simons Foundation. The [official institutional profile](https://www.simonsfoundation.org/people/sidney-holden/) identifies Holden as a Flatiron Research Fellow in this group; checked 12 September 2026. No email address is included.

**Status: Partially resolved; the full RA-14 target remains open.**

[Research note](package/report.pdf) · [LaTeX source](package/report.tex) · [Independent informal AI-agent review](independent-review.md) · [Original problem](../../randomized-and-low-rank-approximation/RA-14/README.md)

Theorems 1.1 and 1.2 summarize the universal bounds, large-rank regime and polynomially-large-dimension regime. Section 2 proves the rank lower bound and exact promised-rank complexity. Theorem 5.1 proves the spectral-to-PCA postprocessor under its stated symmetric spectral-gap promises; Section 6 imports and applies the PCA lower bound. Section 7 gives exact rank padding. Section 8 explicitly records the unresolved simultaneous finite-parameter regimes. Imported theorems are attributed to their original authors; no priority claim is made.

## Provenance and review

Submitted archive: `RA14_research_package.zip` (SHA-256: ee26a885e89df0861902cd75efae18613aaae881117bedae5b8804f75f2206bd). All 18 original manifest checksums passed before editing. The original manifest is retained as `package/ORIGINAL_SHA256SUMS`; the current `SHA256SUMS` covers the attributed package. Editorial changes add the requested author and verified affiliation to the source, PDF and metadata, retaining disclosure that the note was AI-generated. Mathematical content is unchanged. The original package's `independent_peer_review: false` continues to mean no external human peer review.

A separate Codex AI agent reviewed the mathematical argument and primary dependencies; its report records the exact scope and limitations. This is informal review, not formal verification or external human peer review. No Lean verification was performed, as requested.

Duplicate screening on 12 September 2026 checked current upstream main, fetched fork branches, RA-14 pull-request search, and the author's prior submissions. No previously pushed full RA-14 solution was found. The prior spectral submission (#181) concerns other problem IDs. This contribution retains RA-14's ID, path, original statement and Partially resolved status.

## Reproduction

The package's 18 unit tests were rerun with Python 3.12, NumPy 2.3.5 and SymPy 1.14.0; see [rerun log](test-rerun.txt). These finite checks support implementation and identities, not the universal oracle lower bound. Original experiment data and the 19 reported unsuccessful Krylov trials are retained without alteration. See [package instructions](package/README.md) for commands and [source notes](package/SOURCE_NOTES.md) for theorem dependencies.
