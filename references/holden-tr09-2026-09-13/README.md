# TR-09: local ALS rates and an algebraic comparator

**Author:** Sidney Holden  
**Affiliation:** Center for Computational Biology, Flatiron Institute, Simons Foundation  
**Submitted:** 13 September 2026  
**Catalog status:** Open; supporting results only, not a full or restricted random-start resolution.

The current [Simons Foundation profile](https://www.simonsfoundation.org/people/sidney-holden/) and [Biological Transport Networks staff directory](https://www.simonsfoundation.org/flatiron/center-for-computational-biology/about/people/?group=biological-transport&type=ccb-staff), checked on 13 September 2026, identify Sidney Holden as a Flatiron Research Fellow in CCB. The affiliation above is based on these institutional sources; no email or institutional endorsement is asserted.

## Manuscript and scope

[Author-attributed report](report.pdf) · [Editable source](report.tex) · [Independent review](independent-review.md) · [Original TR-09 target](../../tensor-computations/TR-09/README.md).

Theorem 4.1 bounds the derivative of a specified mixed-block ALS cycle by 1/8 when two normalized factor Gram matrices are sufficiently close to identity; Corollary 4.2 gives a pointwise local basin and residual-halving rate. Theorem 5.1 supplies a smoothing event for two orthogonal base modes. Proposition 6.1 illustrates nonuniform design neighborhoods. Theorem 7.1 gives exact 2r-1-term algebraic recovery with probability at least 3/4 and polynomial field arithmetic under its stated rank and noncollinearity assumptions.

These are supporting theorems. The local results do not prove input-independent random-start success, even for the restricted base family; the global comparator is not an allowed optimization trajectory. TR-09 remains Open, with its full original target unchanged. No result here warrants Solved or Lean verified. No Lean verification was performed.

## Provenance and review

The user supplied [TR09_round5_research.zip](TR09_round5_research.zip); its original files are preserved under [submitted/](submitted/README.md). The attributed edition changes only the author/date and the review disclosures. Original manifest and audit claims describe the supplied archive, not this later submission. The bundled PROOF_AUDIT is author-supplied scope commentary, not independent review. The historical fourth-round report is retained as provenance and is not separately certified.

A separate Codex AI agent reviewed the mathematical argument and target correspondence; see its signed report. AI assistance was used for this submission's preparation and informal review. This is not external human peer review, a novelty/priority certification, or formal verification. Arvanitakis, Srinivas and Vijayaraghavan retain credit for the source problem, and all manuscript prior-source citations are retained.

Duplicate check on 13 September 2026: upstream main at 5830ed4, the fork's published main, all returned upstream PR titles/bodies, and published fork branch names showed no earlier full TR-09 solution. This submission introduces no new problem ID and incorporates no unrelated pending PR.

Reproduction commands and the original 12 unit tests, 25 exact-check records, and 276 numerical diagnostics are documented in submitted/README.md. Fresh checks are recorded in the independent review and validation record; finite tests are evidence about implementations, not proofs of the general theorems.
