# Primary sources, provenance and limits

## Immutable repository sources

Repository: https://github.com/ajt60gaibb/OpenProblemsInNLA
Commit: f41f1f9ffa2171550d4bb795862c6170c4f26070
Category: eigenvalues-and-inverse-problems
Access/audit date: 12 September 2026.

The prior session read all 13 canonical problem READMEs through the GitHub
connector at this commit. This response re-read the category README, root
README's status definitions, CONTRIBUTING.md, and KE-02, and fetched branch
metadata confirming that main still points to the same immutable commit.
The full previous canonical readings remain in the conversation; the per-problem
result files restate their targets, and `snapshot.json` records their exact paths,
Git blob SHAs, URLs and prior-session outcome metadata.

`snapshot.json` is an inherited provenance index, **not** a byte-for-byte mirror
or a log of new attempts in this audit. A command-line raw download attempt in
this audit failed due to DNS/network availability. Source reads through the
GitHub connector succeeded. No source-copy success is inferred from that failed
download. The current per-problem statements are authored transcriptions, not
claimed exact file replicas.

Root status definition:
https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/f41f1f9ffa2171550d4bb795862c6170c4f26070/README.md#problem-status
Contribution policy:
https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/f41f1f9ffa2171550d4bb795862c6170c4f26070/CONTRIBUTING.md

## Primary mathematical context checked during this audit

1. Amsel et al., *Linear Systems and Eigenvalue Problems: Open Questions from a
   Simons Workshop*, arXiv:2602.05394v3, Problem 3.2.
   https://arxiv.org/html/2602.05394v3
   The HTML text specifies the deterministic diagonal separation question and
   proposes tridiagonal Toeplitz inputs as a starting class. This supports the
   source relationship in KE-02. Theorem B's gap and runtime proof is supplied
   self-containedly here rather than attributed to the workshop report.

2. N. J. Calkin, R. M. Corless, L. Gonzalez-Vega, J. R. Sendra, J. Sendra,
   *On the maximal spread of symmetric Bohemian matrices*, arXiv:2510.15919v1,
   Sections 7-8 and introduction.
   https://arxiv.org/html/2510.15919v1
   The checked primary text gives the previously recorded finite ranges. The
   current audit uses no external Maple run as evidence for the three new-to-
   this-submission certificate sets. It does not establish that the present
   reduction or numerical parameter values have never appeared elsewhere.

3. L. W. Marcoux, P. Sarkowicz, Y. Zhang, *Kaplansky's problem and unitary orbits
   in matrix amplifications*, arXiv:2508.13834v1, Section 3.1 / Corollary 3.5.
   https://arxiv.org/html/2508.13834v1
   Checked for the self-adjoint finite-amplification result and the distinction
   between spectral matching and general normal unitary-orbit distance. The
   two-point theorem in this pack has a self-contained proof; its novelty is
   unverified.

4. J. A. Baaijens and J. Draisma, *Euclidean distance degrees of real algebraic
   groups*, LAA 467 (2015), 174-187; arXiv:1405.0422, Section 5.
   https://arxiv.org/abs/1405.0422
   This is inherited primary context from the earlier session and the pinned
   SP-03 README, not a claim of a new full-paper review in this response. The
   general count remains unevaluated. The supplied normal-space and elimination
   identities are proved explicitly, and algebraic image dimensions are
   justified via coordinate-ring transcendence degree in the self-review.

Other cited works in canonical READMEs are not claimed to have been fully
independently audited during this packaging pass. In particular no new all-paper
review of Sobczyk, Marcoux-Zhang (2021), or the full perturbation-threshold
literature is asserted. The search queries below are a bounded prior-art check,
not evidence of novelty by absence.

## Search scope and limits

Search terms included: normal matrices/two distinct eigenvalues/spectral
variation; deterministic Minami diagonal perturbation; spread/signed threshold
matrices; the exact Calkin et al. title; normal/two-point/unitary/distance;
normal matrices/two eigenvalues/matching; weak coupling/deterministic/eigenvalue
separation; tridiagonal Toeplitz/Minami. Several results were irrelevant or
insufficient to settle prior art. Only the primary sources above support the
source-specific claims. No complete novelty search was achieved.

The actual proofs do not rely on unverified nonstandard external results:
KE-02 rederives its min-max perturbation estimate and sine-spectrum spacing;
SP-09 uses the normal spectral theorem and finite-dimensional subspace counting;
SP-08 proves the finite reduction and exact root-bound criterion; SP-03 proves
its normal-space and denominator-locus arguments, using basic algebraic dimension
facts. No full third-party papers are redistributed. No credentials, private
account records, font files, or GitHub writes are included.
