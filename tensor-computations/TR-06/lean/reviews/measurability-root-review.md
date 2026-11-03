# Independent measurable-locus contribution review

Reviewer: `/root`, Codex AI agent. Date: 24 September 2026.
Verdict: approve integration of Measurability.lean, SHA-256
`f190029361743ded166300e47794424956bd55542aab744c50bc4ccd1b51a2a6`.
The exact hypothesis-free theorem and route were independently reviewed before
implementation; that approval and the proposed statement are retained by the
author. I read the final source and independently reran a source snapshot.

The proof uses finite real factor spaces, with their ordinary product topology,
only as parameter spaces. All output tensors and frozen definitions retain
the Frobenius norm. Nonzero pure-summand tuples form an open set. A locally
closed subset of a locally compact, second-countable space is sigma compact;
its continuous image in a Hausdorff tensor space is a countable union of compact,
hence closed, sets. This validates the Borel image step without the false claim
that arbitrary Borel images are Borel.

Every image characterization proves both directions from actual factor
witnesses and nonzeroness. ExactRank removes every shorter decomposition locus.
Failure of Identifiable is represented by two nonzero factor tuples with equal
sum and disagreement under every permutation. Equal sum is closed; the finite
permutation-disagreement condition is open. Vacuous identifiability outside
the decomposition locus and empty rank-zero tuples are handled by these exact
logical equivalences, with no tacit positivity assumption.

The final intersection/difference equals the frozen identifiableRealSet. The
argument proves neither generic full dimension nor nullity with respect to
induced Hausdorff volume, and is not used to claim either. Local Lean 4.33.1
elaboration and all four standard-three-axiom/LeanCert kernel assertions pass.
This is a local development contribution review, not whole-TR06 approval,
Linux reproduction, Comparator acceptance, or a human peer review.
