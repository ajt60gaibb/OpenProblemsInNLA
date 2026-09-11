# [IV-06] Proposed resolution: Counterexample: a 3x3 interval matrix with four separated real-eigenvalue components

## Problem

https://github.com/ajt60gaibb/OpenProblemsInNLA/tree/main/intervals-and-absolute-value-equations/IV-06

## Proposed change

Please review the attached proof as a proposed resolution. A repository status change should follow mathematical review; this draft does not represent maintainer acceptance.

## Precise claim

The proposed bound of n connected components is false in general. The matrix [[25,a,b],[1,-1,0],[1,0,1]], with independent a in [-166,-16] and b in [9,159], has at least four real-eigenvalue components.

## Proof overview

The values -3,0,3,25 have explicit integer eigenvectors at admissible parameter choices. At the separators -1,1,12, the exact characteristic-determinant intervals are [-332,-32], [-318,-18], and [-3750,-150], respectively. These intervals exclude zero and separate the four included points.

## Supporting files

Attach `manuscripts/IV-06.pdf`, its `.tex` source, and `manuscripts/common.tex`, or replace these local references with a stable public manuscript link. The archive also contains exact checks, numerical diagnostics, and a machine-generated verification summary. The written proof, rather than finite tests, is the basis of the claim.

## Scope and limitations

The certificate proves at least four components; numerical component endpoints are unnecessary. It concerns the union of real eigenvalues, not a complex spectral set or an interval algorithm enclosure.

## References and attribution

Primary references are in the manuscript. This is an AI-generated draft prepared for independent review; no prior publication, human authorship, or institutional affiliation is asserted. The submitter should establish authorship and attribution and review correctness and novelty before posting. No issue has been posted by preparation of this package.
