# [IV-04] Proposed resolution: NP-hard exact tridiagonal solution hull, including regular families

## Problem

https://github.com/ajt60gaibb/OpenProblemsInNLA/tree/main/intervals-and-absolute-value-equations/IV-04

## Proposed change

Please review the attached proof as a proposed resolution. A repository status change should follow mathematical review; this draft does not represent maintainer acceptance.

## Precise claim

Exact solution-hull computation is NP-hard for rational tridiagonal interval systems, even for a regular family with all superdiagonal entries 1 and the point right-hand side -e_n.

## Proof overview

Use the regular even-dimensional tridiagonal family constructed for IV-02. Its inverse corner entry is -1/det(T). For b=-e_n, the first solution coordinate is 1/det(T), so its lower hull endpoint is the reciprocal of the maximum determinant.

## Supporting files

Attach `manuscripts/IV-02_IV-04.pdf`, its `.tex` source, and `manuscripts/common.tex`, or replace these local references with a stable public manuscript link. The archive also contains exact checks, numerical diagnostics, and a machine-generated verification summary. The written proof, rather than finite tests, is the basis of the claim.

## Scope and limitations

All reduction instances have nonempty bounded solution sets. This is an exact-output hardness result, not an approximation lower bound. Please cross-reference the proposed IV-02 resolution.

## References and attribution

Primary references are in the manuscript. This is an AI-generated draft prepared for independent review; no prior publication, human authorship, or institutional affiliation is asserted. The submitter should establish authorship and attribution and review correctness and novelty before posting. No issue has been posted by preparation of this package.
