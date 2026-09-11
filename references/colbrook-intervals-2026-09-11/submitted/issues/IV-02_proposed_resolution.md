# [IV-02] Proposed resolution: NP-hard exact tridiagonal determinant range, including regular families

## Problem

https://github.com/ajt60gaibb/OpenProblemsInNLA/tree/main/intervals-and-absolute-value-equations/IV-02

## Proposed change

Please review the attached proof as a proposed resolution. A repository status change should follow mathematical review; this draft does not represent maintainer acceptance.

## Precise claim

The upper determinant threshold for rational tridiagonal interval matrices is NP-complete. Exact determinant-range computation is NP-hard even when the entire family is regular and the superdiagonal is fixed at 1.

## Proof overview

A PARTITION reduction implements rational rotations and independent reflection gates by continuant matrices. Vertex determinants are cosines of signed small-angle sums. Rational error and threshold bounds distinguish partitions, while positivity at every vertex proves regularity throughout the box.

## Supporting files

Attach `manuscripts/IV-02_IV-04.pdf`, its `.tex` source, and `manuscripts/common.tex`, or replace these local references with a stable public manuscript link. The archive also contains exact checks, numerical diagnostics, and a machine-generated verification summary. The written proof, rather than finite tests, is the basis of the claim.

## Scope and limitations

This is ordinary bit-complexity NP-hardness, not strong NP-hardness. It does not exclude pseudo-polynomial or approximation algorithms. The same manuscript also resolves IV-04.

## References and attribution

Primary references are in the manuscript. This is an AI-generated draft prepared for independent review; no prior publication, human authorship, or institutional affiliation is asserted. The submitter should establish authorship and attribution and review correctness and novelty before posting. No issue has been posted by preparation of this package.
