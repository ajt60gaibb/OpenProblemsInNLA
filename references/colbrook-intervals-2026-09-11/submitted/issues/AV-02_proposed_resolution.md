# [AV-02] Proposed resolution: NP-hard spectral inverse-norm threshold, even for triangular integer data

## Problem

https://github.com/ajt60gaibb/OpenProblemsInNLA/tree/main/intervals-and-absolute-value-equations/AV-02

## Proposed change

Please review the attached proof as a proposed resolution. A repository status change should follow mathematical review; this draft does not represent maintainer acceptance.

## Precise claim

Deciding max_{d in [-1,1]^n} ||(A-diag(d))^{-1}||_2 >= t is NP-hard under a polynomial many-one reduction. It is NP-complete on rational upper-triangular matrices with diagonal 2; hardness already uses integer matrices and thresholds.

## Proof overview

An upper-right inverse block encodes squared cut size through a graph incidence matrix. A polynomial scale separates its contribution from the remaining blocks. An integer square-root threshold gives a strict rational gap. Sherman–Morrison gives endpoint attainment, and exact positive-definiteness testing verifies an NP certificate.

## Supporting files

Attach `manuscripts/AV-02.pdf`, its `.tex` source, and `manuscripts/common.tex`, or replace these local references with a stable public manuscript link. The archive also contains exact checks, numerical diagnostics, and a machine-generated verification summary. The written proof, rather than finite tests, is the basis of the claim.

## Scope and limitations

All constructed diagonal perturbations are automatically regular. NP membership is claimed for the explicit triangular class, not for arbitrary recognition of the regularity promise.

## References and attribution

Primary references are in the manuscript. This is an AI-generated draft prepared for independent review; no prior publication, human authorship, or institutional affiliation is asserted. The submitter should establish authorship and attribution and review correctness and novelty before posting. No issue has been posted by preparation of this package.
