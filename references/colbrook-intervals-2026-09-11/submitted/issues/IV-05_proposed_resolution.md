# [IV-05] Proposed resolution: Exact inverse-M solution hulls using 2n LPs

## Problem

https://github.com/ajt60gaibb/OpenProblemsInNLA/tree/main/intervals-and-absolute-value-equations/IV-05

## Proposed change

Please review the attached proof as a proposed resolution. A repository status change should follow mathematical review; this draft does not represent maintainer acceptance.

## Precise claim

Under the promise that every interval matrix member is inverse-M, the exact interval solution hull for an arbitrary interval right-hand side can be computed using 2n rational linear programs.

## Proof overview

For each endpoint sign pattern, solve Cx-D_sigma R|x|=b_sigma. With P=C-D_sigma R, Q=C+D_sigma R, minimize 1^T y subject to Q^{-1}y>=0 and P^{-1}(y+b_sigma)>=0. The M-matrix off-diagonal signs force complementarity at an optimum. A secant inverse-sign argument proves that the resulting coordinate is an attained hull endpoint.

## Supporting files

Attach `manuscripts/IV-05.pdf`, its `.tex` source, and `manuscripts/common.tex`, or replace these local references with a stable public manuscript link. The archive also contains exact checks, numerical diagnostics, and a machine-generated verification summary. The written proof, rather than finite tests, is the basis of the claim.

## Scope and limitations

The general regular AVE problem AV-03 is not solved by this argument. Its LP complementarity proof needs the inverse-M signs. IV-03 can separately recognize the promise but is not needed for correctness under that promise.

## References and attribution

Primary references are in the manuscript. This is an AI-generated draft prepared for independent review; no prior publication, human authorship, or institutional affiliation is asserted. The submitter should establish authorship and attribution and review correctness and novelty before posting. No issue has been posted by preparation of this package.
