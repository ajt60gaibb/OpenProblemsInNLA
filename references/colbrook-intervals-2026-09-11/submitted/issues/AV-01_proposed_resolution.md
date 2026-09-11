# [AV-01] Proposed resolution: Polynomial recognition of exactly 2^n AVE solutions

## Problem

https://github.com/ajt60gaibb/OpenProblemsInNLA/tree/main/intervals-and-absolute-value-equations/AV-01

## Proposed change

Please review the attached proof as a proposed resolution. A repository status change should follow mathematical review; this draft does not represent maintainer acceptance.

## Precise claim

The equation Ax+|x|=b has exactly 2^n distinct solutions if and only if b>0, the polyhedron P={y:(A+I)y<=b,(A-I)y<=b} is bounded, and b-Ay has no zero coordinate anywhere on P. These conditions are decided by n+1 rational LP feasibility tests.

## Proof overview

Necessity uses orthant incidence counting and multiaffine Cramer determinants. Sufficiency uses paired facets: every vertex selects one inequality per pair, and an edge walk flips any selected pair. The normalized recession test handles boundedness without any regularity promise.

## Supporting files

Attach `manuscripts/AV-01.pdf`, its `.tex` source, and `manuscripts/common.tex`, or replace these local references with a stable public manuscript link. The archive also contains exact checks, numerical diagnostics, and a machine-generated verification summary. The written proof, rather than finite tests, is the basis of the claim.

## Scope and limitations

Includes singular and infinite-solution negative instances. The floating-point prototype is not the exact polynomial-bit LP algorithm invoked by the proof.

## References and attribution

Primary references are in the manuscript. This is an AI-generated draft prepared for independent review; no prior publication, human authorship, or institutional affiliation is asserted. The submitter should establish authorship and attribution and review correctness and novelty before posting. No issue has been posted by preparation of this package.
