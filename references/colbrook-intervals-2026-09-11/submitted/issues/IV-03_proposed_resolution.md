# [IV-03] Proposed resolution: An n^2-vertex inverse-M criterion

## Problem

https://github.com/ajt60gaibb/OpenProblemsInNLA/tree/main/intervals-and-absolute-value-equations/IV-03

## Proposed change

Please review the attached proof as a proposed resolution. A repository status change should follow mathematical review; this draft does not represent maintainer acceptance.

## Precise claim

For [C-R,C+R], let D_i have a single -1 in diagonal position i and +1 elsewhere. Every interval member is inverse-M if and only if all n^2 vertices C-D_i R D_j are inverse-M. Thus the proposed 2n^2 criterion holds, with half its tests unnecessary.

## Proof overview

Induction establishes all proper principal blocks. Two-index Schur-complement entries are minimized at the specified vertices. An adjugate completion lemma then proves positive full determinant without assuming regularity in advance.

## Supporting files

Attach `manuscripts/IV-03.pdf`, its `.tex` source, and `manuscripts/common.tex`, or replace these local references with a stable public manuscript link. The archive also contains exact checks, numerical diagnostics, and a machine-generated verification summary. The written proof, rather than finite tests, is the basis of the claim.

## Scope and limitations

Zero entries, zero widths, reducible matrices, and dimensions one and two are handled explicitly. O(n^5) is an arithmetic-operation count; polynomial rational bit complexity is asserted separately.

## References and attribution

Primary references are in the manuscript. This is an AI-generated draft prepared for independent review; no prior publication, human authorship, or institutional affiliation is asserted. The submitter should establish authorship and attribution and review correctness and novelty before posting. No issue has been posted by preparation of this package.
