# Primary sources and provenance

Historical source notes copied from the supplied archive. References to searches, PDF inspections and prior-artifact reruns below describe that original submission; the current editor’s and independent reviewer’s checks are recorded separately in [README.md](README.md) and [independent-review.md](independent-review.md).

## Exact target

Alex Townsend, *Open Problems in Numerical Linear Algebra*, entry NR-03, “Full nonnegative rank of the quadratic correlation matrix.” The entry prescribes every value `(1-a^T b)^2` and asks whether nonnegative rank is `2^n` for every `n>=3`.

https://github.com/ajt60gaibb/OpenProblemsInNLA/tree/main/nonnegative-and-positive-factorizations/NR-03

The canonical raw page read in this conversation:

https://raw.githubusercontent.com/ajt60gaibb/OpenProblemsInNLA/main/nonnegative-and-positive-factorizations/NR-03/README.md

The inspected page says “Last checked: 2026-09-11” and records a three-bit partial result. This is a source-status observation, not a statement that the new counterexample has already been accepted by the repository.

## Original conjecture

Arnaud Vandaele, Nicolas Gillis, François Glineur, and Daniel Tuyttens, *Heuristics for Exact Nonnegative Matrix Factorization*, arXiv:1411.7245, Section 6.4, Conjecture 4.

https://arxiv.org/html/1411.7245

That section states the same fixed-matrix conjecture. Its reported unsuccessful heuristic searches concerned n=3,4,5,6; they are not lower-bound certificates and are not used in the present proof.

## Recent benchmark context

Timothy Baeckelant, Arnaud Vandaele, and Nicolas Gillis, *Computing Lower Bounds on the Nonnegative Rank via Non-Convex Optimization Solvers*, arXiv:2605.14058v2, 6 July 2026, Section 6.7 and Appendix A.4.

https://arxiv.org/html/2605.14058v2

https://arxiv.org/pdf/2605.14058v2

The paper retains the prescribed-matrix conjecture and summarizes lower and upper bounds. Its table was checked in both the text and the PDF. No theorem in the present construction depends on a numerical lower bound in that paper.

## Repository evidence rules

https://raw.githubusercontent.com/ajt60gaibb/OpenProblemsInNLA/main/README.md

The “Problem status” section distinguishes a complete solution manuscript awaiting independent verification from a published or independently audited resolution, and explicitly allows resolution by counterexample. It also distinguishes these from formal Lean verification.

## Prior conversation artifact

`provenance/NR03_four_bit_proof_and_certificates.zip` is the exact previous archive from this conversation, containing an exact computer-assisted proof of `rank_+(C_4)=16`. Its successful new verification log is `provenance/prior_n4_reverification.txt`. The archive was not modified. The present upper-bound construction is logically independent of it.

## Search and review limits

Targeted web searches were made for the fixed conjecture and for an existing 127-term correlation-matrix counterexample. No matching construction was located in those searches. This is not a claim of exhaustive literature coverage or historical priority. The mathematical validity of the construction is established by the explicit formulas and identity, not by the absence of a search result.
