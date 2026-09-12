# Global Frobenius minimality and delayed rank submultiplicativity

**Author:** Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics, University of Cambridge, Cambridge, United Kingdom. [Official affiliation](https://www.damtp.cam.ac.uk/user/mjc249/home.html), checked 11 September 2026. Contact: m.colbrook@damtp.cam.ac.uk.

**Recorded:** 11 September 2026. This submission resolves two retained catalog targets: TR-17 affirmatively and TR-27 negatively. Their permanent IDs, paths and original mathematical statements are unchanged; their former difficulty and importance ratings remain historical.

| Target | Complete manuscript | Independent mathematical review | Exact resolution |
| --- | --- | --- | --- |
| [TR-17](../../tensor-computations/TR-17/README.md) | [PDF](manuscripts/tr17_solution.pdf), [LaTeX](manuscripts/tr17_solution.tex) | [PASS](verification/reviews/TR-17-review.md) | Theorem 1 proves global Frobenius minimality of the Euclidean distance degree for every allowed Segre–Veronese format and every positive definite real symmetric metric, using complex-bilinear complexification and algebraic multiplicities. |
| [TR-27](../../tensor-computations/TR-27/README.md) | [PDF](manuscripts/tr27_solution.pdf), [LaTeX](manuscripts/tr27_solution.tex) | [PASS](verification/reviews/TR-27-review.md) | Theorem 1 and Section 4 give a smooth nondegenerate complex curve in projective dimension 11 with border rank 2, rank 3 and tensor-square rank 9, disproving the universal strict-square implication. |

TR-17 supplies the global comparison beyond the local result in [Kozhasov–Muniz–Qi–Sodomaco, Conjecture 3.9 and Theorem 3.12](https://arxiv.org/html/2309.15105v3). The proof establishes positivity of the required signed section Euler characteristics, including singular and nonreduced quadric sections, and expresses the distance degree as a sum with nonnegative weights. Its use of the Chern–Schwartz–MacPherson formula follows [Aluffi–Harris, Theorem 8.1](https://arxiv.org/pdf/1708.00024). There is no generic-metric exception.

TR-27 addresses the universal projective-variety formulation of [Ballico–Bernardi–Gesmundo–Oneto–Ventura, Conjecture 1.1](https://arxiv.org/abs/1909.03811). More generally, for every prescribed finite number of powers the construction produces a variety whose rank remains multiplicative through those powers despite a border-rank gap. The variety depends on the prescribed delay. The result does not assert multiplicativity at every power and does not refute restrictions to Segre or Veronese varieties or the known eventual-power saving.

Two independent mathematical review agents read the complete sources against the exact canonical targets and checked the primary references. A separate agent read and reran all three supplied verification programs; its [computational review](verification/reviews/computational-review.md) reports PASS for their finite exact computations. [Fresh execution evidence](verification/fresh-code/) supplements the analytic proofs and does not replace them. The reviews bind the complete original sources by SHA256 after UTF-8 decoding and CRLF-to-LF conversion, with no trimming:

| Original source | Complete normalized SHA256 |
| --- | --- |
| TR-17/solution.tex | `dd5e71eb942e6b928264426e6598c4cd47b14a04b08d3c3b82f4d38b5a065c3b` |
| TR-27/solution.tex | `db7d556699d5021a9da6674ef491561c8af631d8537d99e21f427a82c7d1dca4` |

All eleven files from `tensor_computations_submission20.zip` are preserved byte-for-byte under [submitted/](submitted/), including the original manuscripts, supplied PDFs and verification material. The [source manifest](verification/source-manifest.json) records the archive and each file. The attributed editions above retain the mathematical bodies from abstract through bibliography; [document checks](verification/document-checks.json) record source comparison, compilation and visual inspection. Provisional review or status wording in the original submission is historical and is superseded by the dated reports here.

The [live public eligibility audit](verification/eligibility-live.json) examined 54 canonical pages across 27 branches in five repositories, plus 21 pull requests and 89 issues. All checked canonical copies still had Partially resolved status, and no existing full resolution or pending solution review was found for these two targets in the inspected public material. This records the inspected scope and date; it does not establish priority or exclude private, unpublished or unlinked work.

AI assistance was used in preparing and checking this submission. The independent reviews are agent reviews, not external human peer review or formal proof certificates. No novelty or priority claim is made. The Solved recommendations rest on the complete mathematical arguments and their explicit scope, not on the supplied verification labels or finite experiments.
