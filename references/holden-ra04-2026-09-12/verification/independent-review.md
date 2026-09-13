# Independent mathematical review of RA-04 partial results

Date: 2026-09-12. Reviewer: a separate Codex AI agent, independently assigned mathematical and target-scope review. This is informal automated review, not external human peer review or formal verification. No Lean verification was performed.

Reviewed source: `RA04_partial_results/src/report.tex` from the supplied archive, SHA-256 `2095466aa22b0331dc8a5e9cb59aa0da5d2947d0168be10e8810e6c2ba8c3438`. The review was made directly from the proofs and the canonical RA-04 README; the supplied AUDIT conclusions were not used. Changes restricted to author metadata, source attribution or typesetting do not alter these mathematical findings.

**Verdict: PASS for the stated partial results; FAIL for promotion to Solved.** No mathematical correction to the audited arguments is required. The package itself correctly disclaims a full resolution.

## Target correspondence and imported result

The report's Section 1 matches the canonical original target: real matrices, standard Gaussian starting block, `m=b ceil(k/b)` no larger than rank, positive relative b-step head gap, exact arithmetic, the same projected rank-k SVD, both approximation norms, and ordered right-component energies. There is no perturbation of the input or replacement of the algorithm.

I independently opened the primary [Chen–Epperly–Meyer–Musco–Rao arXiv v2](https://arxiv.org/html/2508.06486v2). Definition 3.1 is the good-start condition used in the report; Imported Theorem 3.2 supplies convergence at order `log(nL/epsilon)/sqrt(epsilon)`, and Problem 1.1 explicitly uses right singular vectors and both relevant norm choices. Observation 3.3 supplies the simulated-start identity. Thus the report's Theorem 2.3 has the required scope. This review checks this imported result's statement and applicability; it does not independently reprove its cited Appendix F provenance.

## Claim-by-claim findings

| Locator in report | Verdict | Independent reasoning and scope |
| --- | --- | --- |
| Section 2, Lemma 2.2 and simulated-start identity | PASS | Normalizing the first j graph columns gives overlap inverse squared at most `1+||F||²`; the head coordinates between j and m are zero. Multiplying Krylov powers gives depth `s+q0-1`, so a nondivisible target k is covered. |
| Section 3, Lemmas 3.1–3.3 | PASS | The inverse Gaussian estimate follows from row distances and a union bound. A relative window cannot contain b+1 nodes because its endpoint ratio exceeds `1-Delta`. Residue-class Vandermonde blocks supply a nonzero determinant witness even with admissible repeated nodes. |
| Section 4, Theorem 4.1 | PASS | Each scalar filter kills the far head rows, while a Gaussian orthogonal direction kills the remaining b-1 rows. Conditional scalar Gaussian small-ball bounds suffice; independence among columns is not required. Tail nodes lie below every head node, giving `(3/Delta)^(m-b)`. The prefactor and depth are correct. This yields the weaker general leading term `m-b+1`. |
| Section 5, Lemma 5.1 | PASS | Sorted subsets inherit at least the original b-step gap. A leave-one-out null polynomial cannot vanish as a vector at the deleted node, since division by that factor would contradict invertibility on the far subset. Interpolating the quotient gives the displayed recursion. Its normalized evaluation depends only on other rows. |
| Section 5, Theorem 5.2 | PASS | Conditioning on all rows except i leaves its scalar projection standard normal. The full norm-cutoff event can be enlarged to the other-row event and then the far-subset event, with nonnegative integrands. This controls the correlated subproblem norm by its truncated half moment, without claiming inverse/entry independence. The recurrence, Gaussian exponential tail, and Markov threshold yield the stated B_eta. The logarithmic simplification uses `(t-1)/m <= 1` and `log(1+sqrt(x)/m) <= sqrt(x)/m`; there is no missing factor t on the final failure logarithm. |
| Section 5, Theorem 5.3 and Corollary 5.4 | PASS | Shifts by interior tail nodes preserve positivity and improve the relative gap. A union bound over t Chebyshev nodes and the polynomial interpolation inequality give the uniform tail bound. The general iteration bound retains `t log(2m/Delta)`; when `Delta <= 1/m`, this is bounded by `2t log(2/Delta)`. |
| Section 6, Theorem 6.1 and Corollary 6.2 | PASS | Scalar Lagrange interpolation is exact for the repeated b-sized head levels, and all tail factors are bounded by `Delta^-1`. Inverse-block and tail-norm estimates give the displayed prefactor. Tail repetitions at the bottom head level are allowed. For b=1 all admissible heads have singleton clusters; for b=k a direct Gaussian graph removes the equal-head-value assumption. |
| Section 7, Theorem 7.1 | PASS | The linear leave-one-out polynomial has slope `-H_S^-1 D H_S z`. This directly gives the uniform extrapolation bound. Three failure events each cost at most delta/3. The stated simplification to `4000 n^12 delta^-6 Delta^-2` is conservative and valid. The desired order follows for arbitrary admissible t=2 spectra. |
| Section 8, Proposition 8.1 | PASS | When rank equals m, the powers from MG through M^t G have zero tail and invertible head `Lambda K_H`. They span range(A), so the SVD truncation is exactly optimal and its ordered right-vector energies are exact. This includes the zero residual case when rank=k. |
| Section 9, Proposition 9.1 | PASS, auxiliary claim only | The normalized test vector gives expected squared singular-value upper bound `5 eta²/8`; Markov proves convergence to zero in probability at a fixed gap. This concerns a particular raw monomial matrix and does not refute the span-based RA-04 algorithm. |
| Section 10, Proposition 10.1 and Lemma 10.2 | PASS, conditional only | The proposed interpolation estimate would bound the canonical graph. Shifted zero evaluations and discrete cosine coefficients extend it uniformly with only polynomial factors in m. The estimate is explicitly unproved. The displayed noncommuting 2-by-2 product counterexample is algebraically correct. |

## Checks and limitations

I read `tests/exact_checks.py` before attempting execution. Its seven finite rational/symbolic groups are relevant checks of the displayed identities, but are not universal probability proofs. The first execution with the system Python failed at import because SymPy is not installed in that interpreter; it produced no test verdict. Any subsequent execution by the coordinating agent should be recorded separately. I did not rerun the large floating-point experiment, and do not use its reported success as proof. The review verdict rests on the analytic arguments above and the verified imported theorem statement.

Novelty and historical priority of all partial bounds have not been established by this review. Prior authors must retain attribution for imported results. Peripheral bibliographic comparisons in Section 10 are not premises of the passed mathematical results.

## Resolution-policy decision

The exact RA-04 universal target remains unresolved for unrestricted growing b and t with general, nonzero-width leading clusters and `Delta > 1/m`, outside the proved subclasses. Neither weaker all-input bound removes the unwanted general dependence, and the raw-conditioning counterexample does not disprove the target. The report leaves its sufficient interpolation estimate unproved.

The repository's `RESOLVED.md`, “Recording a new resolution,” item 3 requires **Partially resolved** for a partial result and explicit surviving cases. Therefore the proper result of this audit is **Partially resolved**, retaining the original ID, path and mathematical target and keeping RA-04 in the open count. A Solved label, Solution claimed label, or reduction of the open-target count would not satisfy that policy on this evidence.
