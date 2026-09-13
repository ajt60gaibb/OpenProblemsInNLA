# Independent review of the TR-08 submission

**Verdict: PASS — full original mathematical target.**

**Reviewer:** Separate Codex AI agent, independently assigned to review the proof, rather than to prepare its submission. **Review date:** 12 September 2026. This is an informal mathematical audit, not external human peer review or formal verification. No Lean verification was performed. The supplied `PROOF_AUDIT` was not used as evidence for correctness.

## Material and target

Reviewed the submitted `manuscript/solution.tex`, *A square-root-logarithmic threshold for sparse rectangular injectivity*, against the canonical `randomized-and-low-rank-approximation/TR-08/README.md`, including its 12 September precision clarification. The reviewed original TeX SHA-256 is `8738edcfa682175f228b883f0e5d1f34ae61fe75960c6e068402d87cd817b0c2`. Author attribution and submission metadata may subsequently be corrected without changing the audited mathematics.

Theorem 1.1 gives the exact sequence criterion

\[
\exists a>0:\ \Pr\{\sigma_{\min}(A_k)\ge a\}\to1
\quad\Longleftrightarrow\quad
\liminf_{k\to\infty}s_k^2/\log k>0.
\]

The constant may depend on the fixed positive lower bound for the normalized sparsity, and remains independent of matrix size and realization. This matches the repository's existential quantifier. It settles constants and iterated-logarithmic behavior insofar as they decide that property. No optimization of the lower singular-value constant is required.

## Mathematical checks

1. **Exact model reduction (Section 1).** Conditional on the independently chosen column index set, selected columns have the same independent uniform fixed-cardinality supports and signs. Averaging preserves that product law. The large ambient column count causes no residual conditioning or selection bias.

2. **Support probabilities (Lemmas 2.1–2.2).** The hypergeometric inclusion probability is bounded by the Bernoulli product probability factor by factor. Expanding the generating function has nonnegative coefficients for its prescribed nonnegative parameter, so the incidence Chernoff bound is valid, including after exposure of whole columns. The triple-overlap union bound is valid and tends to zero throughout the stipulated polylogarithmic regime.

3. **Nonbacktracking extension (Lemma 3.1).** This potentially delicate step passes. On the common complete bipartite oriented-edge index set, the squared Frobenius trace expands into path-pair monomials with nonnegative combinatorial coefficients. Conditional on supports, independent signs annihilate monomials having an edge of odd multiplicity. Every surviving term is nonnegative. Support-only deletion multiplies a surviving term by a zero-one factor, hence can only reduce its expectation. Independence across columns and the within-column inclusion bound then dominate that term by the matching independent Bernoulli-support term. The argument does not need entry independence for the original matrix and does not claim pointwise signed spectral-radius monotonicity. Padding changes only zero eigenvalues.

   I checked the sole external input directly in the [Dumitriu–Zhu primary paper](https://arxiv.org/html/2209.12271v4), Assumption 3 and Lemma 4.3, equations (4.1)–(4.2), with the path expansion in Section 5. Its hypotheses apply with variance sums 1 and 1/100, maximum variance 1/k, and the manuscript's entry bound. Taking q as the minimum of sqrt(d) and k^(1/20) satisfies the stated range eventually, even for dense matrices; the bound need not be attained. The chosen odd moment order satisfies both restrictions. The Markov exponent is approximately -7.063 before its logarithmic prefactor, so the claimed vanishing failure probability follows.

4. **Deterministic bulk argument (Lemma 4.1).** The opposite-orientation equations give the displayed Ihara–Bass kernel correctly. At imaginary parameter the two off-diagonal imaginary factors produce the positive Gram term in the Schur complement. Nonsingularity and continuation from infinity force this real symmetric complement to stay positive definite. The direction of the inverse row-block bound is correct. The resulting lower bound is at least 21/256, exceeding the required 1/16.

5. **Exceptional columns (Lemmas 5.1–5.2 and Section 5.3).** R is fixed once the positive sparsity lower bound is fixed. Pairwise overlap control permits disjoint private witness rows after exposing the center and R leaves. Conditional incidence estimates apply only to the remaining columns. The union over witness subsets and then centers/leaves has the stated vanishing bound. This justifies a bounded number L of rows lost to other exceptional supports. The high-occupancy cap has adequate constants and correct rounding. Deleting entire exceptional neighborhoods makes the upper-right block exactly zero; merely deleting high rows would not suffice. Good columns retain enough rows for the bulk lemma, exceptional columns have disjoint recovery supports, and the off-diagonal block has norm at most sqrt(DL). The triangular estimate proves the stated positive lower bound. Empty good or exceptional column sets cause no difficulty.

6. **Necessity (Section 6).** The cancellation vector has precisely the stated squared norm and output norm for every sign realization. Reservoir row upper-tail indicators have nonpositive covariance by the displayed conditional stochastic ordering, so the reservoir size estimate is justified without an independence approximation. Excluding rows on four-cycles makes each individual branch clean. Pairwise distance greater than four separates distinct branches and prevents auxiliary columns from meeting a second root row. Degree control makes the forbidden neighborhood negligible relative to the candidate set. Conditional independence of test columns then produces a witness with probability tending to one when d^2=o(log k). The argument also covers bounded sparsity and d=1.

7. **Arbitrary sequences (Section 7).** A zero lower limit yields a subsequence in the necessity regime, which rules out convergence to one for any fixed positive bound along the original sequence. This closes the exact equivalence, rather than just determining the logarithmic exponent.

I also independently checked the numerical eta and Markov exponent and used exact rational arithmetic for the bulk constant and 10,000 instances of the cancellation-quotient identity. These finite checks support algebra inspection; they do not establish the asymptotic proof.

## Findings and resolution-policy assessment

No blocking mathematical gap or counterexample was found. No mathematical correction is required for the verdict. Theorem 1.1, proved in Sections 2–7, resolves the retained model and all its sequence quantifiers.

The repository's `CONTRIBUTING.md` expressly permits `Solved` for a complete argument passing a separate informal AI-agent audit, provided the actual review level and report are recorded. This argument satisfies that mathematical evidence condition. Submission preparation must still preserve the original ID/path/statement, supply the manuscript and attribution, add a dated classification notice and exact theorem locator, update the resolution archive and generated artifacts, run the required ID/catalog checks, and open the requested pull request against upstream `main`. Duplicate screening, author affiliation verification, artifact production, and publication operations are outside this mathematical review. This report does not certify historical novelty or priority.
