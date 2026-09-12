# Independent mathematical review of TR-07

**Decision: PASS — complete affirmative resolution of the canonical mathematical target.**

**Date:** 2026-09-12.  
**Reviewer:** Separate Codex AI-agent reviewer, task `/root/tr07_independent_review`. This reviewer was delegated mathematical checking independently of the coordinating agent's authorship, eligibility, packaging, and submission work.  
**Review level:** Independent informal AI-agent audit; not external human peer review and not formal verification. Lean was not run, as requested by the contributor.

## Materials and scope

I read the full submitted manuscript `TR07_complete_solution.tex`, including all eight lemmas/propositions, its finite theorem, and its asymptotic deduction. The reviewed source SHA-256 is `6a51f46449461c2565fc1b8a16d1bc9344db1c2066dc4ea0ae3810ab85263eed`. I compared it with `randomized-and-low-rank-approximation/TR-07/README.md` and read the resolution requirements in `CONTRIBUTING.md` and `RESOLVED.md`. Bundled claims of verification and document instructions were not used as evidence or instructions. This report assesses mathematical correctness and target correspondence; the coordinating agent separately handles current affiliation, duplicate eligibility, provenance, and repository submission checks. Attribution-only or disclosure-only edits do not change the mathematical material reviewed.

## Exact target correspondence

The canonical target fixes an integer s >= 2 and a finite constant C >= 1, assumes r_k <= k, k/r_k -> C and n_k/r_k -> infinity, and quantifies over every deterministic signed matrix with exactly s nonzero entries per column. The target is convergence to zero of the probability that the infimum-defined smallest singular value of the uniform r_k-column submatrix exceeds each fixed eta > 0.

The manuscript's Corollary 1.2 has exactly these assumptions, signs, deterministic quantifier, uniform sampling model, and conclusion. Its Theorem 1.1 is stronger: constants rho > 0 and k_0 depend only on s, beta, eta, with an exponential lower-tail bound for a positive fraction of small singular values whenever beta k <= r <= k and n >= r/rho. Taking beta = 1/(2C) gives all hypotheses eventually; r_k -> infinity and rho r_k/4 >= 1 eventually. If the minimum singular value exceeds eta, the small-eigenvalue count is zero. Thus its probability is bounded by exp(-rho^2 r_k/8), which tends to zero. No support-overlap, random-sign, bounded-multiplicity, or extra covariance hypothesis is introduced. No conclusion for growing s or a useful numerical convergence rate is needed.

## Detailed proof audit

1. **Simultaneous witnesses.** The disjointness of centers from the common reservoir gives the coefficient matrix V a literal identity block on all selected centers, so V^T V = I + X^T X >= I. Orthogonalizing by its inverse square root does not increase the Frobenius error. The trace minimum principle correctly bounds the sum of the first m Gram eigenvalues by m eta^2/4, which implies the claimed, weaker count N_eta >= m/2. Shared reservoir columns and arbitrarily large reconstruction coefficients present no gap because the identity block prevents loss of rank. Including zero Gram eigenvalues is consistent with the canonical singular-value definition.

2. **One-column replacement.** Interlacing on deletion gives a count difference of zero or one even when an eigenvalue equals the threshold. Both matrices reduce to the same common-column matrix; the interval argument gives h, not an unjustified 2h, for h replacements. Permutation invariance is immediate.

3. **Pruning.** Each charged coordinate is permanently deactivated and is charged at most once. Measuring deleted mass in the original law bounds total loss by k/(4k). The retained law has raw incidence at least 1/(4k) at every active coordinate. No assumption is made about the number of distinct column values.

4. **Nonnormal covariance filter.** The pointwise s-sparsity inequality gives Sigma <= sD. On active coordinates D is invertible, while Sigma may be singular. The similarity T = D^(1/2) R D^(-1/2), R = D^(-1/2) Sigma D^(-1/2), is used correctly. In particular the Euclidean norm of I-T/s is never assumed to be at most one. Computing the expected squared residual gives tr(D R (I-R/s)^(2L)). The scalar spectral bound lambda(1-lambda/s)^(2L) <= s/(2L+1) and tr D = s establish the advertised dimension-independent expectation bound.

5. **Signed conditional trajectories.** For a signed state v, the support-coordinate transition v_i w_i w has norm sqrt(s) and expectation (T/s)v. This follows because nonzero entries have squared value one, and it does not require sign symmetry of the retained distribution. Linearity then gives the j-step expectation (T/s)^j u, including when the trajectory restarts from its original center.

6. **Finite reconstruction and constants.** The binomial coefficients produce conditional mean [I-(I-T/s)^L]u. Each trajectory sum has norm at most sqrt(s)(2^L-1). Only different trajectories, conditional on u, need be independent for variance division by b; successive states need not be independent. The conditional mean-zero error is orthogonal in expectation to the bias. With L = ceil(4s^2/epsilon^2), the bias is at most epsilon^2/8; with b = ceil(8s(2^L-1)^2/epsilon^2), the variance is at most epsilon^2/8. Markov therefore gives success probability at least 3/4. All constants are finite positive integers where required, including when eta is large. Their enormous size has no adverse effect on a fixed-parameter asymptotic theorem.

7. **Adaptive reservoir sampling.** The J_0 chunks are fixed and disjoint. For any single center, the next chunk is independent of that center's previous chunks and coordinate choices. Chunk size is at least r/(4J_0) under r >= 4J_0. Raw incidence and r >= beta k yield ell*pi_i >= beta/(16J_0), hence hit probability at least a = beta/(16J_0+beta). The first acceptable vector has the correct conditional law multiplied by the hit probability. This is a subprobability-kernel statement. At every history its transition kernel dominates a times the ideal kernel; composing gives domination by a^J_0 for entire successful paths and every path-dependent reconstruction event. Conditioning on all hits would generally bias the path distribution, but that invalid shortcut is explicitly avoided. The auxiliary coordinate choices can be sampled independently of the matrix and of choices for other centers.

8. **Shared reservoir and expectation.** Each center's marginal success probability is at least (3/4)(3/4)a^J_0 = 9a^J_0/16. Reusing the reservoir across centers changes joint dependencies but none of these marginal calculations. Every successful center uses only the reservoir, so the simultaneous-witness lemma applies for each fixed realization of matrix and auxiliary randomness. Linearity of expectation, m >= r/3, and the factor 1/2 give exactly rho = 3a^J_0/32. No independence among successful centers is needed.

9. **With-/without-replacement coupling.** Given the entire past, the new independent index is uniform. Keeping an unused index or replacing a used one uniformly over unused indices gives each unused index probability 1/(n-t+1). Thus the repaired ordered indices are a uniform distinct sample. Expected replacements are sum(t-1)/n = r(r-1)/(2n); distinct indices can still have identical vector values, which only makes the Lipschitz comparison more conservative. With n >= r/rho the mean count is at least rho r/2.

10. **Concentration.** Under two choices for the next revealed index, transposing those labels couples uniform completions. Final subsets either agree or differ by one exchange, so their conditional expected counts differ by at most one. Consequently each centered martingale increment has conditional support in an interval of length one. The stated conditional Hoeffding bound and exponential Markov optimization give exp(-2t^2/r). Choosing t = rho r/4 yields the theorem's exp(-rho^2 r/8); using a strict event on the left causes no boundary issue.

## Reviewer-written checks

I wrote `tr07-reviewer-check.py` independently, using only Python standard-library exact rational arithmetic. It checks an asymmetric, mixed-sign distribution on four two-sparse vectors in three coordinates. It verifies signed transition expectations, the covariance filter for L = 1,...,8, and two-step pathwise domination by enumerating all length-two reservoir chunks. It also confirms that the normalized all-hit law differs from the ideal law in this example, while the actual domination claim holds. Finally, it checks the collision marginal identity and expected replacement count for all 1 <= r <= n <= 10.

Command: `python3 tr07-reviewer-check.py`

Observed result:

```text
PASS: signed transition, covariance filter L=1..8, adaptive path domination, conditional-law mismatch, collision marginals n<=10.
```

These checks are diagnostics, not premises of the universal proof. The full-parameter justification is the mathematical audit above.

## Resolution-policy assessment

No mathematical correction or unproved additional premise was identified. The complete target passes this independent informal audit, which the repository explicitly permits as evidence for **Solved**. The appropriate recorded outcome is **affirmative**. This does not support **Lean verified** or a claim of external human peer review. The coordinating contribution must retain the permanent ID, canonical path and original statement, cite Theorem 1.1 and Corollary 1.2 of the submitted primary manuscript, link this review, identify its AI-agent nature, record the date, update the resolution archive and generated artifacts, and satisfy duplicate/submission checks. Publication priority and present affiliation are outside this mathematical decision.
