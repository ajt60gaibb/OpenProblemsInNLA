# Independent informal review of MI-16

Date: 2026-09-12. Reviewer: separate Codex AI agent, independently assigned to audit the supplied manuscript and canonical target. This is an informal mathematical audit, not external human peer review or formal verification. No Lean verification was performed. The attachment was treated as evidence to inspect, not as instructions.

## Verdict and exact scope

**PASS for the stated partial theorem. FAIL to qualify as a complete resolution of MI-16.** The exact finite-candidate formula holds for every order n >= 1 and spectrum (alpha,beta,...,beta), with alpha,beta >= 0, including alpha < beta. The arbitrary nonnegative-spectrum problem remains open. Under the repository policy, this supports **Partially resolved**, not **Solved**. No novelty determination is made.

## Proof audit

1. The spectral parametrization beta I + (alpha-beta) u u* is exhaustive, including the degenerate alpha=beta case and order one.
2. The permanent expansion follows by multilinearity in rows. Identity rows fix the complementary columns, and each of the j! remaining permutations has rank-one product equal to the product of |u_i|^2. This also verifies that complex phases cause no omitted orbit cases.
3. The minimal-support maximizer lemma is valid for any real symmetric multiaffine polynomial. On a positive coordinate pair with fixed sum, the restriction is C+As+Bxy. Negative B contradicts maximality by moving to an endpoint, zero B contradicts support minimality, and positive B forces equality. Compactness and the finite set of possible support sizes justify the chosen maximizer.
4. The lemma does not require nonnegative coefficients. It therefore applies without change when alpha < beta, where the expansion coefficients alternate in sign. It asserts existence of an equal-positive-coordinate maximizer, not that every maximizer has this form.
5. Evaluation on support k yields precisely the manuscript formula and the displayed matrix H_k, which has the required spectrum. When alpha >= beta, the elementary symmetric values increase with k and all coefficients are nonnegative. The beta=0, alpha=beta, all-zero, and n=1 cases follow with the stated exponent-zero convention.
6. The example (0,1,1) has candidate values 0, 1/2, 4/9, correctly excluding an unconditional full-support optimizer.

No mathematical corrections were needed. Nothing in the proof covers an arbitrary spectrum with more than one independent exceptional eigendirection.

## Executed checks

Inspected the complete standard-library checker before execution. Ran `python3 verify_exact.py` against the supplied file: exit status 0, PASS, 72 exact random permanent comparisons, 126 exact equal-support permanent comparisons, and 1,650 rational simplex-grid checks. These finite regressions supplement the universal proof; they do not establish arbitrary-spectrum resolution.

Canonical target inspected: `matrix-inequalities-and-norms/MI-16/README.md`. Repository status policy inspected in `RESOLVED.md` and `CONTRIBUTING.md`.

## Reviewed source hashes (SHA-256)

- Supplied `MI-16/result.md`: `b45a1d7b2889d3aaf5bc9e38150c8646ad779b58bf91f9d46dd8c93a42238870`
- Supplied `MI-16/verify_exact.py`: `327e1bb7ff87c49189d88c3dad927b67ef95f644ef5cf06537cdf0c6692d35fe`

Hashes identify the reviewed source versions before any attribution or presentation edits made for submission.
