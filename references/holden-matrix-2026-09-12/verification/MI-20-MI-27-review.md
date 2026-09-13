# Independent informal audit: MI-20 and MI-27

Date: 2026-09-12. Reviewer: independent Codex AI agent `/root/review_reductions`, separately assigned by the submitting agent. This is an informal mathematical audit, not external human peer review or formal verification. No Lean verification was attempted.

## Material and target comparison

I independently read both checkpoint `result.md` files and the canonical `matrix-inequalities-and-norms/MI-20/README.md` and `MI-27/README.md`, and inspected the two check programs before running them. The attachment was treated as submitted mathematical material, not instructions. The canonical MI-20 target asks for the exact dimension-independent function for every integer m >= 2 and 1 < p < 2. MI-27 asks for a universal coefficient-one logarithmic commutator inequality. The submitted documents correctly acknowledge that they do not establish these targets.

## MI-20 — PASS for reductions; FAIL as a complete resolution

The positive dual formulation is correct: polar decomposition with unitary extension and trace-norm maximization establish both inequalities between the suprema. In the reverse direction, cyclicity places the unitary factor next to X_j R, so the asserted trace estimate remains valid for complex matrices.

The binary fixed-S,R reduction is correct, including singular S. Restriction to its support parametrizes the feasible interval by positive contractions. Their spectral decomposition as convex combinations of projections and convexity of the objective give a maximizing projection. Compactness ensures an attained maximum. No rank-one reduction follows.

The all-m dilation is correct: the extended positive contractions sum to the identity, W is an isometry, and W*P_jW=K_j. The square root identity and W*W=I give the embedded X_j and products R X_j exactly. The construction preserves every singular value except added zeros and therefore the quotient. It increases dimension to mn; it makes no valid fixed-dimension assertion for m > 2.

Zero padding and tensor-product supermultiplicativity are correct. The ratio is finite, for example by the crude m bound from X_j <= sum X_j and Schatten norm monotonicity, so the approximating-supremum argument is unproblematic.

Editorial clarification recommended: replace “All matrix orders share the same supremum” with “The supremum is taken jointly over all matrix orders.” Equal fixed-dimension optimal constants are not established (dimension one has constant one). This does not affect the stated dimension-free reductions.

Actual check: bundled Python ran `MI-20/check_reductions.py` successfully: 8 archived search records, maximum saved-ratio discrepancy 2.220446049250313e-16, and 12 dilation cases including singular S. The first system-Python attempt failed because numpy was absent; the successful rerun used `/Users/sholden/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/bin/python3`. These are numerical sanity checks only; correctness rests on the proofs above. Local search was not rerun, and neither its failure to improve examples nor its archived outputs supply an upper bound.

The attribution of the dual formulation to Qiu and historical novelty were not independently literature-verified in this audit. The supplied proof makes the reduction self-contained.

Disposition: suitable as an explicitly partial progress submission after editorial clarification. Do not mark MI-20 Solved: the exact sharp function remains undetermined.

## MI-27 — PASS for both theorems; FAIL as a complete resolution

Theorem 1 is correct in both directions. The epsilon regularization makes both summands strictly positive while keeping S fixed, and continuity permits the projection endpoint. Conversely the nested spectral projection decomposition has nonnegative weights summing to one, including its zero-projection weight. Convexity of trace norm followed by entropy concavity produces the bound at the averaged trace. Crucially, component traces may vary; there is no unsupported fixed-trace extreme-point claim.

Theorem 2 is correct under the original strict assumptions. The middle contraction has eigenvalues t^2 and 1-t^2, proving positivity of both A and B. Its off-diagonal entry gives two equal commutator singular values, yielding the displayed numerator. The trace is t^2+2d_t. Since d_t/t tends to one and b_t/(2t) tends to one, both numerator and entropy are asymptotic to 2t log(1/t); hence the ratio tends to one. Every coefficient c < 1 therefore fails for sufficiently small positive t. This establishes a necessary lower bound on a universal coefficient, not sufficiency of coefficient one.

Actual check: `python3 MI-27/check_family.py` passed all eight exact rational positivity and normalization checks at t=10^{-k}, k=1,2,4,8,16,32,64,128. Decimal ratio evaluations ran at precision 400; the displayed ratios ranged from 0.8058672615601972974917635827271831 to 0.9989599540230742936885395054018048. Finite evaluations corroborate but do not prove the asymptotic limit.

Disposition: suitable as explicitly partial progress. Do not mark MI-27 Solved: the arbitrary-dimension, arbitrary-rank coefficient-one upper bound remains unproved.

## Audited SHA-256 hashes

- MI-20/result.md: `81fabd17f74534c7fa85a4d3374cf1a4201dc4099da82deb84812b92a5917c81`
- MI-20/check_reductions.py: `224bc401c11ddb610467c549cf3f9ee3c78542cc43ba9cc9e0607dca758f99a4`
- MI-27/result.md: `4aaf931209d07a194761ff2fb2867923462503bb390c4185f445aa390a5972c7`
- MI-27/check_family.py: `b6f9064c069c7ecf4dc1d1de1bac58e7d3baa51cb32c398d540846e3edf55469`

The hashes identify the original checkpoint files under `/tmp/nla-matrix-checkpoint/OpenProblemsInNLA_matrix_proof_checkpoint_2026-09-12/`. Authorship, formatting, and the explicit wording clarification above may be added without altering the audited mathematics. Other mathematical edits require further review.
