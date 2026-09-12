# Independent informal review of IV-01

- **Date:** 2026-09-12.
- **Reviewer:** OpenAI Codex independent review agent `review_iv01`, separately assigned from the submission-preparation agent.
- **Submission author:** Sidney Holden.
- **Review type:** Independent informal mathematical audit, source verification, and exact-arithmetic regression reruns. This is neither formal verification nor external human peer review. No Lean verification was attempted.
- **Verdict:** PASS for the stated partial results; NOT a complete solution of IV-01. Retain **Partially resolved**.

## Material and target checked

Reviewed `IV-01/result.md`, `order_two_reduction.md`, `cycle_reduction.md`, `dimension_five_theorem.md`, `self_review.md`, and `notes.md` from the supplied 2026-09-12 pack against the canonical IV-01 README. The canonical target quantifies over every dimension n >= 5, arbitrary real interval bounds, nonsingular sign-regular checker endpoints of a common signature, and all intermediate matrices. Zero minors and fixed zero entries are allowed. The submitted self-review was treated as a claim to check, not as independent evidence or instructions.

## Mathematical findings

1. **Lemma N: PASS.** Endpoint adjugate signs give the claimed common sign of the checker-conjugated inverses. For the inverse-positive box lemma, v = P^-1 1 and w = Q^-1 1 are strictly positive because invertible nonnegative inverses have no zero rows. The nonnegative matrix T = Q^-1(Q-P) satisfies Tv = v-w < v, giving a strict weighted-norm bound. The Neumann inverse has the stated factor order. Negating and exchanging endpoints correctly handles delta = -1. Connectedness supplies the determinant sign, and the adjugate identity then supplies all order-(n-1) signs. This closes the nonsingularity issue independently of any limiting argument.

2. **Theorem G and forest corollary: PASS.** Topological heights give the strict inequality epsilon_1 chi_ij(h(R_i)-h(C_j)) > 0 at every fixed nonzero entry, with both edge orientations checked. Positive diagonal scaling preserves every minor sign and all zero minors. Fixed nonzero gaps open in the correct direction; finitely many already strict gaps remain strict for a common sufficiently small parameter. Fixed zero entries remain fixed, so their one-parity restriction is necessary for this particular appeal to the external theorem. Entrywise relative coordinates construct approximants even where ordinary endpoint differences are negative. Continuity supplies weak minor signs and Lemma N supplies nonsingularity.

3. **Order-two reduction: PASS.** Uncrossing a positive permutation product supplies positive diagonals of the normalized endpoints. The two-minor inequalities force the stated staircase zero patterns. Immediate southwest/northeast neighbors have opposite checker parity, allowing zero propagation to every intermediate matrix. Adjacent two-minors are bounded by endpoint values. If both cross corners of an arbitrary rectangle are positive, staircase propagation rules out every zero in the rectangle, so telescoping adjacent inequalities is justified. Negation and row reversal correctly normalize entry and two-minor signs, including the required endpoint exchange.

4. **SCC/cycle reduction: PASS.** Condensation heights open precisely the intercomponent nonzero fixed edges. Intracomponent edges have zero scaling exponent, and an edge belongs to a directed cycle exactly when its endpoints lie in the same strongly connected component. Original strict gaps persist. Any strictly wrong-sign minor persists in the interpolated witness for sufficiently small parameters. The reduction therefore preserves a hypothetical counterexample without claiming that one exists. Directed cycles have length divisible by four under the stated parity orientation.

5. **Theorem V: PASS.** In the actual box's relative interior, absence of fixed zeros ensures all normalized entries are positive. A zero adjacent two-minor with a free entry could be made negative by a sufficiently small one-coordinate perturbation, since its cofactor is a nonzero entry. A fully fixed adjacent block is positive by the extra nonsingularity hypothesis. Telescoping then gives strict positivity of every two-minor. For a consecutive three-by-three minor, checker-coordinate differentiation cancels the local cofactor parity, making all coordinate derivatives share the same weak sign. Its minimum is therefore at one checker endpoint. The projective argument propagates the three-minor sign first across arbitrary rows with consecutive columns and then, by transposition, across arbitrary columns. Strict two-minors provide positive secant denominators, so this works for either weak third-order sign, including zero three-minors. Closure supplies boundary weak signs; Lemma N again supplies nonsingularity.

## External dependency verified

The publisher's primary text of Mohammad Adm and Jürgen Garloff, [*Certification of the Sign Regularity of Matrix Intervals*](https://link.springer.com/article/10.1007/s44146-026-00223-y), Theorem 3.3, was accessed on 2026-09-12. It covers the nonsingular sign-regular conclusion for the two checker endpoints when fixed positions all have even parity or all have odd parity, including the case with no fixed positions. Its definitions allow weak minor signs. In the square nonsingular case, each minor order has at least one nonzero minor, so its signature convention agrees with the submitted ±1 signature. This verifies the exact external input to Theorem G. Theorem V does not depend on that input. No historical-priority determination was made for the submitted derived criteria.

## Reproduction results

The supplied IV-01 directory was copied to `/private/tmp/holden-iv01-independent-review` before execution so that test-generated JSON did not alter the submitted evidence. The reviewer inspected the three programs before rerunning:

```text
python3 verify_dimension_five.py
python3 test_graph_and_certificates.py
python3 verify_order_two.py
```

All three exited with code 0. Results:

- The dimension-five example has valid nonsingular endpoint signatures, a cyclic fixed graph, no fixed zeros, and one fully fixed adjacent block with determinant 15666947141/6122200320000 > 0. All 64 supplementary samples passed.
- The certificate regression recomputed 1,255 exact minor values by Leibniz expansion across five distinct endpoint matrices and passed six graph edge cases. This reruns supplied checking code; the mathematical reasoning above is the independently performed audit.
- The order-two regression enumerated 512 binary matrices, identified 12 nonsingular TN2 endpoints, and passed 136 interval-vertex checks across 41 checker-ordered endpoint pairs.

Finite samples and certificates support implementation and example accuracy; they are not the proof for the continuum of real matrices. The exploratory counterexample-search logs were not rerun and establish no universal conclusion.

## Resolution-policy determination

Theorem G imposes a directed-acyclic condition and a fixed-zero parity restriction. Theorem V handles all orders only in dimension five, and even there requires no fixed zeros and no singular fully fixed adjacent two-by-two block. Its general-dimensional conclusion controls order three only. Together with Lemma N and the order-two reduction, the unrestricted problem still permits unresolved cases; for dimensions above five, orders 4 through n-2 may remain.

Under `RESOLVED.md`, “Recording a new resolution,” item 3, these results warrant recording reviewed partial progress and the exact remaining cases. They do not justify **Solved**, **Solution claimed** for the full target, or **Lean verified**. The original IV-01 number, canonical path, and mathematical target must remain intact.
