# MI27 trace-log bridge — independent pre-body referee B

**Verdict: APPROVE all eight exact helper headers for implementation.** This bounded mathematical/statement review covers `development/MI27-C11-referee-a-v1/TRACE-LOG-STATEMENTS.md`, SHA256 `7df20a9c5c1da52cb2c71afd4ea870123e6ecb28316d0d54871e8ae053418151`. No blocking sign, domain, invertibility, normalization or eigenvalue issue was found.

Reviewer: `/root/nr04_mf14_final_referee_b`, independent nonauthor AI agent, 19 September 2026. I reviewed the proposed statements, the literal existing shift-kernel definition, and relevant pinned API signatures. I wrote no proof body, ran no Lean/Lake/Comparator, and made no publication or count change. This approval concerns statements before implementation, not the full C11 or MI27 proof.

| Exact helper | Assessment |
|---|---|
| `c11_identityShift_posDef` | Adding rI with r≥0 preserves positive definiteness; r=0 is included. No dimension-nonzero premise is needed. |
| `c11_inv_eq_cfc` | Correct for Hermitian units: the pointwise reciprocal on the real spectrum equals the matrix inverse. The explicit unit premise is essential and sufficient. |
| `c11_trR_log_eq_log_det` | Correct for P>0: real trace of log P is the sum of logarithms of its positive eigenvalues, and the real part of det P is their positive product. The scalar expression uses the real logarithm of this positive real determinant. |
| `c11_trR_log_normalized_congruence` | Correct for invertible S with SᴴPS=I. Determinants give det(SᴴQS)=det Q/det P, and both congruent Q and P are positive definite. Taking the real determinant logarithm yields the stated difference. |
| `c11_trR_congruence_mul_inv` | Correct for arbitrary A and unit B,S. Expanding the inverse gives S⁻¹B⁻¹(Sᴴ)⁻¹; cancellation and cyclic trace reduce the result to trR(AB⁻¹). No Hermitian or positivity premise for A or B is missing. |
| `c11_shiftKernel_eq_trace_log_resolvent` | Correct with the displayed order and minus sign: log(Y+rI) minus log(X+rI) minus the trace of (Y−X)(Y+rI)⁻¹. This agrees with the literal negative double-spectral-sum definition. |
| `c11_trace_log_resolvent_spectral` | Correct. I+C>0 implies every eigenvalue cᵢ of Hermitian C satisfies cᵢ>−1. The log/resolvent expression is diagonal in C's eigenbasis and equals the displayed finite scalar sum. |
| `c11_normalized_pencil_trace_kernel` | Correct. With P=X+rI, Q=Y+rI and C=Sᴴ(Y−X)S, the normalization gives I+C=SᴴQS. Positivity and the preceding trace identities yield exactly the stated shift kernel. |

The inverse-CFC premise must remain. For example, a singular diagonal matrix with entries 0 and 1 has zero total nonsingular matrix inverse, while pointwise reciprocal CFC keeps its nonzero spectral component. Requiring `IsUnit M` avoids that mismatch, and Hermiticity provides the real-spectrum calculus. The pinned `cfc_ringInverse_id` explicitly takes a unit premise; `Matrix.nonsing_inv_eq_ringInverse` supplies the relevant matrix inverse identification.

The normalized trace-log result does not assert a matrix logarithm congruence law. S need not be Hermitian, positive or unitary; its invertibility and the stated normalization suffice. The determinant factors cancel before the real logarithm is used. Positive definiteness ensures every determinant/log denominator used here is nonzero and positive, so no complex logarithm branch issue is hidden in the formula.

For the shift-kernel sign, expanding its existing definition gives a negative sum of `log(xᵢ+r) − log(yⱼ+r) + (yⱼ−xᵢ)/(yⱼ+r)`, weighted by the actual overlap matrix. The two overlap marginals turn its logarithm terms into the displayed trace difference. The two-basis product formula identifies the rational sum with trR((Y−X)(Y+rI)⁻¹). This uses separate spectral bases, not commutativity or simultaneous diagonalization. Positivity and r≥0 keep every yⱼ+r strictly positive, including at r=0.

The spectral resolvent lemma divides only by 1+cᵢ. Its positivity premise guarantees that denominator is positive, while cᵢ itself may be negative, zero, repeated, or positive. Thus it covers exactly the c>−1 range needed by the scalar-pencil integral, with no hidden c≠0 condition. For C=0 the sum and trace difference vanish. The X=Y case similarly yields C=0 and zero shift kernel for every allowed normalizer. The boundary cᵢ=−1 is correctly excluded by positive definiteness of I+C.

Pinned API inspection at Mathlib `0df444a360eaa60ab8c11dca51a86af692955474` confirmed the determinant spectral formula, positive eigenvalues/determinant, CFC inverse identity for units, nonsingular inverse/ring inverse relation, reversed product inverse, conjugate-transpose inverse, and positive-definite congruence under injective multiplication. These support the proposed route; they are not a Lean elaboration or proof check.

No new definition or conclusion-shaped hypothesis is introduced. The last helper's normalization premise is concrete algebraic input, but the full C11 proof must still construct such an invertible S for every positive P. The inertia connection, weighted integral, legitimate measure exchange, hockey-stick substitutions and finite cutoff are also separate obligations. Approval of these eight statements does not discharge any of those obligations and changes no completed-target count.
