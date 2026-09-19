# MI27 scalar-pencil statements — independent referee B

**Verdict: APPROVE all seven exact helper headers for implementation.** No mathematical, domain, sign or integrability blocker was found. This is a pre-body statement review only; it is not acceptance of a Lean proof, the matrix-pencil connection, full C11 or the original MI27 target.

Reviewer: `/root/nr04_mf14_final_referee_b`, an independent nonauthor AI agent, 19 September 2026. Reviewed source: `development/MI27-C11-referee-a-v1/PENCIL-SCALAR-STATEMENTS.md`, exact SHA256 `7dd3a476ae60b8d7e15833dfd12e33db55af88754e928b118552435599e56e42`. I inspected the two literal definitions and seven headers, their preceding negative-count statement plan, and the relevant pinned Mathlib API signatures. I did not author/edit proof bodies, run Lean/Lake/Comparator, or change publication or counts.

Write (w(t)=1/(|t|(t-1)^2)) and (P(t)=\log(1+1/(t-1))-1/(t-1)), using Lean's totalized real operations. The weight is exactly the one in the earlier count-layer-cake checkpoint. These definitions encode scalar expressions and no desired integral equality.

| Exact header | Independent assessment |
|---|---|
| `c11_pencilWeight_nonneg` | Correct for every real (t): its denominator is nonnegative, including the totalized zero values at (t=0,1). |
| `c11_hasDerivAt_pencilPrimitive` | Correct for precisely the stated nonsingular domain (t\ne0,1). With (q=1/(t-1)), (q'=-1/(t-1)^2), and (1+q=t/(t-1)\ne0), differentiation gives (P'=1/[t(t-1)^2]). |
| `c11_tendsto_pencilPrimitive` | Correct at both infinite ends: (q\to0), (1+q\to1), and real log is continuous at 1. The finite totalized singular values do not affect either limit. |
| `c11_pencilWeight_integral_positive_tail` | Correct for (a>1). On the whole closed ray ([a,\infty)), (P'=w\ge0); its finite limit is 0, yielding integrability and tail integral (-P(a)). |
| `c11_pencilWeight_integral_negative_tail` | Correct for (a<0). On the negative ray (P'=-w), so the integral from (-\infty) to (a) is also (-P(a)). Reflection uses (g(s)=P(-s)), for which (g'(s)=w(-s)\ge0) on (s\ge-a>0), with limit 0. |
| `c11_pencilPrimitive_at_threshold` | Correct when (c>-1) and (c\ne0). Here (1+c>0), and (1/(-1/c-1)=-c/(1+c)). Thus (-P(-1/c)=\log(1+c)-c/(1+c)). No invalid division by (c) or (1+c) is required. |
| `c11_scalar_pencil_count_integral` | Correct for all (c>-1), with actual real Bochner integrability as well as the integral identity. Its strict support splits into the three cases below. |

The derivative header deliberately also covers (0<t<1), where the logarithm argument is negative. This is valid for Mathlib's `Real.log`, which agrees with the log of the absolute value and has derivative (x^{-1}) for every (x\ne0). The pinned `Real.hasDerivAt_log` signature requires nonzero argument, not positive argument. Neither singular point should be added to the derivative statement: totalized point values do not remove the surrounding singularity.

For (c>0), the condition (1+tc<0) is exactly (t<-1/c), with (-1/c<0). For (-1<c<0), it is exactly (t>-1/c), with (-1/c>1). Both supports therefore avoid an entire neighborhood of each singular point. For (c=0), the integrand is identically zero and the right side is `log 1 - 0 = 0`. No nonzero-parameter hypothesis is missing from the final theorem.

At the threshold (t=-1/c), the strict indicator is zero as required by strict negative-eigenvalue counting. Both tail sets exclude this point. Reflection may produce a closed endpoint through `integral_comp_neg_Ioi`; the single point has zero Lebesgue measure, so the Iic/Iio conversion is legitimate. The final integral is over the entire real line with ordinary volume, not a principal value. Its explicit `Integrable` conjunct prevents an accidental reliance on Lean's default value for a nonintegrable Bochner integral. The implementation must establish integrability of the supported function; the bare weight is not globally integrable near 0 and 1.

The restriction (c>-1) is essential. At (c=-1), the indicator activates the positive tail immediately after 1, where the integral diverges; for (c<-1), its support also reaches the singularity at 1. These cases are correctly excluded. Limits as (c\to0\) or (c\downarrow-1\) introduce no missing premise because no uniform bound or exchange of a parameter limit with the integral is asserted. Repeated scalar eigenvalues cause no issue: the theorem can be applied to every eigenvalue separately, with multiplicity retained in later finite sums.

The proposed API route is sound at pinned Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`. The primed Ioi integrability and FTC theorems require derivatives on the closed ray, which the strict endpoint hypotheses supply. The negation substitution changes the negative tail to a positive ray with the correct derivative sign. Indicator rewriting then converts the tail integrability and set integral to the all-real integrability and Bochner identity. This is an API feasibility check, not an elaboration test.

These headers add no congruence-inertia assumption, simultaneous diagonalization, distinct-eigenvalue hypothesis, matrix logarithm congruence rule, Tonelli conclusion or C12 premise. Those matrix/measure connections remain separate obligations. The scalar component is ready for source-body development under the existing root-only compiler workflow. Completion-count increment: zero.
