# Spectral recursion: numerical and probability contracts before implementation

Author: infrastructure/Gaussian agent. Scope: the spectral induction in manuscript Proposition 5.5, retaining the original IE-06 final target. Proposed owned files are SpectralRecursionScalars.lean, GaussianSpectralBase.lean, and GaussianSpectralRecursion.lean. The selected-block extension (B4) remains owned by the source-proof agent. This document is recorded before implementing the following estimates. Independent root review APPROVED these exact contracts before implementation on 2026-10-06. Root checked the coefficients 8 and β+802 against (D−4)/4≥β+1000, the exact A3 prefactor absorption, the strict μ bound, the recurrence loss, and the precise Fin n × Fin n pair count.

Use the exact actual selected block

`T_t(A) = GaussianPivotConditioning.selectedBlock ht (GaussianPivotConditioning.pivotOrder ht A) A`,

where `ht : t ≤ n`, and the actual `gaussianMatrix n` law. Singular values are the frozen genuine Euclidean zero-based `Spectral.singularValue`; source sigma_(t-d) means index `t-d-1`.

Fix `β≥1`, a positive constant `C` supplied by the unconditional B4 theorem, `λ=log n≥256`, and

`D = max (100*C) (4*β+4004)`.

For `d≥ceil(sqrt λ)`, set `k=ScalarRecurrence.step λ d`, with the exact finite orbit cost and profile `g(d)=ScalarRecurrence.profile n λ D d` already proved in ScalarRecurrence. In particular k=max(100d,ceil(d²/λ)); no recurrence rule is silently changed.

## Scalar contracts

1. Cost is nonnegative when λ≥0. For 0<d<n it is at least `1+λ/d`. The profile is positive for d>0 and at most d/sqrt n. If 0<k<n, then `g(k)<sqrt k` strictly, which supplies B4's strict upper bound on μ.

2. In the base regime `t≤8*k`, `d<t≤n`, set

   `θ = exp(-(D-4)*(1+λ/d))`.

   Then `0<θ≤1`,

   `g(d) ≤ d*θ/(4*exp(1)*sqrt t)`,

   and the exact finite-row union bound satisfies

   `n^t * t^(d+1) * θ^(d²/4) ≤ exp(-β*λ)`.

   All powers in the θ exponent are real powers; n^t and t^(d+1) are natural powers of positive reals. The proof uses `tλ≤8d²+800dλ`, the exact ceiling bound from ScalarRecurrence, and `(d+1+β)λ≤(β+2)dλ` for d≥1 and β≥1. Since `D-4≥4β+4000`, the negative exponent dominates `(t+d+1+β)λ`. The factor `4e` in the exact A3 theorem is absorbed by `4e≤exp 4`, and the cost's first term. Thus θ needs no additional prefactor and is manifestly positive.

3. In the recursive regime `8*k<t`, put `u=t-4*k`. Then `k<u<t`, `u+4*k=t≤n`, and k≥100d. The profile recurrence and `D≥100*C` give

   `g(d) ≤ (g(k)*d/k)*exp(-C*(1+k*λ/d²))`.

   This follows from the proved exact `1+kλ/d²≤2+100λ/d`; multiplying `1+λ/d` by 100 dominates the latter expression. All denominators are positive.

## Gaussian base case

For each fixed injection `π : Fin t ↪ Fin n`, the literal `selectedBlock ht π` has the actual t by t standard Gaussian pushforward law. This follows from the already proved fixed-coordinate Gaussian law and does not condition on the adaptive pivot order.

Apply the proved exact A3 to each such π with j=d≥16 and the θ above. The number of injections is at most the number of functions, exactly n^t. A finite union bound therefore bounds the bad event for the actual T_t by exp(-βλ), with no rank exception or adaptive-conditioning premise. The actual pivotOrder is an injection for every input, so it is one of the fixed candidates. All comparisons use the actual source threshold and original zero-based index.

## Induction and assembly

An initially reusable deterministic first-failure lemma may take the B4 probability bound as a named ordinary theorem hypothesis while its author finishes the proof. The final exported Gaussian recursion theorem must instantiate that hypothesis with the actual unconditional source-agent B4 theorem; no such hypothesis, sorry, custom axiom, or manuscript result may remain in the final result.

For every admissible pair (t,d), define its local failure as the current profile failure in the base regime, or the current profile failure together with all required earlier-stage profile bounds at u in the recursive regime. In the recursive case those earlier bounds imply both `sigma_(u-k)(T_u)≥g(k)` and the exact `sigmaInvSum T_u k≤2k/g(k)²` by ProfileSum. The scalar contract gives containment in B4's actual bad event. Thus each local failure has outer measure at most exp(-βλ).

Strong induction on t shows that any profile failure belongs to one local failure. Index pairs by two Fin n coordinates (t is one plus its coordinate, d is the other), giving at most n² events. The total outer measure is at most

`n²*exp(-βλ)=exp(-(β-2)λ)`.

With β=γ+2 for γ>0, the result gives, simultaneously for every `ceil(sqrt(log n))≤d<t≤n`, `g(d)≤singularValue T_t (t-d-1)`, outside outer measure exp(-γ log n)=n^(-γ).

ProfileSum then gives simultaneously, for every positive r≥ceil(sqrt λ) and t≤n,

`Sigma_r(T_t) ≤ 2*r/g(r)² ≤ (2*n/r)*exp(12*D*sqrt λ)`.

The second bound uses the already kernel-proved `cost≤6sqrt λ`. This is the deliberately sufficient auxiliary estimate for the unchanged final IE-06 probabilistic theorem. It does not claim the manuscript's sharper general-r log-log cost estimate; all original statements remain preserved in the problem/source documentation. Empty retained ranges r≥t are included by the exact finite sum definition.

All new declarations require LeanCert kernel audits and standard foundational axioms only. No native evaluation or externally assumed probability result is permitted. Evidence from local macOS compilation is explicitly distinguished from a Linux sandbox Comparator run.
