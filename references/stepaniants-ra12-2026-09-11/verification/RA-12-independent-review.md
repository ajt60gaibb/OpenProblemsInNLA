# Independent mathematical review of the RA-12 manuscript

Reviewer: separate Codex agent `/root/prepare_manuscripts`.
Review date: 11 September 2026.

**Verdict: PASS for the complete canonical RA-12 implication in the exact frozen source identified below.** I found no unresolved mathematical gap in the proof after an independent reconstruction and an adversarial check of the manuscript. This is an independent agent audit, not human peer review or formal certification.

## Exact target

I read the retained canonical problem at `randomized-and-low-rank-approximation/RA-12/README.md` and checked Hallman's primary statement, Theorem 6 and Conjecture 3 in [arXiv:2411.15454v1](https://arxiv.org/html/2411.15454v1). The target is the complete two-comparison probability chain for every nonzero real symmetric positive semidefinite matrix A, every positive integer m, and every epsilon >= 2/(m mu), with mu = tr(A)/||A||_2 and the specified capped-spectrum matrix B_mu. The Gamma comparison distribution has shape and rate m mu/2. The target concerns the actual tail probabilities; the stronger auxiliary upper-mode conjecture is distinct.

## Independent reconstruction

Before reading the integrated draft, I reconstructed the proposed mode, coefficient-transfer, and infinite-splitting arguments from the exact target and the short candidate description. I then read the complete manuscript and checked each assumption and transition against that reconstruction.

1. **Gamma representation and normalization.** Orthogonal diagonalization and independence give chi-square_m/2 ~ Gamma(m/2, rate 1). Writing alpha=m/2 and w_i=lambda_i/||A||_2 gives sum w_i=mu, 0<=w_i<=1, rho=alpha mu, and T_m(A)/tr(A) distributed as Q_w/rho. The same normalization makes T_m(B_mu) distributed as Q_ext/rho. If H has shape rho and rate one, H/rho has shape and rate rho. Thus the displayed relative threshold is exactly h=rho epsilon>=1; no factor of two, scale/rate conversion, or effective-rank change is lost.

2. **Mode identity.** For a finite Gamma convolution with shapes r_i and positive scales w_i, I independently differentiated L(u)=product(1+w_i u)^(-r_i), obtaining -L'=L K with K the Laplace transform of k(t)=sum r_i exp(-t/w_i). Therefore x f=k*f. Differentiation by the kernel gives f+x f'=k(0)f+k'*f. At a positive global mode z, extending f by zero and putting v(t)=1-f(z-t)/f(z) produces both M-z=integral k v and 1=integral(-k')v. The latter constant is one, not total shape. Since v>=0 and w_min(-k')<=k<=w_max(-k'), the claimed mode interval follows with the correct inequality directions.

3. **Regularity and attainment.** The density assumptions hold when total shape beta>1. A direct simplex-convolution representation bounds the density by C x^(beta-1) exp(-x/w_max), gives positivity for x>0 and smoothness there, and shows that the density vanishes at zero and infinity. Thus a positive global mode exists and has derivative zero. Differentiating the smooth convolution kernel only requires local integrability of f; no bounded derivative at zero is tacitly required when 1<beta<=2. The transfer's augmented density has total shape strictly greater than two, so in particular its value at zero is zero and its first derivative is continuous at positive cutoffs.

4. **External unimodality theorem.** I independently opened [Roosta-Khorasani and Szekely, arXiv:1601.04731v1](https://arxiv.org/html/1601.04731v1), Appendix A, Theorem 4 and Lemma 5. Theorem 4 explicitly covers independent Gamma variables with arbitrary positive shapes and rates and nonnegative coefficients. Lemma 5 gives positivity, analyticity on the positive half-line, and vanishing derivatives at zero for orders below total shape minus one. Zero-weight terms are discarded before applying the positive-scale statements. These hypotheses cover every augmented density used in the manuscript. The version record contains only v1, submitted 18 January 2016, and gives the cited Metrika 78(8):997-1014 (2015) journal reference and DOI 10.1007/s00184-015-0537-9. I did not reprove the classical unimodality theorem; it is an explicit published external input. The audit does not depend on an unverified inference that arbitrary convolutions of unimodal densities are unimodal.

5. **Choice of the transfer.** If there are at least two fractional coefficients, choosing b as a smallest positive fractional coefficient makes it a minimum among all positive coefficients, because every positive nonfractional coefficient is one. Increasing a and decreasing b preserves this property until saturation. Zeros cannot create a smaller positive scale. At an interior transfer time, all augmented scales lie between b(t) and one and the augmented mean is rho+a(t)+b(t). The upper mode bound is therefore rho+a(t)+b(t)-b(t)=rho+a(t)<=rho+1. The lower mode bound is at least rho+a(t)+b(t)-1>=rho-1. This is the critical restricted-path argument; it does not assert that arbitrary augmentation indices satisfy this interval.

6. **Coefficient derivative and sign.** I independently obtained d_t(L_Q/u)=alpha(a(t)-b(t))u L_Y, hence d_t F_Q(x)=alpha(a(t)-b(t))g_t'(x), with the positive prefactor and correct derivative order. The zero boundary term follows from g_t(0)=0. On every compact time interval before a coefficient vanishes, parameter differentiation is valid: the simplex density formula yields a dominating bound C x^(beta-1)(1+x)exp(-c x) for the base density's parameter derivative. Laplace uniqueness identifies the resulting continuous functions for x>0. This also matches Hallman's Appendix A.1. Unimodality and the mode interval give increasing lower CDFs at x<=rho-1 and decreasing CDFs at x>=rho+1, hence increasing probabilities of each tail along concentration.

7. **Termination and boundary cases.** Equal fractional weights are allowed: the derivative is zero initially and nonnegative/ nonpositive as appropriate thereafter. Each transfer has positive length and makes at least one fractional coordinate equal to zero or one, while creating no new fractional coordinate from a previously integral coordinate. Finitely many transfers therefore reach the stated extremal vector. Coefficient convergence gives almost-sure convergence under a fixed Gamma coupling; the endpoint law remains continuous, so a vanishing b or saturated a causes no endpoint gap. If rho<=1, the lower cutoff is nonpositive and its event has probability zero. The cases of a zero cutoff, integer mu, rank one, rank deficiency, zero padding, and equality h=1 are covered. Upper and lower tail events are disjoint because h>=1>0, and all finite endpoint laws have no atoms.

8. **Gamma upper comparison.** For each integer N, splitting every Gamma(alpha,1) variable into N independent Gamma(alpha/N,1) variables preserves Q_w in distribution and preserves rho while repeating the coefficient list N times. Lemma 3 applies for all alpha>0, so it remains valid for alpha/N. Its extremizer has a unit-scale Gamma component of shape alpha floor(N sigma)/N and an independent nonnegative residual of mean at most alpha/N. For all sufficiently large N the first shape is positive and tends to rho; the residual tends to zero in probability. The limiting law is Gamma(rho,1). The cutoffs rho-1 and rho+1 do not depend on N, and the limiting CDF is continuous at every real point. Thus the two one-sided comparisons pass to the limit. Applying this result to Q_ext gives the second member of the required chain.

9. **Auxiliary counterexamples and claimed scope.** The repository's upper-mode counterexample augments two large coefficients while a smaller positive coefficient remains. That configuration does not occur along the manuscript's selected transfer path. For example, coefficients (1,1,1/2,1/2) are transferred through the two fractional coefficients, not the two ones. The manuscript therefore does not contradict or silently retract the existing auxiliary counterexample. The proof establishes validity at the stated threshold; it does not prove that no smaller threshold could work. No claim is made for indefinite matrices, the absolute-error RA-13 problem, arbitrary majorization paths, or arbitrary augmentation indices.

## Review observations resolved before freezing

Two wording clarifications were requested: the elementary weak-convergence alternative should describe its Gamma component only for sufficiently large N when the general coefficient sum sigma could be below one; and the scope should say the 'stated endpoint' rather than call it sharp without an optimality proof. These do not expose a gap in the complete RA-12 application, which has sigma=mu>=1. Both changes are present in the frozen source. The unimodality source links are also pinned to arXiv:1601.04731v1. I checked these edits and recomputed the source hashes locally.

## Limitations

The verdict concerns the mathematical implication stated in the canonical problem and the exact reviewed source. It is not a claim of human peer review, machine-checked formal verification, optimality of the threshold, or historical priority. No numerical scan is used as a substitute for the proof. Publishing eligibility and the final branch/fork duplicate-solution check are separate responsibilities of the parent agent.

## Frozen source and signed verdict

- Reviewed source: [full-proof-candidate.md](../full-proof-candidate.md).
- Full source size: 12,071 bytes.
- Full source SHA-256: `247d615cab324975198b7b4f743deb44b45fd41a893224153603a2143be6b78f`.
- Mathematical core: from the literal `## The statement` inclusive to the literal `## Scope and relation to the auxiliary counterexamples` exclusive.
- Mathematical core size: 9,988 bytes.
- Mathematical core SHA-256: `29bf6811ba39b1f4e4507cb3b98daec6fc9d545809cf019c288a759e34154400`.

Signed: independent Codex reviewer `/root/prepare_manuscripts`, 11 September 2026. **PASS.** The exact manuscript proves both comparisons for all of the canonical problem's parameters, including the stated endpoint. This verdict incorporates the external published unimodality theorem explicitly identified above and the stated limitations.
