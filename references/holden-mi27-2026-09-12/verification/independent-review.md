# MI-27 independent informal mathematical audit

**Verdict: PASS — complete affirmative resolution of the canonical coefficient-one target.**

Review date: 13 September 2026 (UTC; 12 September in the submitting user's timezone). Reviewer: a separate Codex AI reviewer agent, assigned to inspect the submission independently of the agent preparing the repository changes. This is an informal AI-agent mathematical audit, not external human peer review, formal verification, or a publication-priority determination. No Lean verification was performed or required for this review.

## Material and exact scope

I read the original canonical `matrix-inequalities-and-norms/MI-27/README.md`, the supplied `solution.md`, the complete mathematical argument and appendices of `solution.tex`, and the resolution rules in `RESOLVED.md` and `CONTRIBUTING.md`. I treated the package's prior audit and its claims as untrusted evidence, and checked the proof itself. The uploaded sources reviewed have SHA-256 hashes:

- `solution.md`: `1f816442e70a4f703dd0740c419d6fa411b5bfcf87b07b2ab6c9dbcfcc6e9655`
- `solution.tex`: `8b2047e8e1e702cf2c158480de9384f10d47da4e42ecde72599a88320a5d8945`
- `verification/verify.py`: `46979b8a9890e067f029fb4f998907f2823cb26b94c5ffb1ca3e4488bafff9ff`

The theorem covers every integer n >= 1 and every complex Hermitian strictly positive definite A and B with tr(A+B)=1. It establishes the full trace norm of [B,log(A+B)] bounded by -a log(a)-b log(b), with a=tr(A), b=tr(B), and natural logarithms. No dimension bound, commutativity assumption, rank restriction, or factor-of-two change of trace-norm convention is introduced. It also proves that coefficient one cannot be decreased, within the same strictly positive definite input class. The main theorem is Theorem 1.1 in the TeX source; its proof is in Sections 2–5. Markdown Sections 2–5 give the corresponding argument.

## Independent analytic checks

1. **Elementary commutator bound.** For an effect 0<=Q<=I, the matrix R=2Q-I has operator norm at most one. The trace-norm triangle and product inequalities give ||[X,Q]||_1 <= ||X||_1 for X>=0, hence <=tr(X). This is dimension independent and uses the full trace norm.

2. **Differentiation at spectral crossings.** For each fixed gamma, the positive-part trace of M(t)=rho-gamma sigma_t is locally Lipschitz because the variational formula makes it Lipschitz with respect to the trace norm. It is therefore absolutely continuous on compact intervals. At a differentiability point, the fixed positive spectral projection Q_t maximizes the variational expression. Taking positive and negative increments in the maximizing inequality forces the asserted derivative, without differentiating Q_t. This remains valid even if M(t) has a zero eigenvalue. The proof only uses derivatives almost everywhere and correctly integrates them.

3. **Uniform cancellation of gamma.** Since Q_t commutes with rho-gamma sigma_t, [rho,Q_t]=gamma[sigma_t,Q_t]. Cyclicity of trace therefore gives f'(t)=-i tr(H[rho,Q_t]); its absolute value is at most ||H||_infinity. This is the crucial improvement over an estimate proportional to gamma. Reversing the arguments is justified by joint unitary invariance and generator -H, for arbitrary pairs of real times.

4. **Published input independently checked.** I opened the primary author manuscript [Hirche–Tomamichel, arXiv:2306.12343v3, Section 2.3](https://arxiv.org/html/2306.12343v3#S2.SS3). Corollary 2.3, equation (2.22), gives precisely the two positive-part integrals with weights 1/gamma and 1/gamma^2 for ordinary Umegaki relative entropy. Equation (2.20) supplies that entropy definition, and Theorem 2.2 identifies the originating result as Frenkel's Theorem 6. Thus the submission does not mistakenly substitute a different noncommutative divergence. The normalization used here is valid for states and gamma>=1. I accepted this published theorem as an external input; I did not independently re-prove Frenkel's theorem.

5. **Changes of variables and entropy kernel.** In the first skew integral, 1-alpha v=beta/(beta+alpha gamma) and dv/dgamma=beta/(beta+alpha gamma)^2, while 1/v=(beta+alpha gamma)/gamma. Their product gives beta^2/[gamma(beta+alpha gamma)^2]. The second substitution gives beta^2/(alpha+beta gamma)^2. Combining the two weighted relative entropies yields exactly ab/[gamma(b+a gamma)] and ab/[gamma(a+b gamma)]. Both kernels are positive; their integrals are -a log(a) and -b log(b), using a+b=1. The positive-part quantities lie in [0,1], so these final integrals converge. The derivation applies in particular to the positive definite states needed for MI-27, avoiding any support difficulty.

6. **Entropy bound and trace-norm conclusion.** Unitary invariance cancels the individual input entropies. Integrating the finite-difference Lipschitz bounds against the fixed positive kernels gives the claimed entropy difference bound. There is no unjustified differentiation under an improper integral. Because A+U_t B U_t* is strictly positive definite, its entropy is differentiable, with derivative -i tr(H[B,log(A+B)]). The trace derivative uses tr(i[H,B])=0. The matrix K=-i[B,log(A+B)] is Hermitian; H=sign(K) is an admissible Hermitian contraction and satisfies tr(HK)=||K||_1. This proves the exact canonical inequality. The choice of H after establishing the estimate for every H is legitimate.

7. **Strict positive definiteness and sharpness.** The proposed middle factor t^2 I+(1-2t^2)P_t has eigenvalues t^2 and 1-t^2. Both lie strictly between zero and one for 0<t<1/2; congruence by T_t^(1/2) proves both A_t and B_t strictly positive definite. Their sum has trace one. The determinant is t^3(1-t)(1-t^2) for each matrix. The commutator has two singular values equal to d_t log((1-t)/t). Since d_t/t tends to one and b_t/(2t) tends to one, numerator and entropy denominator both have leading term 2t log(1/t). Consequently their ratio tends to one. No coefficient below one works, even in dimension two.

8. **Appendices.** The skew-divergence kernel masses sum to -log(alpha), giving the normalized Lipschitz bound. The projection consequence follows by epsilon regularization with a fixed positive sum. Conversely, the spectral decomposition expresses any effect as a convex combination of projections including zero. Trace-norm convexity followed by concavity of binary entropy has the correct direction even though the component traces differ. These additions are consistent with, but unnecessary to, the main resolution.

## Computational inspection and limits

I inspected the complete `verification/verify.py` before attempting execution. It performs local mathematical computations using NumPy, SciPy, SymPy and mpmath, then writes an explicitly chosen JSON output. I found no network access, subprocess execution, or unrelated filesystem effects. Its symbolic checks and finite numerical tests are appropriate consistency evidence, but cannot prove the universal theorem.

Initial attempts with system and bundled Python stopped at a missing `mpmath` import. After the submitting agent installed the pinned dependencies in a temporary environment, I independently reran the original script using `/private/tmp/mi27-verify-env/bin/python`, with deterministic seed 270912. The run completed successfully with exit status zero: **all six groups passed** (nine exact symbolic identities, positive-part checks, weight masses, integral identities, matrix inequalities, and sharpness family). The maximum integral-identity error was 7.327471962526033e-15. The largest sampled MI-27 ratio was 0.4490172264802815; this finite sample is consistency evidence only, while the analytic family establishes sharpness. The complete independent run is recorded in `mi27-review-rerun.json` and `mi27-review-rerun.log` (prepared in `/private/tmp/` for inclusion in the submission verification directory). The analytic PASS does not depend on these numerical results.

## Resolution-policy conclusion

No mathematical gap was found in the complete canonical target, including its quantifiers and normalization. The repository expressly permits `Solved` for a complete argument passing an informal independent AI-agent audit, provided that this actual review level is recorded and linked. On that basis, this argument qualifies for **Solved**, subject to the submitting agent retaining the canonical ID, path and original target, adding the primary manuscript and exact theorem locator, recording authorship/provenance accurately, and performing the repository's required rendering and catalog checks. It does not qualify for `Lean verified` on this evidence.

This report does not determine authorship, current affiliation, duplication against already-pushed submissions, external novelty, or publication priority; those are separate submission checks. Adding verified author metadata without altering the mathematics does not affect this mathematical verdict. Any substantive mathematical change requires renewed review.

## Final submitted-source comparison

I compared the prepared repository sources under `references/holden-mi27-2026-09-12/` with the uploaded sources reviewed above. The only changes are author/affiliation front matter in Markdown and TeX and the TeX PDF author metadata. **The mathematics is unchanged**, so the analytic PASS applies to the prepared sources. Their SHA-256 hashes are:

- `solution.md`: `ae5a9c05e57c5c56f4eac63cf46b11d56fe1d9c5d1bde84978ae8821e454133d`
- `solution.tex`: `34169e9e59d83d8e243c0430ba59e1e69b560d53fcc1d6ea674c1001323fae4a`
- `verification/verify.py` (unchanged): `46979b8a9890e067f029fb4f998907f2823cb26b94c5ffb1ca3e4488bafff9ff`

The affiliation itself is checked by the submitting agent's separate source record, not inferred from this mathematical review.
