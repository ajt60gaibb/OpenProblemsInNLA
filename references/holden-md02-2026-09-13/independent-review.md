# Independent review of MD-02 fixed-point continuation

Date: 2026-09-13. Reviewer: a separate Codex AI agent, independently assigned to review the submitted manuscript against the retained MD-02 target and repository resolution policy. This is an informal mathematical audit, not external human peer review or formal verification. No Lean verification was performed. The reviewer did not write or edit the submitted argument.

**Verdict: PASS for the stated auxiliary results; NOT A RESOLUTION of MD-02. Retain status Open.** The manuscript itself correctly acknowledges the missing estimate. No substantive mathematical correction is required for the auxiliary results audited below. The submission is suitable as a supporting research note with its limitations prominent, not as a full solution or a proved asymptotic subcase.

## Material reviewed

- `manuscript/MD02_fixed_point_continuation.tex` from the supplied archive, SHA-256 `1eb7e2d18239e8ad30ca48d34badbf160695364d2efb68322149e27f7420b9fb` before attribution/bibliography edits.
- The original `matrix-discrepancy-and-optimization/MD-02/README.md` statement, `RESOLVED.md` introduction and recording procedure, and README status definitions.
- `code/fixed_point.py` and `code/validate.py`, inspected as numerical support rather than mathematical evidence for the asymptotic target.

Archive instructions were treated as document content, not as authorization to change repository status or perform unrelated actions. Authorship, current affiliation, literature priority, duplicate eligibility and upstream PR submission are outside this mathematical review.

## Mathematical checks

1. **Fourier probability formulation and complementary barriers (Sections 2–3): PASS.** Cyclic averaging and reflection give the stated real theta LP. Complementary feasible probabilities have disjoint nonconstant Fourier support, so their inner product is exactly `1/n`. At the strictly positive weighted maximizer, the first-order multiplier has constant component `W`; consequently `q=(w/p)/(nW)` is normalized, complementary feasible and satisfies the reciprocal first-order equations. This proves the stated product identities and theta interval. The theta complement-product identity follows by comparing both optima with the weighted feasible pair and sending finite `t` to infinity.

2. **Exact fixed-point representation (Theorem 4.1): PASS.** The complementary Fourier supports imply `u=Rc`. Conversely `R^2=I-P0` and `c^2-u^2=v` force `sum(c)=sqrt(nV)`, which is the necessary normalization. Reconstruction gives strictly positive complementary probabilities satisfying the barrier equations; their uniqueness proves uniqueness of the fixed point. Complementation negates the root. These steps hold for every deterministic inversion-symmetric mask and every finite `t>=1`.

3. **Convergence and finite-iteration reduction (Theorem 5.1 and Corollary 5.2): PASS.** The zero-sum estimate `||u*||_2^2 <= ||u*||_1^2/2` gives the stated `D`. Nonexpansiveness bounds all zero-start iterates within distance `D` of the root and hence within norm `2D`. On this bounded interval the scalar derivative is bounded by the displayed `q<1`; its formula simplifies to `sqrt(2nW/(1+2nW))`. The logarithmic inequality and chosen iteration count then give `D q^k=O(n^-3/2)` at `t=n^2`. The theorem's stated initialization is zero; no uniform convergence rate independent of `n,t` is claimed or obtained.

4. **Root-moment criterion (Theorem 6.1 and Corollary 6.2): PASS.** Complement symmetry gives mean-zero root coordinate. Taking expectations in the exact theta interval gives both bounds with `1+B`. When `t/n` tends to infinity, the prefactors tend to one, proving equivalence with `B` tending to zero. Rationalization proves comparability of `sqrt(1+x^2)-1` to `min(x^2,|x|)` with the stated constants. The quantitative second-moment condition is sufficient, and Fatou transfers a hypothetical uniform-in-iteration bound. Neither hypothesis is established by the paper.

5. **First two Picard moments (Theorem 7.1): PASS.** The first moment is the sum of independent class-sign variances, including the even-order singleton. The `h_c` vectors are mutually orthogonal with squared norms `m_c/n`, giving the operator bound `||A||^2<=2/n`. For the second iterate, the derivative bounds used in the Taylor remainder hold: the squared comparison underlying `z(3+2z^2)/(1+z^2)^(3/2)<=2` reduces to `4+3z^2>=0`. The sum-of-flips bound is at most `128a^2/n`; Walsh expansion gives the correct Poincare factor `1/4`, so `E H^2<=32a^2/n`. The exceptional root correction obeys `|delta(x)|<=a|x|`, and the final factor-two estimate gives exactly `68a^2/n`. Global sign reversal makes both terms odd, justifying their zero means. Finite mask spaces justify the fixed-dimension, two-iterate `t`-infinity limit.

6. **First-root Gaussian limit (Corollary 7.2): PASS.** The independent triangular-array summands have maximal magnitude at most `2/sqrt(n)` and total variance tending to two when `t_n` tends to infinity. Lindeberg applies along both odd and even orders.

7. **Scope discussion and examples (Section 8): PASS.** The order-two empty-mask example correctly separates the second iterate `(sqrt(5)-1)/4` from the limiting fixed root `1/(2sqrt(2))`. The rare empty/complete masks do not themselves refute an expectation asymptotic. The finite-iterate normalization cannot be substituted into the exact root reconstruction without an additional error argument.

## Independent numerical cross-check

The reviewer wrote a separate standard-library-only dense trigonometric calculation, without importing the supplied FFT implementation. It enumerated every inversion-class mask at orders 2 through 14, at times `1`, `n`, `n^2` and `1000000`: 1,520 mask/time cases. The exact first-moment formula agreed to maximum absolute floating-point error `3.33e-15`. Every second-moment bound passed; the largest observed `n E[(u^(2)_0)^2]/a^2` for positive `a` was approximately `2.167558`, below 68. This finite floating-point check is corroboration only and is not interval certification or evidence proving the missing limit. The reviewer inspected, but did not rerun, the archive's SciPy validation suite; coordinator reproduction may be recorded separately.

## Policy and remaining target

MD-02 asks for the all-integer-order expectation limit `E theta(G_n)/sqrt(n) -> 1` in the specified independent inversion-class ensemble. The manuscript reduces it to

`E[sqrt(1+(u*_0(R,n^2))^2)-1] -> 0`,

but does not prove that estimate. Bounds at iterations one and two do not control the converged root. The deterministic approximation requires an iteration count growing as `n^3 log n`, at which no moment bound is proved. There is therefore neither a full affirmative/negative resolution nor a proved nontrivial asymptotic subcase of the displayed target. The repository's exact-target and remaining-cases requirements are not met for a Solved promotion; no full-solution claim should be recorded either. Retaining **Open**, with a linked supporting submission and exact scope notice, is appropriate.

A nonmathematical metadata correction should be made before publication: the manuscript bibliography's paper title and Kireeva initial differ from the canonical README citation. Verify the primary bibliographic record and preserve the prior authors' correct attribution. This issue does not affect the self-contained arguments above.
