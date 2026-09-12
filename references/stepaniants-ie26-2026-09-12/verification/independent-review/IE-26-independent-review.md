# IE-26 independent adversarial mathematical review

Reviewer: separate Codex agent `/root/prepare_manuscripts`  
Date: 12 September 2026 (UTC)

**Verdict: PASS for the complete retained IE-26 target, both bounds.** I independently reconstructed the analytic argument, checked the exact norm conventions and parameter ranges against the canonical target and primary sources, and found no mathematical gap. The first estimate has an absolute constant uniform in the perturbation parameter; the second has the permitted constant depending on a fixed parameter strictly between one quarter and one half.

This verdict is bound to the exact frozen candidate identified below. No mathematical correction is required. It is an independent Codex-agent audit, not external human peer review, proof-assistant verification, or a formal certificate. No repository page or status was changed during this review.

## 1. Reviewed inputs and independence

| Input | Bytes | SHA-256 |
| --- | ---: | --- |
| [Candidate snapshot](reviewed-candidate.md), originally `../RESULT.md` | 20,755 | `5ce6d660bb1b22f0c4dec439934e883b3e014708e49a63de2dba2760c939d295` |
| [Canonical target snapshot](canonical-target.md) | 5,051 | `c7d4e909081c37d0e7ea7e7b97c17c39a45e794e55f3165b09a34e4519fd185b` |
| [Independent exact algebra checker](exact_algebra_check.py) | 7,730 | `65c9827a492d2372ff50d251e47766ba54f56904a556bef8ee90f6b899d4e723` |
| [Exact checker output](exact-algebra-output.json) | 3,089 | `25fc4aeebe575f1af6026508f5992647e7191bbffdc4c984028e3cee04b03b30` |

The canonical snapshot was read from `linear-systems-and-elimination/IE-26/README.md` in `/tmp/nla-sp15-worktree`. The [manifest](manifest.json) binds the report and supplementary source notes as well.

I did not develop the candidate or its proof route before freeze. The originating agent and coordinating agent contributed to that route and are not counted as this separate final reviewer. I did not use their numerical checker. I wrote the exact rational-arithmetic supplement independently after reconstructing the proof. Neither finite computations nor a coordinating-agent endorsement are premises of this PASS.

## 2. Exact target and primary-source checks

The candidate retains arbitrary complex interpolation data, every integer `N >= 2`, all real shifts with `|s_j| <= alpha`, and the odd grid size `m=2N+1`. Its first conclusion is the canonical universal bound

\[
\Lambda_N\le C\frac{N^{2\alpha}-1}{\alpha(1-2\alpha)},
\qquad 0<\alpha<\tfrac12.
\]

Its second conclusion is precisely

\[
\|F_N(s)^{-1}\|_2\le C_\alpha N^{4\alpha-1},
\qquad \tfrac14<\alpha<\tfrac12,
\]

with `alpha` fixed in the second assertion. There is no restriction to random shifts, special signs, sufficiently smooth interpolation data, or a subsequence of dimensions.

I directly checked [Austin–Trefethen (2017), equation (12) and its conjectured sharpening, pp. 2115–2116, and the second-norm conjecture, p. 2119](https://people.maths.ox.ac.uk/trefethen/perturbed.pdf). These match the two requested powers and the strict supercritical range of the second bound. [Austin's thesis, Conjectures 3.5 and 3.10, printed pp. 75 and 82](https://personal.math.vt.edu/apaustin/pubs/DPhilThesis.pdf), confirms the first bound's parameter-independent constant and contains a stronger endpoint assertion that is not imported here.

The normalization is consistent with [Chen–Lin–Zhang, arXiv:2608.21960v1, equations (1.6)–(1.7)](https://arxiv.org/html/2608.21960v1): the normalized inverse Fourier matrix accounts for the square-root-of-grid-size conversion. Complex conjugation or index permutations do not alter its singular values. The candidate proves the norm for its stated matrix directly, rather than relying on a potentially lossy norm conversion.

The only external inequality used in the proof is verified directly in [Laugesen, arXiv:0903.3845v2, Theorem 12.1, printed p. 67](https://arxiv.org/pdf/0903.3845v2). It is a periodic Hilbert-transform weak `(1,1)` estimate for all `L^2` boundary data and every positive threshold, with an absolute constant. Smooth data in the candidate satisfy its hypothesis. Normalized versus ordinary angular measure changes only an absolute factor. I also read the source's proof and the stated Fourier-multiplier convention.

## 3. Interlacing, phases, and residues

Distinctness follows from the strict inequality `alpha < 1/2`: each perturbed root remains inside its own open cell between consecutive zeros of `Q(z)=z^m+1`. This remains true along the entire homotopy that multiplies all shifts by a parameter in `[0,1]`.

Because `m` is odd, the product of the unperturbed roots is one. Therefore

\[
P(0)=-e^{2i\vartheta},\qquad R(0)=e^{i\vartheta},
\qquad |\vartheta|\le\pi\alpha<\pi/2.
\]

The sine-product expression on the boundary gives a purely imaginary `R` with the stated phase, not its negative or an uncontrolled rotation. Near a pole `eta`, pure imaginary boundary values force the coefficient of `(eta+z)/(eta-z)` to be real. The coefficient is nonzero throughout the homotopy, because a numerator zero never reaches a pole. It starts at `1/m`, and therefore stays positive. The same reasoning applies to the reciprocal. After all pole terms are removed the rational remainder is constant: the function is bounded at infinity and has no finite poles. Its boundary real part vanishes, so this remaining constant is purely imaginary.

This proves the positive-real representations throughout the open disk, not merely on a sampled radial line. In particular,

\[
\sum_j\beta_j=\operatorname{Re}(e^{-i\vartheta})=\cos\vartheta\le1.
\]

The residue of the kernel at `z_j` is `-2 beta_j z_j`. The residue of the reciprocal expression gives

\[
2\beta_j=\frac{|Q(z_j)|}{|P'(z_j)|},
\qquad |Q(z_j)|=2\cos(\pi s_j).
\]

The cosine is positive for every allowed shift. Its lower bound by `cos(pi alpha)` has the correct direction. The resulting Poisson representation is exact and has positive summands. No cancellation of signed residues is assumed.

## 4. Exact radial exponent and the first bound

Differentiating the logarithmic distance with respect to the root angle gives the negative of the kernel `K_t` in equation (12), including its factor one half. For `t <= T`, its difference has the sign of `sin u`. Consequently its exact integral is

\[
\|K_t-K_T\|_{L^1}
=2\log\frac{\coth(t/2)}{\coth(T/2)}
\le2\log(T/t).
\]

For clarity, the last comparison follows from monotonicity of `v coth(v/2)`: its derivative has the sign of `sinh v-v`, which is positive for `v>0`. The maximum of `K_t` on `(0,pi)` is `1/(2 sinh t)`, so its total variation is `2/sinh t <= 2/t`. The cell-supremum estimate therefore contributes only an absolute additive constant to the logarithm because `h/t <= h/t_0=2pi` and `alpha<1/2`.

Thus the logarithmic coefficient remains exactly `2 alpha`. It is not enlarged by a hidden multiplicative constant in the integral estimate. The factors from `P_0/Q` are uniformly above zero and bounded at every height with `mt>=1`. Sending the comparison height to infinity is legitimate by the same kernel calculation with the second kernel zero, and `|R(0)|=1`. This proves both radial estimates with absolute constants.

The trigonometric cardinal function is `(z_j/z)^N` times the algebraic cardinal polynomial on the unit circle; hence their moduli agree. The exact identity

\[
|r\zeta-z_l|^2=r|\zeta-z_l|^2+(1-r)^2
\]

for unit `z_l,zeta` yields the radial product bound. Only the `m-1` noncardinal factors are used, so their accumulated factor is at most `exp(1/2)`. In particular, evaluation exactly at a node causes no division by a zero boundary factor.

On a dyadic annulus of angular radius `T`, the original radial denominator is bounded below by an absolute multiple of `T`; for the first annulus, `t_0` supplies that lower bound. The Poisson kernel at height `T` is bounded below by an absolute multiple of `1/T` throughout the annulus. Summing the positive residues gives equation (17), and the radial comparison then gives equation (18). The remaining angular distances at least one are bounded using the total residue mass and the global radial estimate.

The last geometric sum is uniform even when `alpha` tends to zero. One must retain the subtraction of one in its numerator. Indeed, for `a=2alpha` and `L=ceil(log_2 m)`,

\[
\sum_{q=0}^{L}2^{aq}
=\frac{2^{a(L+1)}-1}{2^a-1}
\le C\frac{m^a-1}{a},\qquad 0<a<1,\ m\ge5.
\]

Here `2^a-1 >= a log 2` and `2^{L+1} <= 4m`; the ratio of the two subtracted numerators stays absolutely bounded for `m>=5` and `0<a<=1`. The conversion from `m` to `N` has the same uniform property because `m<=5N/2` and `N>=2`. Finally `cos(pi alpha)>=1-2alpha` by concavity. These steps introduce no unrecorded dependence on `alpha`, so the full first bound, including its logarithmic small-parameter behavior, follows.

## 5. Sector comparison and local regularization

For the step function used in the candidate, direct expansion of the Herglotz kernel gives

\[
G(z)-G(0)=\sum_j s_j\int_{\text{cell }j}
\frac{ze^{-i\theta}}{1-ze^{-i\theta}}\,d\theta,
\qquad G(0)=\vartheta\in\mathbb R.
\]

The derivative of `log(1-z exp(-i theta))` with respect to `theta` is `i f_z(theta)`. Therefore the linearized product has the sign `i(G-G(0))` used in the manuscript. This checks the potentially important orientation `|R|` comparable to `|B|`, rather than to its reciprocal.

The Taylor and quadrature errors are bounded by a constant times `h^2` times the sum of the cell suprema of `|f'_z|`. At the chosen height, these suprema have sum at most

\[
C\bigl(t_0^{-2}+(ht_0)^{-1}\bigr).
\]

Multiplication by `h^2` is bounded because `h/t_0=2pi`. The shift coefficients and their squares are at most absolute constants. This proves the product comparison without any differentiability assumption on the step function.

Differentiating the Herglotz kernel and integrating its magnitude gives `|partial_x G| <= C alpha/t_0`; restricting the boundary function to an arc preserves this estimate. Thus both a weight and its reciprocal vary by only absolute factors on any fixed number of adjacent cells.

The explicit analytic logarithm of `B` is `iG`. Its imaginary part lies in `[-pi alpha,pi alpha]`. Consequently the functions with logarithms `+iG/(2alpha)` and `-iG/(2alpha)` both have nonnegative real part. This remains true when the boundary function is localized to an arc. There is no branch-choice ambiguity, nor a strict-positivity assumption that excludes constant extreme boundary data.

## 6. Weak-type localization and the sharp second moments

For an analytic function with nonnegative real part and smooth boundary values, write its real boundary part as `u`. Its integral is the appropriate absolute measure factor times `Re f(0)`, and its imaginary part is the periodic Hilbert transform of `u` plus `Im f(0)`. Markov's inequality, the verified weak `(1,1)` theorem, and a separate bound for this constant imaginary part give

\[
|\{|f|>v\}|\le C|f(0)|/v.
\]

The constant imaginary part cannot be discarded: for a purely imaginary constant the real-part mass is zero. The candidate correctly includes it. The same estimate after a disk automorphism is a harmonic-measure estimate based at the image of zero.

For a small interval of `q` cells with angular length `ell=qh`, the local arc of length `8ell` leaves an absolute multiple of `ell` between the selected cells and the far support. The derivative of the far kernel is integrable there with bound `C/ell`, so its variation across the interval and its neighboring cells is at most `C alpha`. This gives one positive scale `b_I` that simultaneously normalizes the weights and their reciprocals.

At height `ell`, the local Herglotz integral is bounded by `C alpha`, since its support has length `8ell` and the kernel magnitude is at most `C/ell`. Dividing the exponent by `2alpha` therefore leaves an absolute bound for both local sector functions at the chosen base point.

The automorphism is applied to the radially regularized functions. These are analytic in a neighborhood of the closed disk, and that remains so after the automorphism: its pole is outside the closed disk and the extra radial factor places its image strictly inside the domain of the unregularized function. The base point before regularization has radius `exp(-(ell-t_0))`, which is legitimate because `ell>=2pi t_0`. Its harmonic-measure density on all the selected cells is at least `c/ell`.

It follows that the local reciprocal and nonreciprocal level sets have measure at most `C ell v^{-p}`, where `p=1/(2alpha)` lies strictly between one and two. Cellwise comparability turns this into the discrete count `Cq v^{-p}`, with no factor depending on the number of cells. The constants from raising fixed comparison factors to `p` remain bounded because `1<p<2`.

The exact pointwise exponent is also retained. The imaginary Herglotz kernel is `sin u/(cosh t_0-cos u)`; its absolute integral over a symmetric interval of radius `O(ell)` is twice a logarithmic endpoint difference. Including the factor `alpha/2` from the integral definition yields

\[
|\operatorname{Im}G_{\rm loc}|\le
2\alpha\log(\ell/t_0)+C\alpha.
\]

Since `ell/t_0=2pi q`, both local weights have cutoff `Cq^{2alpha}`. Integration of the level counts therefore gives

\[
q+ Cq\int_1^{Cq^{2\alpha}} v^{1-p}\,dv
\le C_\alpha q^{1+2\alpha(2-p)}
=C_\alpha q^{4\alpha}.
\]

The strict hypothesis `alpha>1/4` is exactly what makes `2-p` positive. For larger arcs the whole-circle version has base modulus one because `G(0)` is real, and its cutoff is `Cm^{2alpha}`. The condition `qh>1/100` implies `m<=200pi q`, so the global estimate converts to the asserted local one. Restoring the single scale `b_I` proves both inequalities in Lemma 4 simultaneously.

## 7. Fourier orientation, block normalization, and summation

With the candidate's convention, ordinary Fourier coefficients `c` produce sample data `y=sqrt(m) F c`. Their values on the equispaced grid are `sqrt(m) F_0 c`. Hence

\[
E=F_0F^{-1}
\]

with no adjoint, transposition, or additional normalization factor. The equispaced `F_0` is unitary by the finite geometric-series identity. Thus `||E||_2=||F^{-1}||_2` exactly.

In the Poisson representation, the summand based at the same node gives `beta_j <= C m^{-1}|R(rz_j)|^{-1}`. Its sign is positive, so omitting the other terms is valid. The residue formula, product comparison, and adjacent-cell comparison yield the reciprocal-derivative bound. The radial cardinal estimate then gives equation (33). Its denominator is valid for `d=0` because of the radial displacement, and for `d>=1` because the circular angular separation is at least `(d-alpha)h >= dh/2`.

At each scale one may concretely take consecutive blocks of length `R` except for one final shorter block. This is the partition implicit in the manuscript's bounded-interaction statement; taking arbitrary tiny blocks would not give that property. The specified partition has only an absolute number of interacting blocks in each block row and column. Every interacting pair is contained in one circular interval of at most `CR` indices, or in the whole circle when `R` is comparable with `m`.

Entrywise domination by `(C_alpha/R) w_k w_j^{-1}` bounds any masked block norm by the product of the two corresponding Euclidean norms divided by `R`. Applying the two moment estimates to **the same containing interval** is essential: its factors `b_I` and `b_I^{-1}` cancel. This gives a block norm bounded by `C_alpha R^{4alpha-1}`. The scalar row/column bound applied to the matrix of block norms proves the same bound for the entire scale. The near-diagonal range is handled by constant-size blocks.

Finally `4alpha-1` is strictly positive. The dyadic scale sum is therefore bounded by an `alpha`-dependent constant times `m^{4alpha-1}`. It contributes no logarithm in `m`. The comparison `m<=5N/2` gives exactly the second claimed power of `N`. Constants may diverge when `alpha` approaches one quarter or one half; that is permitted for the second assertion and is not transferred to the universal constant in the first assertion.

## 8. Supplementary exact checks and limits

The independent checker runs as follows:

```bash
python3 exact_algebra_check.py --output exact-algebra-output.json
```

It passes 12 grouped checks using only exact arithmetic over the Gaussian rationals. These include a complete polynomial-coefficient verification of the positive-residue partial-fraction identity for an explicit five-node configuration, exact residue magnitudes and total mass, the centered-frequency cardinal inverse and evaluation-matrix orientation, and three rational interior-point Poisson checks. The source and target hashes are included in its output.

This supplement is finite and is expressly not a certificate of the all-grid estimates. The positivity for every admissible grid, radial exponents, weak-type input, localization, uniform constants, and infinite range of dimensions have been audited analytically above. No conclusion is inferred by fitting a numerical growth rate.

The harmless block-partition specification above makes an implicit standard choice explicit; it is not a mathematical change or a missing hypothesis. No other notation or mathematical correction is requested for the frozen proof. Editorial removal of the pending-review notice should retain this report's exact source binding and review limitations.

This report does not independently certify publication priority, a complete current public-network search, novelty of every ingredient, or final PDF conversion and layout. Those are separate checks. The proof does not settle the excluded second-bound endpoint, assert an optimal numerical universal constant, or import the thesis's stronger endpoint or extremizer claims. Those omissions do not narrow the retained canonical target, which asks only the two displayed upper bounds on the stated ranges.

Signed: **Codex agent `/root/prepare_manuscripts`**, 12 September 2026 (UTC).
