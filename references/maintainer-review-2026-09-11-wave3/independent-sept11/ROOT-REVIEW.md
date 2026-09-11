# Independent adversarial review of PRs 93 and 103

Review date: 11 September 2026.

This review examined the submitted proofs independently of their supplied PASS
reports. It supplements the separate maintainer task's document and integration
review. No blocking mathematical error was found in either proof at the commits
below. This is mathematical review by AI agents, not proof-assistant
certification, human peer review, or a determination of novelty.

| Pull request | Reviewed commit | Original target | Root verdict |
| --- | --- | --- | --- |
| [93](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/93) | `c797aee814c8bebe4452329c93f5d84fd9c41f1f` | RA-12: the complete relative Gaussian trace-tail comparison | The argument supports the full stated threshold, including equality. |
| [103](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/103) | `6f5861fa392db467dc23abd096a02a08573146b8` | RA-10: a universal nuclear-error transfer constant without ordering | The argument supports the universal constant 11 under the original hypotheses. |

The complete original target sections were compared directly with published
commit `aaa88c40fbf58e8cebc335021b3c5cd108c357e4`. Both are unchanged. The ID
registries are identical to that base: all 203 published ID/path pairs remain
unchanged. The reviewed snapshot README and solution Markdown were also compared
directly with their corresponding Git objects. No indexes were regenerated and
no submission, shared checkout, workflow or remote branch was modified by this
independent pass.

## PR 93: Gamma-tail quantifiers and the key transfer

The proof was read in `randomized-and-low-rank-approximation/RA-12/solution.md`.

1. **Mode lemma, lines 51–113.** The Laplace-transform derivative gives
   `x f(x) = (k*f)(x)`, with `k(t) = sum r_i exp(-t/w_i)`. Differentiating the
   smooth kernel, rather than requiring a bounded density derivative at zero,
   gives the stated derivative identity. At a global mode `z`, the two identities
   imply `M-z = integral k v` and `1 = integral (-k') v`, where
   `v(t)=1-f(z-t)/f(z)` lies in `[0,1]`. The pointwise bounds
   `w_min(-k') <= k <= w_max(-k')` therefore give exactly the claimed mode
   interval. Total shape greater than one puts the global mode strictly inside
   the positive half-line. No disputed auxiliary mode bound is used.
2. **Transfer, lines 148–197.** Choosing the smallest positive fractional
   coefficient as the decreasing coordinate is essential. It remains a minimum
   positive scale throughout that transfer. For the twice-augmented convolution,
   the preceding lemma bounds the mode between `rho-1` and `rho+1`.
   Independently differentiating the two changing factors of the Laplace
   transform gives `alpha (a-b) g'(x)` for the CDF derivative, with the sign in
   the manuscript. Thus the lower CDF increases and the upper survival
   probability increases toward the extreme coefficient vector in the stated
   regions. Every completed transfer removes a fractional coordinate, so the
   path is finite. This does not assert monotonicity along arbitrary
   majorization paths.
3. **External input.** [Roosta-Khorasani and Székely, Appendix A, Theorem 4](https://arxiv.org/html/1601.04731v1#A1)
   explicitly gives unimodality for independent Gamma variables with arbitrary
   positive shapes and rates. Its scope covers both the augmented variables
   and the subdivision into shape `alpha/N`; no hidden shape-at-least-one
   assumption is introduced. The coefficient-derivative method is credited to
   [Hallman, Appendix A.1](https://arxiv.org/html/2411.15454v1#A1).
4. **Gamma endpoint, lines 211–228.** Splitting each Gamma variable into `N`
   independent pieces repeats its weight `N` times while dividing its shape by
   `N`; the mean remains `rho`. The extreme law is a Gamma variable with shape
   approaching `rho`, plus a nonnegative remainder whose mean tends to zero.
   Weak convergence therefore transfers both CDF comparisons at every fixed
   endpoint. The limiting shape stays strictly positive. The finite intermediate
   shapes can be less than one, which the preceding lemma permits.
5. **Original quantifiers, lines 232–264.** Gaussian diagonalization gives the
   normalization `T_m(A)/tr(A) =_d Q_w/rho` with `alpha=m/2` and
   `rho=m*mu/2`. The stated threshold is exactly `rho*epsilon >= 1`.
   Noninteger effective ranks, `m=1`, zero eigenvalues and the possible extra
   zero coordinate of `B_mu` cause no problem. All nonzero weighted Gamma laws
   have no atoms, including at zero, so equality at the threshold and the
   non-strict tail inequalities are covered. When the lower endpoint is
   nonpositive, that tail is simply zero. The proof establishes sufficiency,
   not optimality, of the threshold.

The target matches [Hallman's Theorem 6 and Conjecture 3](https://arxiv.org/html/2411.15454v1#S5).
The earlier counterexamples to auxiliary mode/inflection assertions do not
contradict this restricted-transfer argument and must retain their original
attribution.

## PR 103: noncommutation, the compression lemma and constant 11

The proof was read in `randomized-and-low-rank-approximation/RA-10/solution.md`.

1. **Lemma 2.** Independently multiplying the resolvent eigenvector equation by
   `sI+A` recovers both block identities (2) and (3). Their scalar consequence
   (4), together with the Schur complement, implies (5). Substitution gives
   `v^T(C-A)v = mu*s + mu*(2-mu)*u^T H u`, as asserted. The difference of the
   scalar terms in (7) is nonnegative for `0<mu<1/2`. Summing over an orthonormal
   positive eigenspace is legitimate: the compressed eigenvectors form a
   subunit frame, and the positive-trace variational principle bounds the other
   sum. The proof never diagonalizes `A` and `PAP` simultaneously. Replacing
   `A,C` by `A+rP,C+rP` keeps their difference fixed and gives the singular
   compression case by continuity.
2. **Sections 3–4.** Pinching and positivity of the complementary block give
   `e0 >= R+L`. Compression min-max bounds give `d <= L`. The restricted
   resolvent estimate in (14) is taken on the selected subspace, where the
   eigenvalues of `B0` are at least `c=a_k`; it does not use the false global
   bound that would result from ignoring the zero complement. The resulting
   estimate is `5*g*e0`. The ordered-eigenvalue nuclear perturbation inequality
   then gives `r <= e(B)` and `e0 <= e(B)+r`, yielding
   `5*g*(e(B)+r)+g*r <= 11*g*e(B)`. Finally `tau_s >= g*tau` has the correct
   direction for converting absolute excess to relative excess.
3. **Full function class.** [Chansangiam, Proposition 1.1, p. 2](https://arxiv.org/pdf/1304.7936v1)
   supplies the positive integral representation without a normalization such
   as `f(1)=1`. The endpoint masses produce the nonnegative constant and linear
   terms. In finite dimension the scalar spectral integrals are finite, so
   integrating the nuclear-norm bound is valid. Realification supplies the
   complex-Hermitian hypothesis of the usual representation from the original
   real-symmetric, all-sizes monotonicity assumption.
4. **Selected zeros and tails.** The proof retains the full rank-`k` selected
   projection even if `B` has smaller rank. Consequently the constant atom
   contributes `f(0)(I-P)`, rather than an incorrect truncation determined only
   by the range of `B`. This also handles repeated eigenvalues and arbitrary
   permitted eigenbasis selections. If the optimal tail vanishes, the input
   hypothesis forces `A=B`; the output tail is then exactly `(n-k)f(0)`.
   No division by zero, positive-definiteness assumption, commutation, Loewner
   ordering, or excluded `epsilon=0` case is hidden in the proof.

The supported conclusion is the original nuclear-norm assertion with `C=11`.
It does not establish sharpness of 11 or an analogous assertion for other norms.
The earlier commuting result and lower bound of two remain separate credited
results. No source or target correction is required by this independent review.

## Integration boundary

These findings concern the mathematical sources at the two recorded commits.
The maintainer task retains responsibility for the current PR heads, rendered
document correspondence, required checks and any publication or merge. A
mathematical verdict here neither approves a workflow nor bypasses a pending
execution-approval requirement.

## Corroborating independent reviews

- [Complete PR 93 audit](PR93-independent.md): analytic proof, primary theorem
  scope, all tail endpoints and Gaussian normalization.
- [Complete PR 103 audit](PR103-independent.md): every proof step and the full
  original function class, including an exact selected-zero example.
- [Separate PR 103 compression audit](PR103-compression-check.md): independent
  block algebra, singular limit and constant accounting, supplemented by
  [independent diagnostic code](pr103_compression_check.py) and its
  [results](PR103-compression-results.json). Numerical diagnostics corroborate
  the analytic reasoning and do not certify the universal theorem.

Both live PR heads were rechecked after the mathematical review and still
matched the commits recorded above.
