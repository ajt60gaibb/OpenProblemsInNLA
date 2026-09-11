# Independent proof review: IE-08

**Verdict: PASS at the level of an independent mathematical manuscript audit.** I found no material gap in the proposed proof of the exact canonical IE-08 target. The proof establishes the requested randomized Schur result, subject to the conventional floating-point kernel results explicitly imported in Lemma 2 and the published Gaussian regularization theorem. It does not merely establish a result for already separated or diagonalizable inputs. This verdict is not a claim of formal verification, external peer acceptance, novelty, or a validated production implementation.

Review date: 11 September 2026. Reviewer: an independent proof-review agent, distinct from the submitting/packaging agent. No manuscript or canonical problem files were edited. No numerical experiment was used as evidence for a universal mathematical claim.

## Reviewed material and identity

- Canonical target: `eigenvalues-and-inverse-problems/IE-08/README.md`, the complete current local formulation.
- Complete original manuscript: `.cache/colbrook-additional-submission/nla_additional_submission/manuscripts/IE-08-proposed-resolution.md`, lines 1–584, including the complete proof and references.
- SHA256 of the full manuscript decoded as UTF-8, with every CRLF normalized to LF, then encoded as UTF-8: `f66e63e417749f4b70776fad119ed05fad49ea12f6cba9cd81b932b1ac388704`.
- Normalized UTF-8 length: 34,778 bytes. The inspected original already uses LF and has no UTF-8 BOM. The hash includes the front matter and all other manuscript content, not a selected excerpt.

All manuscript line locators below refer to that exact original file.

## Exact target comparison

| Canonical requirement | Review finding |
| --- | --- |
| Arbitrary complex input with spectral norm at most one | Met. Regularization is applied to every such input; no input simplicity, gap, or eigenvector conditioning is assumed. |
| Every `0 < delta < 1/2` | Met. The large parameter has logarithm bounded by a universal multiple of `log(n/delta)`. |
| At most `O(n^3 log^c(n/delta))` arithmetic operations | Met by capped levels, capped sign iterations and sampling, and cubic classical kernels. Balanced spectral cuts are unnecessary for this bound. |
| `O(log(n/delta))` mantissa bits | Met by the fixed choice `u <= R^(-2000)` and polynomial bounds for every conditioning and error requirement. |
| Success probability at least 0.99 | Met by the explicit union bound, including small dimensions and finite sampling. |
| Exactly upper triangular stored `T` | Met through structural zero assignment and termination with scalar diagonal blocks. A dummy failure output can be chosen triangular as well. |
| Both required spectral-norm residuals | Met by the final global backward-error identity and the bound for the accumulated stored basis. |
| Usual relative-error arithmetic, sufficient exponent range | Met. Classical QR/solves and finite-bit scalar evaluation suffice; no exact Gaussian, eigenvalue, or matrix-function oracle is used. |

The checked workshop statement is consistent with this target: Problem 3.3 asks for cubic time up to logarithms and logarithmic precision for backward-error diagonalization or Schur form. Its remarks do not themselves supply the end-to-end result. [Primary workshop source](https://arxiv.org/html/2602.05394v3#S3.SS2).

## Detailed mathematical and finite-precision audit

### 1. Classical kernels: Lemma 2, lines 48–81

The multiplication and addition estimates use a very loose polynomial dimension factor. Classical Householder QR supplies a nearby exact unitary factor and a normwise backward error; the rectangular factorization with full completion is a standard extension of the square result. This does not require a well-conditioned full completion: only the thin range estimate later uses a lower singular-value bound.

The inverse estimate is consistent with classical QR and columnwise backward-stable triangular solves. Writing `a = C0 m^6 u`, the displayed residual gives

`||Xhat - Y^(-1)|| <= a ||Y^(-1)|| (1 + ||Y|| ||Xhat||)`.

When `a kappa(Y)` is small, this first bounds `||Xhat||` by a constant multiple of `||Y^(-1)||`; substitution yields the claimed fixed conditioning exponent. Constants can be enlarged once. The identity `||Y|| ||Y^(-1)|| >= 1` absorbs the standalone term. Consequently the manuscript does not inadvertently substitute a nearly matrix-multiplication-time inversion bound with a dimension-dependent conditioning exponent.

I checked Banks et al., Definition 2.8 and the paragraph after Remark 2.9, for the stated QR interface and availability of classical cubic kernels. I separately checked its Theorem 3.6 and proof: the manuscript's equation (17), normalization by `1/sqrt(n)`, and hypotheses agree; the exponential term is a Gaussian norm-tail contribution and can be replaced by a sharper elementary bound. The published probability theorem is used as an imported result, not reproved here. [Banks et al., primary manuscript](https://arxiv.org/pdf/1912.08805).

### 2. Uniform Newton composition: Lemmas 3–5, lines 94–197

The Cayley-transform formula and both scalar orbit bounds are valid, including the initial iterate. Oddness handles the left half-plane. A possible collision of eigenvalues under an iterate is harmless: all exact iterates remain diagonalized by the same original eigenvector matrix, even when their spectra cease to be simple.

The two contours in Lemma 4 enclose every exact orbit spectrum at distance at least `1/(2B)`. Their total perimeter is at most `24B`. The perturbation radius makes the Neumann factor at most two, and homotopy preserves the number of enclosed eigenvalues. No diagonalizability of the perturbed matrices `W_i` is needed.

For every remaining composition, the scalar contour bound is uniform: `|f^r(z)| <= 32 B^3`. The resolvent identity therefore gives a Lipschitz factor at most

`(24/(2 pi)) * 32 * 16 * K^2 B^6 < 4096 K^2 B^6`.

All these rational functions are analytic on the two half-planes and inside the contours. In particular there is no unaccounted pole of a long composition inside a contour.

The nonlinear telescoping identity (8) is exact. Its intermediate terms cancel by composition, not by linearity or commutation. For the induction step, the previously proved bound puts `Y_s` within `rho/(4L)` of `X_s`; applying the one-step member of the uniform bound puts `f(Y_s)` within `rho/4` of `X_(s+1)`. Adding the next local error keeps both arguments of the telescoping term in the required neighborhood. This proves the claimed additive accumulation without multiplying `L` once per step. I found no circular existence argument in this bootstrap.

### 3. Sign accuracy and actual precision: Corollary 6 and lines 509–524

With `2^N >= 16 B K/epsilon`, the transformed scalar satisfies `|w|^(2^N) <= exp(-32K/epsilon)`, which more than suffices for the claimed exact-iteration error. The exact iterates and their inverses have norms at most `KB`. The radius `rho` then bounds the inexact inverses by `2KB` through another Neumann estimate. Thus the classical inverse error and update errors are at most a constant times `m^6 u (KB)^3`.

For the actual calls, the paper's deliberately weakened exponents are compatible:

- `K <= R^3`, `B <= R^11`, `L <= R^73`, and `rho >= R^(-15)`.
- The local arithmetic bound is at most `C0 R^(-1952)`, hence below the stated `R^(-1900)`.
- The reciprocals of the two required local-error thresholds are bounded by `R^164` and `R^376`, as claimed after constants are absorbed.
- The inversion smallness condition is much weaker than these bounds.

Input rounding, scalar shifts, and forming the projector have adequate slack. All iteration counts can use the stated known upper bounds on `K` and `B`; computing eigenvectors to determine those bounds is unnecessary. The iteration count is logarithmic, not polynomial in `B`.

### 4. Perturbation robustness and diagonal-block conditioning: Lemmas 7–8, lines 230–265

After transformation to the original eigenbasis, the perturbation has norm at most `K||F||`. Disjoint Bauer–Fike disks plus homotopy give one simple eigenvalue in each disk. For its normalized eigenvector, the complementary system is invertible because its diagonal separation is at least `g-||E||` and its additional perturbation is at most `||E||`. The bound `2/g` is valid under the stated hypothesis. Stacking the eigenvector corrections gives `||Y|| <= 1/8` and hence the claimed `3K` condition bound.

For an upper block triangular matrix, polynomials preserve diagonal blocks. Compression of a full simple-eigenvalue projector is exactly the corresponding projector of the diagonal block, and compression cannot increase its norm. With unit-norm right eigenvectors, the dual row norm equals the rank-one projector norm. The two Frobenius bounds yield `kappa_V(C) <= mK`. The argument applies to all diagonal blocks, including middle blocks that are not themselves invariant coordinate subspaces of the full matrix.

This is the needed control of recursion: it is reapplied to the full working matrix. No product of dimension losses along a branch is concealed here.

### 5. Finite sampling and regularization: Lemmas 9–10, lines 285–343

The Box–Muller expression has the intended standard complex Gaussian law: the squared modulus is mean-one exponential and the angle is independent uniform. Coupling the dyadic uniforms to continuous uniforms in their cells preserves independent continuous reference variables. Endpoint rejection allows uniformly polynomial derivative bounds. For example, on the retained radial interval a crude derivative bound for `sqrt(-log u)` is a constant times `R^30`, already enough to make a mesh of `R^(-1000)` negligible relative to `R^(-800)`.

The indicated log series, fixed Machin identity, and bounded-argument trigonometric series can be truncated after a universal multiple of `log R` terms. Their terms, range-reduction counts, and absolute-error propagation have polynomial bounds far below the precision reserve. The mesh integers fit within the available mantissa. This is a finite sampler with capped work, rather than the stronger ideal Gaussian sampler sometimes used as an assumption in the literature.

Substituting the proposed `t,r` into (17), the first failure term becomes `576 * 10^(-40) * gamma^8 / n^6`; the second is `9/(10^8 n)`. Both are below the stated budget. For `n >= 5`, `2 exp(-2n) < 10^(-4)`. For `n = 2,3,4`, Markov's inequality applied to the exponential moment at parameter `1/2` gives exactly the manuscript's `exp(-8n) 2^(n^2)` bound, whose largest value in that set is below `2 * 10^(-6)`.

The explicit definition of `R` dominates both `100t` and `100/r`. A perturbation of norm `R^(-500)` satisfies Lemma 7 by a wide margin, preserves a gap above `1/R` and condition number below `R`, and leaves the initial backward perturbation below `delta/3`. The case `n=1` is separately handled.

### 6. One grid and nonorthogonal range extraction: lines 347–434

The grid spacing is `1/(128R)`, with every coarser bisection line in the finest shifted grid. Counting offsets modulo one grid spacing gives the displayed bad fraction. Union over both coordinates and all eigenvalues gives `512 R^(-8) + 4 R^(-19)`. The grid is selected independently of the regularized matrix; no spectral oracle is needed to select a successful grid.

Lemma 12 correctly covers nonorthogonal idempotents. In orthogonal range coordinates, their nonzero singular values are those of `[I F]`, all at least one. Rotational invariance of the Gaussian gives the square Gaussian reduction. The column-distance argument and a union bound give `r^2 t^2`; the other columns have codimension one almost surely.

On the good event, `||Omega|| <= R^2`. The projector approximation contributes at most `R^(-298)` to its product; sampling, multiplication and QR errors are smaller. Dividing the generous total `R^(-297)` by the retained singular-value lower bound `R^(-20)` gives ample room for the angle allowance. A direct unitary rotation of the nearby subspaces supplies the full frame `Z0` close to `Z`; consequently the lower-left residual is below `R^(-260)`.

The rank determined from the real trace is correct despite possible large norms of individual projector entries: its exact trace is an integer, `|tr(Ptilde-P)| <= m tau`, and the summation error is polynomial times `u`. Fresh range-sampling randomness is independent of each current block. For the probability argument, apply the conditional Gaussian bound before conditioning on the current sampler's success, then union-bound the sampler failure separately. This avoids any erroneous assumption that a truncated sample remains Gaussian.

### 7. Recursive global error and spectral labels: lines 438–505

Let `W_(ell+1) = W_ell Z_(ell+1)`. Conjugating the level update yields a new full perturbation

`F_(ell+1) = F_ell + W_(ell+1) E_(ell+1) W_(ell+1)^*`.

Exact unitarity of `W_(ell+1)` is precisely what makes this an additive error estimate. The stored bases need only be close to these unitary analysis factors.

The deliberate new lower-left deletions occupy disjoint parent diagonal blocks, so their direct-sum norm is their maximum. Stored-basis errors and matrix multiplication errors are far smaller. Resetting old structural zeros is also harmless: even the crude bound of `n` times the norm of the rounding error for an arbitrary entry mask fits in the reserve. Thus (30) and (27) are justified.

The global perturbation stays below `R^(-100)`. Lemma 7 gives global simplicity, condition number at most `3R`, and eigenvalue displacement at most `R^(-99)`; the latter is much less than the fixed grid margin. Lemma 8 then bounds every current block's condition number as required for its next sign call. This proves the assumptions before using them in each level's subspace computation.

The label argument supplies more than a global multiset perturbation bound. Each exact child of the invariant transformation has the correct side's spectrum and condition number at most `R^4`. Its actual child perturbation has norm at most `R^(-260)`, so each actual eigenvalue is matched within `R^(-256)` to an eigenvalue of that particular exact child. The parent gap and grid margin exclude cross-label or cross-cut changes. Combining this local match with the unique global match gives the original eigenvalue's correct cell. Trivial splits and retained scalar blocks preserve the same labels; any rounding from identity transformations is much smaller than the same separation budget.

Every remaining nonscalar block has undergone all `H` coordinate cuts. Its cell diameter is less than `1/(2R)`, whereas the original eigenvalues have gap at least `1/R`. The label invariant therefore rules out a nonscalar final block. Allowing already scalar blocks to stop following the grid does not affect this conclusion.

### 8. Worst-case work, success and final output: lines 455, 532–571

At each level the positive block orders sum to `n`, so their cubes sum to at most `n^3`, irrespective of balance. There are `O(log R)` levels, and each sign call takes `O(m^3 log R)` work. Full transformations are cubic per level. Finite sampling adds only cubic work up to a universal logarithmic factor. Bit generation can be done a bit at a time within its stated logarithmic scalar cost. Invalid ranks, zero pivots or threshold violations can terminate with a fixed dummy output; no repeat-until-success loop is required.

The rank-extraction failure bound can be union-bounded over the capped possible calls, conditional on each past history. The number of potential Gaussian entries is below `R^3`. The total displayed failure probability is less than 0.01 even with the noted double-counting of sampler failure.

The accumulated basis error obeys the stated near-unitary recurrence after constants are enlarged, and `O(log R)` levels give a bound much smaller than `R^(-1000)`. Finally, `||T|| <= 3`, the exact global relation `WTW* = M0 + F`, and `||Q-W|| <= R^(-1000)` give both required residuals. Since `delta >= 1/R`, the final inverse-power remainders are negligible even for arbitrarily small requested delta. These are bounds on the stored outputs interpreted as matrices, as required by the canonical formulation.

## Nonblocking presentation issues

1. **Lines 455 and 528: spell out abort thresholds in a future implementation specification.** The existence proof has enough information to choose polynomial caps, but the sentence calling the thresholds “explicit” is stronger than the presentation: their values and check locations are not listed. This does not require an unknown spectral test. For example, the proved bounds give inverse/output norm caps for the sign kernel, and triangular solves can check zero or suitably tiny pivots. Capped classical kernels already have deterministic operation counts. No new precision theorem is needed to make these choices concrete.
2. **Lines 434 and 532: make the probability filtration explicit.** Independence applies to a fresh continuous reference Gaussian conditional on the past, not after conditioning on its own endpoint-retention event. The proof's separate sampler union bound supports the valid interpretation described above; one sentence would prevent an avoidable ambiguity.
3. **Line 343: correct the section reference.** The linked arXiv version has sections 3.1 and 3.2 followed by section 4; the reference to finite-precision regularization in “section 3.3” is inaccurate. The main dependency is accurately located at Theorem 3.6, so this bibliographic error does not affect the proof.

None of these is a material obstruction to the stated theorem. I did not find an inequality reversal, missing conditioning factor with a nonconstant exponent, unsupported recursion assumption, or probabilistic step that restricts the result to a weaker target.

## Scope and verification limitations

The reviewed proof supports the full canonical randomized backward Schur theorem, including unrestricted inputs, cubic arithmetic work up to a universal logarithmic factor, logarithmic mantissa precision, and simultaneous residuals with success probability above 0.99. The analytic sign subroutine alone has diagonalizability and conditioning assumptions, but the regularization and global induction discharge them for the full algorithm; they are not added input hypotheses.

This review checked mathematical derivations, the stated exponent reserves, dependency interfaces, and the cited primary regularization theorem. It did not reprove every standard Householder/triangular-solve theorem from elementary floating-point operations, formally verify a proof in a proof assistant, implement the enormous-constant algorithm, validate an ordinary-precision diagnostic as that algorithm, or establish novelty against all literature. Expert review remains appropriate for a claimed solution to an open problem. A manuscript-audit PASS must therefore not be represented as formal certification or independent community acceptance.
