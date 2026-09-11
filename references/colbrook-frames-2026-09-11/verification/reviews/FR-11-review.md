# FR-11 independent mathematical review

Reviewer: independent agent `/root/review_transfer_counterexamples`, 2026-09-11.

**Mathematical verdict: PASS for the twelve-measurement construction, its stated quantitative stability, exact decoder, and global-minimizer noise bounds. Scope: PARTIAL progress on canonical FR-11.** The manuscript proves `m_R(7)<=12`; it supplies neither optimality in dimension seven nor exact thresholds for both fields in every dimension. A numerical scaling defect in the original floating-point decoder was independently reproduced and repaired in the separately preserved reviewed decoder; the exact-arithmetic theorems are unaffected.

## Reviewed material and source identity

Read the complete original `.cache/colbrook-frames-submission/frames_submission/manuscript/twelve_measurements.tex`, including its local preamble, every proof and limitation; the full canonical `frames-and-matrix-designs/FR-11/README.md`; `verification/verify_r7.py`; `verification/decode_r7.py`; the matrix JSON; and supplied verification and decoder-result JSON files. No manuscript or canonical file was edited.

SHA-256 of the **complete** original UTF-8 source after CRLF-to-LF normalization, with no trimming of whitespace or final newlines:

`6feb8ce53691a946250fe13ce786d31df25d328090576c5f2091e1c1945ccdb0`

Normalized length: **20496 bytes**. There is no external preamble dependency.

The original and separately corrected decoder have the following full UTF-8/LF identities under the same no-trimming hash convention:

| Decoder | Normalized bytes | SHA-256 |
| --- | ---: | --- |
| Original archive `verification/decode_r7.py` | 7031 | `cde50e683e6ae81aa68ccf7dfa0963086e9500b38d9df00b42807afd71ca7f77` |
| Reviewed `references/colbrook-frames-2026-09-11/verification/decode_r7.py` | 8086 | `bc877874ccc121570943fe90964864ae972783b0d82ecc44099512f93c5b56e2` |

## Exact target and primary references

Canonical FR-11 permits arbitrary self-adjoint matrices, including indefinite matrices of arbitrary rank; recovery is for every vector, without knowing its norm and with the zero vector included. In the real field its ambiguity is exactly a global sign. The manuscript's twelve real symmetric matrices on `R^7` therefore fit this model exactly. The six complex-valued formulas are a convenient encoding of **twelve real** quadratic measurements, not six measurements in the complex-field version of the problem. No rank-one-frame assumption is made.

I checked [Wang–Xu, *Generalized phase retrieval*](https://arxiv.org/html/1605.08034), Definition 1.1, Theorem 2.1, and Theorem 5.1. Its real bilinear characterization and odd/even general upper bounds agree with the comparison made in the manuscript. I also checked [Xu's v2 survey PDF](https://arxiv.org/pdf/2506.17572v2), Theorem 4.3 and Problems 4.1 and 4.3: the latter questions ask for exact thresholds across all dimensions. These confirm the distinction between this explicit upper bound and the full canonical target.

[Harrison's primary preprint](https://arxiv.org/html/1907.11312), the discussion around Proposition 1.13 and Corollary 1.14, supplies the stated surrounding connection to symmetric nonsingular bilinear maps and polynomial multiplication. No theorem from the historical James article is needed by the new proof. Its DOI could not be retrieved in this audit; as the manuscript itself discloses, full historical coverage and priority are not established. I do not infer a sharp dimension-seven lower bound from a remembered projective-space embedding table.

## Construction and nonsingularity

### Coordinate realization and quotient — §2, lines 59–90

PASS. The three complex coefficients `a_0,a_1,a_3` supply six independent real coordinates. Substitution into `L_0=a_2+a_1/12+a_0/5` gives `(9-2i)x_6`, and multiplication by `c=9+2i` gives `85x_6`. Conversely, the condition `Im(c L_0)=0` says that `L_0` is a real multiple of `9-2i`, so exactly one more real coordinate remains. This proves the claimed real-linear bijection onto the seven-dimensional hyperplane; multiplication by complex scalars is not incorrectly assumed to preserve that hyperplane.

Expanding the kernel polynomial gives coefficients `p_6=t`, `p_5=-bt`, `p_2=conj(t)`, `p_1=-b conj(t)`, and zero in degrees 0, 3 and 4. The map `R` annihilates these coefficients. Conversely, `R(p)=0` forces precisely this form with `t=p_6`. Its kernel has real dimension two. Surjectivity is also immediate by setting `p_6=0` and choosing the other six complex coefficients arbitrarily. The conjugations make `R` real-linear, which is exactly what is needed; complex linearity is never required.

Ordinary polynomial multiplication followed by `R` gives a symmetric **real** bilinear map on `H`. The displayed quadratic formulas are its diagonal values. The real and imaginary coordinate convention preserves the Euclidean norm of the complex output, so there is no missing factor of two or square root of two later.

### Bilinear implication — `lem:bilinear`, line 92

PASS. Equal measurements yield `R((f_x-f_y)(f_x+f_y))=0`. Both factors lie in the real subspace `H`. Nonsingularity gives one factor zero; injectivity of the coordinate map gives `x=±y`. This includes `x=0` or `y=0`. The argument uses the exact identity without a polarization normalization factor.

### Ten factor partitions — `lem:factor`, line 103

PASS. For `|t|=1`, all six roots are distinct: two are 0 and `b=5/12`, and four form a rotated unit square. The four unit roots solve `z^4=-conj(t)/t` and can be written as stated. Their squares multiplied by `t` are `±i`.

Every monic cubic factorization of the degree-six squarefree polynomial corresponds to one of the ten unordered splits of six roots into two triples. There are exactly four splits keeping 0 and `b` together and six separating them. Of the six separated splits, four choose an adjacent unit-root pair for the factor containing 0 and two choose an opposite pair. Labeling that factor by its root 0 removes any accidental double-counting. There are no repeated-root or lower-degree factorizations to omit here.

In the first case, dividing the four-root factor by `z-gamma` gives the displayed monic cubic `z^3+gamma z^2+gamma^2 z+gamma^3`. Substitution in `L_0` gives both stated remainder expressions. The product error is bounded by `|r_F|+|r_G|+|r_F r_G|`, producing `D_A=7453/8640`. Since `c^2=77+36i` and `|c^2|=85`, the main term has imaginary magnitude 77 and the total error in that imaginary part is at most `85D_A`. The resulting lower bound is exactly `6355/1728>385/144`.

In the separated case, I expanded `(z-b)(z^2+s z+p')` independently. The `p'` contributions in `f_2+epsilon b f_1+epsilon f_0` cancel exactly, leaving `(1-epsilon b^2)s-b`. This cancellation is important and valid. For adjacent roots, `|s|=sqrt(2)` and `t s^2=±2`. The error estimate used is

`|s| (epsilon b+b+|s| epsilon b^2) + epsilon b(b+|s| epsilon b^2)`.

Replacing `sqrt(2)` by the strict rational upper bound `99/70` gives `D_B=230141/282240`. The main imaginary magnitude is 72, yielding `151859/56448>385/144`. For opposite roots, `s=0`, and the exact product gives imaginary magnitude `77 epsilon b^2=385/144`. These prove a uniform bound for every angle and every partition, not merely for a finite sample.

### Nonsingularity and matrix claims — `prop:ns`, line 181; `thm:main`, line 35

PASS. A zero bilinear output means `fg=P_t`. For nonzero factors, the integral-domain property excludes `t=0`. Dividing one factor by the positive real scalar `|t|` preserves `H` and changes the product to `P_(t/|t|)`, so unit modulus is legitimate. Degree additivity forces both factors to be cubics. Their leading coefficients have product `t`; writing monic factors `F,G` then gives `L(f)L(g)=tL(F)L(G)`. The left side is real because both factors belong to `H`; the uniform bound makes the right side nonreal. This contradiction proves nonsingularity for all nonzero factors.

I independently reconstructed the twelve matrices by Gaussian-rational arithmetic: evaluate each quadratic on the seven standard basis vectors, and obtain each off-diagonal entry from `(Q(e_i+e_j)-Q(e_i)-Q(e_j))/2`. This method did not import the supplied symbolic/Hessian generator. All twelve seven-by-seven matrices matched the supplied JSON entry for entry; every entry is an integer, each matrix is symmetric, and the maximum absolute entry is exactly **144**.

## Quantitative stability

### Product lower bound — `lem:mahler`, line 199

PASS. For actual degree `r<=3`, each coefficient is bounded by its binomial coefficient times Mahler measure. Summing the squared binomial coefficients gives `binom(2r,r)<=20`. This covers constants and lower-degree polynomials without depending on an ambiguous padding convention. Multiplicativity of Mahler measure and its upper bound by the coefficient Euclidean norm give `||fg||>=||f|| ||g||/20`. The latter upper bound follows from the unit-circle logarithmic mean formula, Jensen's inequality, and Parseval; unit-circle zeros are handled by the usual integrable logarithmic limit. Zero factors satisfy the inequality directly.

### Uniform lower output bound — `lem:coefstable`, line 210

PASS. The proof explicitly resolves the leading-coefficient normalization issue rather than mistaking the monic factor margin for the Euclidean condition number.

1. Positive real scaling reduces to unit coefficient norms. With `t=p_6`, the error `E=p-P_t` has degree at most five and its six complex coefficients are exactly `R(p)` in the stated order. Hence `||E||=u` exactly.
2. If `u<=10^-7`, the product lower bound and `||P_t||=sqrt(2(1+b^2))|t|<2|t|` imply `|t|>(1/20-u)/2>1/80`. In particular `t` cannot vanish, so the product and both factors have their full degrees.
3. The radius `rho=100u/|t|` is positive after excluding `u=0` by nonsingularity, and is less than `8000u<=0.0008<0.01`. Root disks are disjoint: the minimum separation among the kernel roots is at least `b`, and `2rho<b`.
4. On each circle, the product of the other five root distances is bounded below by `(b-0.01)(1-b-0.01)^4`. For the centers 0 or `b`, this follows directly from the fixed-root distance and four unit-root distances. For a rotating-root center, one distance can be bounded by `b-0.01` and all the other four by `1-b-0.01`; the actual unit-root pair distances are larger. Thus the same conservative bound applies to **every** circle.
5. Independent rational calculation gives `(b-0.01)(1-b-0.01)^4=208546861/4746093750>1/25`, so `|P_t|>4u`. Cauchy–Schwarz on the six coefficients, together with `|z|<=1.01`, gives `|E(z)|<=sqrt(6)(1.01)^5u<3u`. Rouché therefore places exactly one root, counting multiplicity, of `p` in each disk. This simultaneously proves simplicity and accounts for all six roots.
6. The roots of each monic factor can then be paired to three distinct kernel roots with displacement below `rho`. Expanding elementary symmetric functions gives coefficient changes `3rho`, `6rho+3rho^2`, and `3rho+3rho^2+rho^3`. Substituting the weights in `L` bounds its change by `10(4.1+0.85rho+0.2rho^2)rho<42rho`.
7. The undeformed factor values obey `|L(F)|,|L(G)|<35`; the product perturbation is less than `2940rho+1764rho^2<3000rho`. Since `tL(f_0)L(g_0)` is real, so is its division by `|t|`. Applying the factor margin at `t/|t|` is valid because `P_t/t` is unchanged by this normalization. The contradiction is `385/144<3000rho<=12/5`, with a strict numerical gap.

Every rational inequality and constant in these steps was independently recomputed with `fractions.Fraction`. The resulting coefficient-norm lower bound `10^-7` is conservative but justified globally.

### Signal coordinates and matrix perturbations — `thm:stable`, line 262; following corollary

PASS. The coordinate inverse formula is exact, including `x_6=Re L_0/9`. Bounding the first three coefficient contributions by `||f_x||^2/25` and the last by Cauchy–Schwarz gives the displayed factor `15433/291600<1/16`. Thus `||f_x||>4||x||` for nonzero signals, and the stronger bilinear constant is `16*10^-7`, which safely implies the stated `10^-6`.

Applying the bilinear estimate to `x-y,x+y` gives the first difference inequality. The parallelogram law makes the larger of these two norms at least `sqrt(||x||^2+||y||^2)`, proving the second, including coincident and opposite vectors. Symmetric measurement perturbations change the output by at most the combined operator norm times `||x|| ||y||`; the strict perturbation threshold therefore leaves a positive nonsingularity margin. No compactness-only argument is substituted for the explicit constant.

## Exact decoder and noisy variational solution

### Quartic and exceptional branches — `prop:decoder`, line 305

PASS as an exact-arithmetic statement for data in the image. If `q_1!=0`, fixing either square root `a_0` selects one of the two global signs. The first three recursive equations force the coefficients `A_1,A_2,A_3`, of degrees one, two and three in `u`. Their leading coefficients are respectively `-b/(2a_0)`, `-b^2/(8a_0^3)`, and `-b^3/(16a_0^5)`. Thus the coefficient of `u^4` in `Phi` is exactly `5b^4/(64a_0^6)`, nonzero. There are at most four distinct candidates even if the quartic has repeated roots.

The consistency checks recover the conjugate relation, the unused sixth measurement, and the hyperplane constraint. All other equations have already been enforced by construction or the quartic. The actual signal up to the chosen sign passes the checks. Nonsingularity proves uniqueness after fixing the nonzero `a_0`; no unproved selection criterion is used.

When `q_1=0`, necessarily `a_0=0`. Nonzero `q_2` forces nonzero `a_3`, making both divisions legal; its two square roots produce globally opposite coefficients. If also `q_2=0`, then `a_3=0`; nonzero `q_3` allows the stated square root for `a_1` and division to obtain `a_2`. If the first three data vanish, only `a_2` remains and its square determines it up to sign, including zero. These exhaust the exceptional branches. For data known to lie in the image, unused equations and the hyperplane condition follow from the actual compatible sign choice; for arbitrary data they must be checked, as the manuscript states.

### Noise bound — `cor:noise`, line 348

PASS. The lower quadratic growth bound makes the continuous residual objective coercive on the finite-dimensional real signal space, hence a global minimizer exists. Its residual is at most the noise norm by comparison with the true signal. The measurement discrepancy is consequently at most `2epsilon`. The product of the plus/minus distances is at least their minimum squared, giving the square-root error bound; the additional factor `sqrt(||xhat||^2+||x||^2)>=||x||` gives the second bound for nonzero `x`. This is a statement about a global minimizer, not a guarantee that local least-squares polishing computes it.

## Supplied code, diagnostics, and implementation issue

The supplied symbolic verification script matches the analytic construction and inequalities. Its finite angle grid and local minimizations are explicitly diagnostics; neither a finite positive sample minimum nor a local search value proves global nonsingularity. The matrix-span rank check is also not itself a phase-retrieval certificate. The independent exact matrix reconstruction and rational checks described above supplement, rather than trust, the supplied labels.

The supplied decoder-result JSON records 365 tests covering the quartic branch, all three special branches, zero, and several moderate scales, with no recorded failures. I read this as the record of those finite tests only. The original decoder uses floating roots, projects candidates into real coordinates, optionally polishes them, and evaluates a residual. The theorem already disclaims uniform floating-point accuracy for small `a_0` and arbitrary noisy data.

**Original decoder scaling issue: FAIL for unrestricted finite-input residual safety.** At the start of `decode_r7.py`, `scale=np.linalg.norm(y)` can overflow or underflow even when all entries of `y` are finite and nonzero. For the exact signal `x=s e_6`, only `q_5=(77-36i)s^2` is nonzero. At `s=10^80`, the data are finite but the unscaled Euclidean norm overflows to infinity. Division produces all-zero normalized data, the special branch accepts the zero candidate with reported residual zero, and rescaling by `sqrt(infinity)` produces NaNs. At `s=10^-90`, the norm underflows to zero and the early zero-data branch returns zero for a nonzero signal. I reproduced both failures in the actual original decoder after enabling read access to the installed SciPy dependency files: it returned seven NaNs and seven zeros, respectively, with reported relative residual zero in both cases. The mathematical exact decoder and stability theorems remain valid.

### Authorized reviewed-decoder repair — PASS for the targeted fix

At the parent agent's request, copied the original decoder into the separately preserved reviewed path above and changed only its numerical normalization, final validation, and scale regression tests. The original decoder, manuscript, and canonical statement remain unchanged.

- Normalize first by `max(abs(y))`, which is finite and strictly positive for any finite nonzero input. The zero branch now means actual zero input, rather than a squared norm that underflowed.
- Form the complex normalized data only after dividing the real components; compute their Euclidean norm in this bounded scale. Divide residuals by that norm so the original Euclidean relative-residual convention is preserved.
- After restoring signal scale, explicitly reject nonfinite output and recompute a relative residual from the actual returned vector in normalized coordinates. Quadratic homogeneity permits this check without directly squaring extremely large or small restored coordinates.
- Add generic signal-scale tests through `10^-150` and `10^150`, plus four pure-`a_2` regressions at `10^-150`, `10^-90`, `10^80`, and `10^150`. Compute signal-error diagnostics after max-component normalization as well, so the tests do not hide the same norm overflow/underflow issue.

The corrected decoder returned the expected `e_6`-direction vectors for the two original regressions, with relative measurement residuals approximately `2.51e-16` and `2.07e-16`. It then passed **373** self-tests at seed 1, covering the quartic branch (308), both intermediate exceptional branches (20 each), the pure-`a_2` branch (24), and zero (1). Maximum observed relative signal error was approximately `1.06e-14`, and maximum measurement residual approximately `1.75e-14`. The report is `verification/decoder_extreme_scale_review.json` under this reference record.

These executions used the bundled Python with `PYTHONPATH` pointing to the existing `.cache/colbrook-transfer-submission/python-packages` and approved read access to those dependencies. No dependency download or original-artifact mutation was required. The repaired normalization removes the demonstrated scaling failures; it does not establish a uniform numerical-accuracy theorem for ill-conditioned quartics, extreme relative coordinate disparities, or arbitrary inconsistent/noisy data. Those limitations remain correctly distinct from the exact decoder proposition.

## Status recommendation and exact surviving target

- **Retain canonical FR-11 as Partially resolved.** Add the independently reviewed explicit upper bound `m_R(7)<=12`, along with the integral matrix certificate and precise stability/decoder scope.
- The manuscript does not establish `m_R(7)=12`: it contains no lower bound excluding ten or eleven measurements. Even a separate optimality result in this dimension would not answer the all-dimensions, both-fields canonical question.
- The surviving canonical task is to determine `m_R(d)` and `m_C(d)` exactly in all still-unsettled dimensions. This submission makes no complex-field construction or threshold claim and supplies no general minimum formula.
- A matrix family can be correct and useful without being historically new. The comparison to the generic odd-dimensional bound 13 is valid, but no priority claim or exhaustive specialized-construction search is certified here.
- No mathematical source correction is required by this audit. The original floating-point scaling defect has been documented and repaired in the separately hashed, regression-tested reviewed decoder; its original is retained for provenance.
