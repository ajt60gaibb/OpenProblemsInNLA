# IV-05 independent proof review

Review date: 2026-09-11. Verdict: **PASS — full canonical promised polynomial-bit hull computation.** Recommend **Resolved** for IV-05, with attribution to the submitted manuscript and this independent mathematical audit. No mathematical correction is required. This is a Codex proof audit, not journal peer review or a priority determination.

## Reviewed source identity and scope

The complete original `.cache/colbrook-package-submission/nla_submission/manuscripts/IV-05.tex` and its included `common.tex` were read, including all proofs, complexity statements, limitations, and references. Hash normalization is UTF-8 decoding, replacement of CRLF by LF, and UTF-8 encoding, without trimming or removing the final newline.

| Original source | Normalized bytes | SHA256 |
|---|---:|---|
| `IV-05.tex` | 7724 | `a75952ac1917cd129b6d4f15addbfc0c0db1bb581a20c4718c74a7fb5fb4a694` |
| `common.tex` | 985 | `d8e7a0de2ed1a1fd162b147211fe29c7b1d7bfbc0be7b827dcda4d9a2653d0d4` |

The exact canonical target is `intervals-and-absolute-value-equations/IV-05/README.md`: arbitrary rational independent-entry matrix and right-hand-side intervals, all n >= 1, with the promise that every matrix is inverse-M, and deterministic computation of the exact rational solution-hull endpoints in polynomial binary-input time. The submitted algorithm covers this target using 2n linear programs. Promise recognition is not needed for the result; the accompanying IV-03 theorem can provide it separately.

`common.tex` provides formatting and notation without extra mathematical hypotheses. Shared numbering gives Lemma 1 (`lem:bijective`, line 25), Lemma 2 (`lem:lp`, line 55), and Theorem 3 (`thm:hull`, line 70). The LP is equation `eq:lp`, line 51; complexity and limitations begin at line 96.

## Independent proof checks

### Lemma 1: bijectivity under regularity — PASS

For each coordinate, the secant slope of absolute value lies in [-1,1], including the convention zero when the two coordinates coincide. Consequently the secant matrix is exactly `C-D_sigma R D_d`, and every entry lies in the original interval. Nonsingularity therefore proves injectivity for all x,y, without a differentiability assumption at coordinate hyperplanes.

The regular interval is compact, and its smallest singular value is continuous and positive, so it has a positive minimum alpha. Applying the secant identity with y=0 proves the coercive bound `||H_sigma(x)|| >= alpha ||x||`. This is an existence argument and does not require efficiently computing alpha. Every squared residual consequently attains its minimum.

At a minimizer with nonzero residual r, any convex combination of adjacent selection matrices remains in the interval. Hence zero cannot belong to the convex hull of their transposed products with r: otherwise a nonsingular convex-combination matrix would annihilate r after transposition. The nearest point g to zero in that compact convex hull is nonzero. Its projection inequality gives `g^T J_s^T r >= ||g||²` for every adjacent selection. Along h=-g, the signs of all nonzero coordinates stay fixed for sufficiently small positive t, and the zero coordinates can be assigned a selection consistent with h. If a zero coordinate of h remains zero, either sign gives the same image. Thus the piecewise linear identity along the ray holds, and the squared residual has a strictly negative first-order term. This contradicts minimality and proves surjectivity. The proof is valid at all nondifferentiable points and uses no unjustified smooth inverse theorem.

### Lemma 2: complementarity LP — PASS

Both `P=C-D_sigma R` and `Q=C+D_sigma R` are actual interval members. Their inverses X=Q^{-1} and Y=P^{-1} are nonsingular M-matrices, hence have positive diagonal and nonpositive off-diagonal entries. The positive diagonal follows, for example, from the diagonal-dominance scaling argument in the independently checked IV-03 closure lemma; it also follows directly from the standard M-matrix characterization. No strict off-diagonal sign is needed.

For the unique root x, its positive and negative parts u,v satisfy `Pu-Qv=b`. Thus y=Qv is feasible for the LP. Conversely, any feasible y has v=Xy nonnegative and y=Qv nonnegative because Q is nonnegative. A nonempty objective sublevel set therefore lies in the compact simplex `y>=0, sum(y)<=c`, and is closed. Choosing c at a feasible point proves attainment of an optimum. This handles possibly unbounded feasible regions and does not confuse bounded objective with attainment in a general nonclosed set.

At an optimum, if both u_k and v_k were positive, decreasing y_k by a sufficiently small positive amount decreases those two entries by positive diagonal coefficients but keeps them nonnegative. All other entries of u and v weakly increase because the corresponding off-diagonal inverse coefficients are nonpositive. The change is feasible and strictly improves the objective, a contradiction. Therefore u and v are complementary coordinatewise. It follows exactly that `|u-v|=u+v`, and the equality `Pu-Qv=b` becomes `H_sigma(u-v)=b`. Lemma 1 gives uniqueness of the resulting root. The reasoning proves the claim for every optimum, not just for a specially selected optimal basic point.

Although not required by the manuscript, complementarity also implies that any optimal y is uniquely determined by the unique root: u=x^+, v=x^-, y=Qx^-. This is consistent with the exact-rational endpoint claim, including degenerate optima in an LP representation.

### Theorem 3: endpoint domination and attainment — PASS

For a true interval solution z, each row product lies between `C_j z-R_j|z|` and `C_j z+R_j|z|`. If sigma_j=1, the chosen H row is its minimum and the chosen b row is the upper right-hand-side endpoint. If sigma_j=-1, the chosen H row is its maximum and the chosen b row is the lower endpoint. Therefore `w=D_sigma(H_sigma(z)-b_sigma)<=0` with the exact direction used in the manuscript, regardless of the signs of z or the right-hand side.

The secant identity gives `z-x=M^{-1}D_sigma w` for a matrix M in the same interval. With sigma_i=1 and all other signs -1, row i of `M^{-1}D_sigma` is nonnegative: the diagonal stays positive, and all other entries switch from nonpositive to nonnegative. Thus z_i<=x_i. Reversing sigma makes that row nonpositive and yields z_i>=x_i. This checks both endpoint orientations independently; it does not rely on an ambiguous lower/upper convention from a source.

The candidate x is itself attainable. Choose any sign vector agreeing with its nonzero coordinates and form `A*=C-D_sigma R D_s`. Its entries belong to the interval, and `A*x=H_sigma(x)=b_sigma` with b_sigma in the right-hand-side interval. At zero coordinates, either sign works because the column contributes zero to the product. Thus the dominance bounds are exact attained extrema. Different coordinates may use different witnesses, as is appropriate for a coordinatewise hull.

## Boundary cases and exact binary complexity

The arguments cover n=1, zero interval widths, point right-hand-side intervals, a zero right-hand side, mixed-sign right-hand sides, zero coordinates of the roots, zero off-diagonal inverse entries, and reducible inverse-M matrices. The input endpoint inequalities guarantee nonempty compact intervals. The regularity promise makes the inverse continuous on the compact matrix interval, so the full solution set is nonempty and compact. No componentwise nonnegativity of b is assumed.

There are precisely 2n LP instances with n free variables and 2n displayed inequalities each. Their P,Q coefficients are formed from rational endpoints using polynomially many arithmetic operations. Exact inverses have polynomial binary length: clear denominators with at most the total input denominator length, and use the adjugate formula and determinant bounds. Products with b and the postprocessing `u-v` retain polynomial size. Standard deterministic rational linear programming returns an exact optimal rational point in polynomial input time. Free variables can be split into positive and negative parts with only a linear-size increase; alternatively, y>=0 is already implied by feasibility here.

The exact output length is also independently transparent: for the root's sign vector s, `x=(C-D_sigma R D_s)^{-1} b_sigma`. This is a nonsingular rational linear system of polynomial coefficient length, so each coordinate has polynomial binary length by the same determinant argument. The proof requires ordinary polynomial bit complexity, not a strongly polynomial algorithm or a uniform condition-number bound. Even extremely ill-conditioned rational promised inputs are covered by the bit model.

The theorem is an algorithmic existence result using a standard exact rational LP subroutine. It does not require that the attached numerical implementation itself be such a subroutine. The manuscript correctly states that the complementarity argument uses inverse-M signs; regularity alone does not provide them. No resolution of the general AV-03 search question follows from this result.

## Code inspection and primary-source comparison

The relevant portions of `code/nla_algorithms.py` and `code/verify_exact.py` were read in full. `inverse_m_ave_float` uses the correct matrices and inequality signs. Its explicit bound y>=0 is mathematically redundant under the promise. It is nevertheless a floating-point SciPy/HiGHS implementation and supplies neither exact rational output nor a polynomial-bit implementation certificate.

The exact verification script obtains roots by enumerating sign vectors and checks exact primal and dual LP certificates with rational arithmetic. Its dual equations and objective equality correctly certify optimality for the finite checked instances. It compares coordinate endpoints with all entry vertices using the selected right-hand-side vertex. The enumeration is exponential and is supplementary validation, not the polynomial algorithm asserted in the theorem. In higher dimensions, testing all entry vertices alone should not be described as an independent proof of the inverse-M promise for every interior point. This review establishes the mathematical statements directly; parent-task execution logs document supplied-program reruns separately.

Hladík's [author preprint, §9, p. 11, question before Theorem 25 and Theorem 25](https://arxiv.org/pdf/1711.08732) asks about efficient interval-system solution and fixes the right-hand-side vertices attaining each endpoint. It does not give the missing optimization over matrices. The submitted LP argument supplies that step. The neighboring inverse-matrix hull formula is a different problem. Karmarkar's [original Combinatorica article, publisher abstract and bibliographic record](https://link.springer.com/article/10.1007/BF02579150) supports the polynomial-bit LP ingredient. Its role is the standard rational LP theorem, not a new claim about strong polynomiality.

**Final disposition: PASS for the entire submitted IV-05 manuscript and the full canonical promised exact hull computation. Recommend Resolved. No part of IV-05 remains unaddressed; general regular absolute value equations remain outside its scope.** The review does not certify publication priority or perform an exhaustive later-literature search.
