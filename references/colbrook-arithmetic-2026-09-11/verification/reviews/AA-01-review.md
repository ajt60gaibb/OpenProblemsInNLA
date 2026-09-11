# Independent proof review: AA-01

Review date: 2026-09-11. Mathematical verdict: **PASS for the exact canonical finite-tree model.** Recommended canonical status: **Solved**, by the signed-gap necessary-and-sufficient criterion and real quantifier elimination. No mathematical repair is required. This review does **not** verify the manuscript's reported experimental runs: the relevant scripts are absent from the received AA01 directory.

## Complete source and scope

I read the complete `.cache/colbrook-arithmetic/NLA_GitHub_submission_bundle/AA01_submission/manuscript.tex`, including all main and auxiliary proofs, examples, model boundaries, reproducibility claims, and references. Its complete UTF-8 text, with CRLF converted to LF and no trimming, has SHA256:

`e34166543fea38668251b2b1307b6b29aac799f218aadd577c0280ed36610491`

There is no shared external TeX proof input. Main locators, using this original source's lines:

| Claim | Source locator |
| --- | --- |
| Signed-gap equivalence, Theorem 1.1 | line 122 |
| Constructive sufficiency and terminating decision | Section 2, line 143 |
| Separated execution, Lemma 3.1 | line 248 |
| Primitive-form preservation, Lemma 3.2 | line 297 |
| Fixed-root replay, Lemma 3.3 | line 326 |
| Necessity and coefficient interpolation, Lemma 4.1 | Section 4, line 411; lemma at 435 |
| Canonical-family and single-tolerance corollaries | lines 473 and 487 |
| Face criterion, Proposition 5.1 | line 518 |
| Existential obstruction test and certificates | line 570 onward |
| Examples | Section 6, line 605 |
| Model limitations and experimental claims | Sections 7–8, lines 676 and 718 |

The actual `arithmetic-and-complexity/AA-01/README.md` was read and compared. Both formulations use exact real inputs, integer-coefficient p with p(0)=0, binary rounded addition/subtraction/multiplication, exact negation and comparisons of available values, finite branching control flow, stored-value reuse, no constant input nodes, and arbitrary separate errors for distinct arithmetic occurrences. Both require a fixed tree to work for every requested relative tolerance, with an error bound uniform over the whole real input space and over the entire error box. Equality at zeros is included. Comparison outcomes supply control flow, not extra numerical constants. Thus the proof does not settle a weakened formula-only, homogeneous, fixed-input, or generic-input variant instead of the canonical question.

The proof assumes n>=1. Its discussion separately handles an encoding with n=0: only the zero polynomial is admissible, and under the literal available-value output convention with no input nodes there is no output-producing tree. That degenerate convention is decidable and does not leave a family of canonical instances untreated.

## Primary-source comparison

Primary sources were accessed on 2026-09-11:

- [Demmel–Dumitriu–Holtz, v2](https://arxiv.org/pdf/math/0508350v2), Sections 2.2–2.7: the bounded-running-time convention, exact comparisons, separately arbitrary occurrence errors, and reuse of stored arithmetic results are explicit. Section 4 identifies the constant-free classical operations. The source also supplies the three-term-addition obstruction and an accurate branching Motzkin construction. These agree with the manuscript's motivating model and example attributions.
- [Demmel–Dumitriu–Holtz–Koev, Acta Numerica survey](https://people.eecs.berkeley.edu/~demmel/Demmel_pubs_07_11_final/B15_ActaNumerica08.pdf), Section 3.3.7: the discussion explains obstacles to completing the dominant-term induction for the real problem. The submission's argument is independently checked here rather than inferred from that earlier partial analysis.
- [Rauh–Kahle–Ay, v2](https://arxiv.org/pdf/0906.5462v2), Section 2, especially Lemma 7 and Proposition 8: the closure/support description for a finite exponential family is compatible with the auxiliary face argument. The manuscript provides its own proof, audited below; this citation is not being treated as an unexplained theorem implying the main accurate-evaluation result.
- Arnon–Collins–McCallum, [journal record](https://epubs.siam.org/doi/10.1137/0213054) and [primary technical-report text](https://www.lacl.fr/pvanier/cours/2015-2016/lm/articles/Cylindrical%20Algebraic%20Decomposition%20I-%20The%20Basic%20Algorithm.pdf), establishes CAD as part of effective real quantifier elimination. The accessible full text is the December 1982 technical report preceding the cited 1984 publication. The proof needs the complete decision procedure for real closed fields, not successful execution of any particular commercial or resource-limited solver.

These are scope and dependency checks, not an exhaustive priority search. No claim of novelty or human authorship is made in this review.

## Constructive sufficiency and algorithmic termination

The signed-gap map is invertible and integral. For any fixed permutation and signs, raw magnitudes are nested prefix sums of nonnegative gaps. These finitely many closed chambers cover all real inputs, including ties and zeros. Comparing x_i with its exact negation decides its sign without a stored zero constant. Sorting available exact magnitudes is a finite exact comparison tree. Subtracting consecutive **original magnitudes** computes each noninitial gap with precisely one relative error; an exactly zero gap remains zero. This correctly avoids an error bound based on subtracting two previously perturbed gap approximations.

Because p(0)=0 and the chart map is linear, every nonzero term of the collected chart polynomial has positive degree. Monomials can therefore be built from available gaps, with no constant one. Integer coefficients can be compiled as finitely many additions; negative signs use exact negation. The zero polynomial can be returned by the allowed operation x_1-x_1.

When this evaluator is symbolically expanded, each signed monomial contribution acquires a product of factors 1+delta, possibly repeating the same factor when a stored value is reused. It is not necessary, and would be incorrect, to assign fresh errors to aliases. Positive integer coefficient construction averages the corresponding positive factor products after normalization by that coefficient. A finite integer R bounds the total number of factors in each contribution. For u<=1/(2R), their deviations from one are bounded by `(1+u)^R-1<=exp(Ru)-1<=2Ru`, which also bounds downward deviation. The final signed additions preserve a contributionwise bound by `2Ru q#`; they do not require every intermediate sum to have one sign.

Consequently `q#<=C|q|` gives the displayed relative bound uniformly on that closed chamber, even at q=0. Taking maxima of C and R over finitely many charts and choosing `u<=eta/(2CR)` also satisfies u<=1/(2R), since C>=1 and eta<1. The evaluator is fixed as eta varies and is exact at zero errors.

The squared formula is equivalent to domination because C>=1 and q# is nonnegative on the quantified orthant. It has integer coefficients and finitely many real quantifiers; no unknown program, real coefficient oracle, transcendental predicate, or unbounded search over trees remains. Complete real quantifier elimination therefore decides each chart and terminates. After a YES answer, sequentially testing positive integer C values terminates because any valid real C may be increased. This also makes the canonical evaluator and its error budget effective witnesses. No practical complexity claim is proved or needed.

## Separation and replay: the necessity mechanism

**Root normalization.** Along a chosen execution every available numerical value is a signed alias of an original input or of a rounded arithmetic output. Assignments and stored reuse introduce no new error. Distinct executed arithmetic nodes do create distinct roots even when their zero-error expressions coincide. Exact negation changes only an alias sign. This exhausts the allowed numerical operations; free polynomial predicates or exact nontrivial scalings would invalidate that normalization but are not allowed in the canonical model.

**Uniform separated execution.** All n raw inputs are already available when rounded roots are selected. With `M=n+N(P)`, `gamma=u/(64M)`, and 0<u<=1/4, the new multiplier s has an interval of length u inside [1/2,3/2]. For nonzero pre-result b and an earlier root w, the failure of one separation inequality reduces, when r=w/b>0, to `s in ((1-gamma)r,r/(1-gamma))`. If this interval meets the multiplier interval, r<=2. Its length is below 6gamma. Replacing w by -w gives at most another 6gamma. Thus all earlier roots exclude at most `12M gamma=3u/16<u`, leaving a legal choice. A zero pre-result produces a zero root; separation from nonzero roots then has ratio one and pairs of zero roots are exempt. Following whichever branch these choices select yields a legal full execution because the control-flow tree is finite. Adaptive selection in this existence proof is allowed: accuracy is required for **every** vector in the error box, so the selected vector is among the quantified vectors.

**Primitive forms.** Each signed raw input is a signed prefix sum of gaps. Each sum or difference of two such inputs is either a signed sum of prefixes or a signed difference of nested prefixes. Its coefficients, after a possible overall sign, are in {0,1,2}. Multiplying each gap by t_i in `[1-epsilon,1+epsilon]` therefore changes each primitive form relatively by at most epsilon, preserves its sign, and preserves zero exactly. Repeated operands, opposite aliases, tied magnitudes, and boundary gaps are all covered.

**Comparisons in replay.** The replay inductively fixes every existing rounded root numerically. Comparisons between two raw values are governed by primitive forms; comparisons between two rounded values stay unchanged. In a mixed comparison, separation gives a margin at least gamma times the larger magnitude unless both values are zero. The raw value changes by at most epsilon times its magnitude, and epsilon<gamma, so no strict comparison can switch. In the zero case both values remain zero. Thus equality branches are not assumed negligible. Consecutive comparison nodes and early returns need no separate arithmetic-node assumption: the same argument applies at each reached node.

**Arithmetic nodes in replay.** Both-rounded operands give unchanged pre-results. Both-raw addition/subtraction has the primitive relative bound epsilon; both-raw multiplication has `2epsilon+epsilon^2`. Mixed multiplication has epsilon. Mixed addition/subtraction has at most epsilon/gamma by separation, and can be zero only when both operands are zero. All zero pre-results are preserved. With gamma<1/3 and epsilon<1, the largest of the five bounds is `theta=epsilon/gamma=u/16`. Nonzero pre-results stay nonzero.

For the old output v=sb, with `|s-1|<=u/2`, setting `s'=v/b'` fixes the new rounded root exactly. Its deviation obeys

`|s'-1| <= (u/2+theta)/(1-theta) = 9u/(16-u) <= 4u/7 < u`.

The penultimate inequality holds for u<=1/4, with equality at u=1/4. Thus the full error budget is legal at every replayed node. Unused error coordinates may be filled arbitrarily. The output is either a fixed signed rounded root or a signed raw input changing relatively by at most epsilon. The output clause correctly covers trees with no executed arithmetic on a selected branch. There is no hidden need for a new error on an alias or a perturbation of held roots.

## Uniform local bound and interpolation

An accurate tree supplies a single positive u for eta=1/4. Shrinking u to at most 1/4 preserves its guarantee. M, gamma, and epsilon then depend on the fixed program and tolerance, not on input values, chart, or execution path. Accuracy at the original and replayed error vectors gives `|V|<=5|p(x)|/4`, `|p(x')|<=4|V'|/3`, and `|V'|<=(1+epsilon)|V|`. Since epsilon<1/5, their product is at most 2. No division by p(x) occurs, so zeros are included. Both x and x' lie in the whole-space domain required by the canonical target.

For fixed positive epsilon and degree bound D, the tensor-product Vandermonde grid in the t box is invertible. The sum of the absolute entries of its inverse bounds the coefficient l1 norm by the maximum absolute grid value and hence by the box supremum. Applying this to `Q_y(t)=q(y_1t_1,...,y_nt_n)` gives coefficient norm exactly q#(y), including zero coordinates. Each variable degree is at most deg(p). Thus `q#(y)<=2K|q(y)|` uniformly on the closed orthant. The finite K may be extremely large, but its size is immaterial to the existence/decision assertion. The zero polynomial is treated separately.

This proves the required necessity for arbitrary finite branching programs, rather than merely for a leaf regarded as a fixed formula. In particular, the proof never assumes that a path selected with nonzero errors is also selected at zero errors. The canonical-family corollary follows immediately. The single-uniform-tolerance corollary is also valid: replacing the factor 2 by `(1+eta_0)(1+epsilon)/(1-eta_0)` keeps it finite for eta_0<1, after which sufficiency provides an accurate canonical tree for every tolerance.

## Auxiliary face criterion and certificates

For a face polynomial with a positive zero z, an exposing vector produces a monomial exponential curve whose scaled q tends to zero while its scaled majorant tends to a strictly positive number. This rules out domination; the whole face is included by taking normal zero.

Conversely, failure on the closed orthant implies failure on its positive interior by continuity. A sequence of normalized absolute monomial contributions has a convergent subsequence in the compact simplex. Its nonempty limiting support T is facial: projecting logarithmic coordinates onto the span of differences in T yields a convergent bounded component, while the orthogonal component makes all outside-support log ratios tend to minus infinity. One sufficiently late member of that orthogonal-component sequence exposes exactly T, since the support is finite. The limiting positive weights on T are exponential weights of the bounded-component limit. Their signed sum is zero, so the resulting positive point is a zero of that face polynomial. This proves the converse and handles both behavior near boundary strata and escape to infinity.

The existential formula selects exactly one full exposed face because every unselected exponent has a **strictly** smaller normal value. The selectors are constrained to 0 or 1, and the nonempty-face condition is explicit. Rational exposing normals exist by rational linear feasibility and can be scaled to integral normals. A nonempty real semialgebraic positive-zero set over the rationals has a real-algebraic sample point. With an integer normal, the exponents `b-alpha dot v` in the scaled curve are nonnegative integers, so Q and H really are polynomials with `Q(0)=0<H(0)`. This is a mathematically effective negative certificate; a particular absent checker supporting only rational points would not limit the theorem to rational zeros.

## Examples and independently checked finite algebra

The difference-of-squares chart has a one-sign expansion and C=1. The specified three-term-sum chart gives q=a-c and q#=a+c, failing at (1,1,1). For the isolated-zero example, `(x^2-y)^2+x^2y^2` vanishes only at the origin. Substituting y=t^2 and x=t gives q=t^6; the negative part of the expanded chart has magnitude `2a(a+b)^2`, so the majorant along that curve is `t^6+4t^4`, as claimed.

I independently recomputed the displayed Motzkin chart expansion and its `3q-q#` certificate using exact integer polynomial arithmetic in a fresh standard-library Python check. Both identities passed. Independently expanding all six magnitude permutations gave negative-coefficient counts `[0,3,0,0,3,0]`: four one-sign cases and two middle cases. Evenness supplies the eight sign choices, so the same reasoning covers all 48 signed charts, with 16 requiring the middle-case certificate. Every term on the certificate's right side is nonnegative on the orthant. This check corroborates the printed finite identities; it is separate from the missing submitted scripts and does not establish the universal theorem.

The positive family discussed in Section 8 is analytically valid as well. For primitive-form products F and G, each chart yields signed coefficientwise-nonnegative polynomials U,V. The coefficient triangle inequality bounds the collected majorant by `U^2+UV+V^2`; opposite signs give `3(U^2-UV+V^2)-(U^2+UV+V^2)=2(U-V)^2`. Equal signs are immediate. Thus the stated C=3 follows without trusting the reported family-test counts.

## Experimental and remaining-scope limits

The received AA01 directory contains `manuscript.tex`, `manuscript.pdf`, two JSON logs (`solver_tests.json`, `structured_families_tests.json`), and an issue draft. It does not contain the separation/replay harnesses, compiler, symbolic tests, certificate checkers, generated Wolfram drivers, or solver implementations described in Section 8. Their reported counts, the claimed R=36 Motzkin compiled-program budget, the irrational certificate-export checks, and the solver-regression outcomes have **not** been independently reproduced or certified by this review. The source's package-reproducibility wording must therefore be read with this inventory limitation. It is not a mathematical gap in Sections 2–5, whose proof and termination argument do not depend on those experiments. In particular, a resource-limited solver returning UNKNOWN is not the always-halting mathematical decision algorithm; the latter is supplied by complete real quantifier elimination.

All numbered mathematical claims and the printed analytic example certificates pass for the stated model. No case of the exact canonical decision problem remains unresolved by this proof. Its limits are material: it does not establish a result for restricted domains not preserved by the gap perturbations, unbounded adaptive loops, numerical comparisons of exact symbolic expressions supplied for free, nonzero constant inputs, division, fused multiply-add, exact nontrivial scaling, polynomial black boxes, or correctly rounded IEEE arithmetic with error-free transformations. It establishes existence and decidability, without a useful runtime bound. No source or canonical file was edited during this review.
