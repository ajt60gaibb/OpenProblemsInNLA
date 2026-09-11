# Independent full-source review: TR-06

Review date: 2026-09-11. Verdict: **PASS for the exact canonical target.** Recommended status: **Solved**, affirmative, for every format and rank satisfying the stated generic complex identifiability assumption. No source correction is required. This is independent agent mathematical review, not external human peer review or formal verification.

## Source identity and complete coverage

I read the complete `references/colbrook-unclaimed-2026-09-11/manuscripts/TR-06.md`, including its front matter, theorem, general graph lemma, regular-locus argument, radial integration, limitations, and references, after independently investigating the proposed argument. Full UTF-8 source SHA256, replacing CRLF by LF and making no other normalization or trimming:

`65f9b731628a7a9ab0580d8522cead94bf7e4599ee3c4285e485287d35d451b2`

Locators: statement and model at line 11; theorem at line 24; graph-volume argument at line 28, with the multiplicity/exhaustion explanation at line 46; regular locus and normalized graph at line 48; radial integration at line 77; references at line 100. This review is tied to that complete source hash. The earlier preliminary report in `.cache/colbrook-unclaimed/reviews/TR-06-preliminary.md` reviewed the proof route; this record reviews the authored manuscript itself.

The actual `tensor-computations/TR-06/README.md` was read and compared. Its distribution is induced Euclidean volume on smooth identifiable real rank-r tensors, weighted by `exp(-||A||_F^2/2)`. Its condition number is the operator norm of the derivative of the individually normalized rank-one summands, with input tangent Frobenius norm and output product Frobenius norm. The manuscript uses exactly these definitions. It covers all requested r>=3, d>=3, n_j>=2 under generic complex identifiability. It does not substitute independent random summands or the unnormalized inverse derivative.

## Primary-source verification

Accessed on 2026-09-11:

- [Beltrán–Breiding–Vannieuwenhoven, preprint v2](https://arxiv.org/pdf/1903.05527): Assumption 1, Definition 1.3, equation (1.6), Theorem 1.9 and Conjecture 1.10 match the identifiability assumption, probability model, angular norm, known rank-two case, and higher-rank target. Definition 2.1 and Proposition 2.2 give a regular full-measure conical locus of dimension `k=r(1+sum_j(n_j-1))`; Lemma 6.1 supplies the same degree-minus-one homogeneity used in the manuscript. The [journal version](https://doi.org/10.1007/s10208-022-09551-1) uses equation (6), Theorem 3 and Conjecture 2.
- [Hardt–Lambrechts–Turchin–Volić, Real homotopy theory of semi-algebraic sets](https://msp.org/agt/2011/11-5/agt-v11-n5-p01-s.pdf), Theorem 2.4, printed page 2482 (PDF page 6), states that a bounded semialgebraic set of dimension at most s has finite s-dimensional Hausdorff measure. Closedness is not required. Its surrounding discussion identifies this measure with induced manifold volume, and its Proposition 2.3/Lemma 2.5 provide compatible smooth stratifications.

These checks verify the motivating target and the essential finite-volume theorem, not priority. The source paper contains a wording pitfall in Proposition 2.2(4), which calls the ordered addition map a global diffeomorphism despite the r! permutation fiber. The reviewed manuscript explicitly uses local branches and finite fibers and does not rely on that global-injectivity assertion.

## The general bounded-graph argument

Section 2 is correct under its stated hypotheses. Finite nonempty semialgebraic fibers imply that the graph set G has the same dimension s as L. Boundedness and the cited theorem then give finite H^s(G), even if G is not closed or its derivatives diverge near the boundary.

For a smooth branch g, the graph metric in an orthonormal tangent frame is `I+(Dg)*Dg`; therefore its volume factor is the product of `sqrt(1+sigma_j^2)`. Every factor is at least one, so that product dominates the largest singular value. This is an inequality for the actual operator derivative norm. It does not incorrectly replace that norm by `|det Dg|`, which would fail when other singular values are small or zero.

The explanation at line 46 supplies the needed global integration step: partition the base measurably under a countable local graph cover, count each distinct branch once over each piece, and sum the disjoint graph areas. Their Jacobian sum is at least the common branch norm K, because there is at least one branch. Exhaustion and monotone convergence allow the use of nonnegative integrands without assuming integrability beforehand. Alternatively the finite semialgebraic projection stratification gives the same conclusion. The inequality deliberately does not need a globally fixed fiber cardinality; in the tensor application it is r! and all branch norms agree by orthogonal permutations. No global labeling is needed.

## Regular full-measure real locus

The nonzero rank-one cone S is a smooth real semialgebraic manifold, of dimension `Sigma=1+sum_j(n_j-1)`. All matrix flattenings having rank at most one characterize the rank-one cone together with the origin, and removing the origin selects S. The ordered summation map on S^r is polynomial and the generic complex fibers have r! elements under the hypothesis. In characteristic zero this implies a full-rank generic differential and image dimension k=r Sigma; it is not merely an assertion of isolated solutions at every exceptional point.

The real-locus step in Section 3 is valid. An expanded justification is as follows. The real points of the product of rank-one cones are Zariski dense in its complexification, as is seen from the real multilinear factor parameterization. Thus the nonempty generic complex regular/identifiable locus meets the real domain. Its real image consists of tensors with actual real decompositions and has dimension k. The proper exceptional algebraic sets for identifiability and image smoothness have dimension below k on this image. The critical values of the generically full-rank real polynomial map likewise have smaller dimension. Removing these sets leaves a nonempty full-dimensional smooth semialgebraic locus of real rank-r tensors; its complement has zero induced k-volume. This is also the r-nice regular locus constructed in the primary source.

The restriction is understood within the manuscript's original real rank-r input set M; it does not replace M by every real point of the complex secant variety, some of which might have larger real rank. Semialgebraicity is justified by the rank-one equations, projections, smooth algebraic locus, and real quantified uniqueness conditions. If complex uniqueness is used in such a formula, real and imaginary parts give a real-algebraic encoding. No effective efficient rank algorithm is required.

Uniqueness, smoothness, and full-rank regularity are invariant under common nonzero scaling, so the locus may be chosen conical. Its dimension is the asserted k, which exceeds one for all admitted formats. The omitted null set includes any identifiable but critical point where a differentiable local inverse is unavailable; uniqueness alone is not being used as a substitute for inverse regularity. No expectation depends on a chosen value of the condition number on that null set.

## Normalized graph, multiplicity, and smooth branches

The unit link `L=M^circ intersect {||A||=1}` is smooth of dimension s=k-1: the radial vector is tangent to the cone and the norm has nonzero derivative on it. L is nonempty, bounded, and semialgebraic. The finite-volume theorem applies to this possibly nonclosed link.

The graph definition at line 62 is semialgebraic exactly as claimed. Auxiliary positive variables t_i satisfying `t_i^2=||a_i||^2` and `t_i u_i=a_i` implement individual normalization; the nonzero rank-one constraint avoids division by zero. Projecting away these variables preserves semialgebraicity. Boundedness follows from the unit norm of A and each u_i, regardless of possible divergence of the discarded summand magnitudes. That last distinction is essential.

A minimal rank-r decomposition cannot contain two proportional summands: they can be merged into one rank-one summand or cancel, contradicting rank r. Its normalized components are consequently distinct. Identifiability gives exactly r! ordered decompositions and r! distinct normalized tuples. In particular each fiber is finite and nonempty, so the graph dimension is k-1; the auxiliary unbounded magnitude variables do not enlarge its dimension.

The inverse-function theorem gives smooth local ordered summand branches at each regular point. On a sufficiently small base neighborhood those r! branches exhaust all decompositions, by uniqueness. Normalization is smooth on the nonzero summands, yielding the local normalized graphs required in Section 2. Permutation of labels acts isometrically on the product output space and gives identical derivative norms. Thus the application of equation (1) proves equation (2), including integrability near every omitted boundary stratum, without assuming a global ordering or extension of normalized outputs to the boundary.

## Full angular derivative and radial integration

With compatible local labels, a decomposition of tA is t times the decomposition of A for t>0. The normalized map is therefore constant on positive rays. Its radial derivative vanishes. At A in L the induced tangent space splits orthogonally as `T_A M^circ = R A direct-sum T_A L`. The full derivative norm in the canonical definition is hence **equal** to the derivative norm on the unit link, not merely bounded below by it. Differentiating the scaling identity yields the stated `kappa_ang(tA)=t^-1 kappa_ang(A)`. This agrees independently with the primary source's Lemma 6.1.

The polar parameterization `(t,A)->tA` is one-to-one for t>0 and A in L. Its induced volume element is `t^(k-1) dt dV_L`: radial length is one and all k-1 orthogonal link directions scale by t. Tonelli therefore separates the weighted condition-number integral into the link integral from equation (2) and `integral_0^infinity t^(k-2) exp(-t^2/2) dt`. The radial factor equals `2^((k-3)/2) Gamma((k-1)/2)` and is finite for k>1. This explicitly checks the potential singularity at the origin, not only Gaussian decay at infinity.

The same polar calculation gives the asserted Z with radial exponent k-1. Its link factor is finite by bounded semialgebraicity and strictly positive because a nonempty smooth manifold of its stated dimension contains a positive-volume local patch. Thus `0<Z<infinity`. Restoring the removed volume-zero set changes neither numerator nor denominator. Dividing proves finite expectation in the precise volume-Gaussian model.

## Final scope and remaining cases

Every mathematical claim in the reviewed manuscript passes. There is no remaining case of canonical TR-06 under its hypotheses. The rank-two consistency statement is valid as an auxiliary consequence. The argument supplies existence of a finite expectation for each fixed format and admissible rank; it supplies neither a useful format-uniform numerical estimate nor an efficient decomposition algorithm.

The exclusions are accurate: the ordinary condition number concerns an unbounded output graph and is not covered; generic nonidentifiability or infinite decomposition fibers invalidate the finite-fiber argument; and the graph Jacobian estimate does not imply arbitrary higher moments. No numerical diagnostics, finite examples, or tests were used as substitutes for the measure and derivative proof. No canonical target, status, ID, or source file was altered by this reviewer.
