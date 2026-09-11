# TR-06 — second independent proof review

Reviewer: independent adversarial AI review, 11 September 2026. This is a mathematical source review, not external human peer review or a priority certification.

**Verdict: PASS for the full canonical TR-06 target.** The manuscript proves finite mean angular condition number for each fixed admissible format and rank under generic complex identifiability, with the canonical induced-volume Gaussian input distribution and product Frobenius derivative norm. No material gap or required source correction was found. Recommendation: the canonical problem can be recorded as resolved by the affirmative result, with the proof and its review provenance linked. This conclusion does not establish a uniform bound over formats, higher moments, or integrability of the ordinary condition number.

## Reviewed sources and binding

Read the complete manuscript `references/colbrook-unclaimed-2026-09-11/manuscripts/TR-06.md`, including all four sections, references and front matter, and the complete current canonical `tensor-computations/TR-06/README.md` (status Open, last checked 2026-09-10).

The manuscript's complete UTF-8 source, with CRLF replaced by LF and with no trimming, has **8,373 bytes** and SHA-256:

`65f9b731628a7a9ab0580d8522cead94bf7e4599ee3c4285e485287d35d451b2`

This hash was independently computed from the file read during review. It binds the entire original Markdown source, not an extracted body, rendered derivative, or mathematical-content-only normalization.

The principal theorem is the unnumbered **Theorem in Section 1, line 24**. Its proof consists of the graph estimate **Section 2, equation (1), lines 28–46**, its tensor application **Section 3, equation (2), lines 48–75**, and radial integration **Section 4, equation (3) and the following displayed integrals, lines 77–98**. The most delicate claims are the regular locus construction at **line 50**, local graph assertion at **line 69**, and measurable partition argument at **line 46**.

## Canonical target and primary-source comparison

The canonical input is a tensor sampled by induced Euclidean volume on the smooth identifiable real rank-r locus, weighted by exp(-||A||²/2). The output map normalizes every actual rank-one tensor summand before differentiation. The manuscript preserves both choices exactly. Its r ≥ 3 statement covers the entire still-open rank range in the canonical page and does not replace it by a summand-sampling problem.

Primary sources were opened and checked directly:

- [Beltran, Breiding and Vannieuwenhoven, author preprint arXiv:1903.05527v2](https://arxiv.org/pdf/1903.05527): Definition 1.3 supplies the Gaussian-volume model; equation (1.6), Theorem 1.9 and Conjecture 1.10 identify the angular quantity and rank distinction. Definition 2.1 and Proposition 2.2 describe the regular locus; Lemma 6.1 confirms inverse-radius scaling. Proposition 2.2(4) literally claims a global diffeomorphism for the ordered map, conflicting with its permutation fibers. The reviewed manuscript correctly uses only local inverses and does not inherit that statement.
- [Hardt, Lambrechts, Turchin and Volic, *Real homotopy theory of semi-algebraic sets*, Theorem 2.4, page 2482](https://msp.org/agt/2011/11-5/agt-v11-n5-p01-s.pdf): the cited theorem applies to bounded semialgebraic sets of dimension at most the Hausdorff-measure index, without a closedness assumption. The adjacent Proposition 2.3 supplies compatible smooth stratifications of semialgebraic maps. These are exactly the finite-volume and dimension tools needed here.

The following arguments were independently reconstructed rather than inferred from the manuscript's claim of verification or from any numerical experiment.

## 1. The bounded-graph lemma is valid

Let L be an s-dimensional embedded smooth manifold with its induced metric, and let g be a local branch. Choose an orthonormal basis of T_xL. For the graph embedding h(x)=(x,g(x)), its differential has Gram matrix I+(Dg)*Dg in this basis. Thus the stated graph Jacobian is correct even when L is curved in its ambient space. The identity term is essential: it arises from retaining the input A in the graph.

For the singular values sigma_j of Dg, each factor sqrt(1+sigma_j²) is at least one. Selecting a largest singular value therefore proves

`J_g = product_j sqrt(1+sigma_j²) >= sqrt(1+||Dg||²) >= ||Dg||`.

This inequality does not require all singular values to be large or comparable. In particular, singular directions that become ill-conditioned separately do not create a missing product estimate.

Finite nonempty fibers of a semialgebraic projection imply that the graph has dimension exactly s: the zero-dimensional fiber dimension prevents an increase, and surjectivity prevents a decrease. Boundedness and the cited finite-volume theorem then give finite H^s(G). The graph need not be closed or complete, and its derivatives need not be uniformly bounded.

The area-formula step is also noncircular. A smooth graph map is locally Lipschitz; restrict to a countable exhaustion by relatively compact coordinate patches if necessary. The ordinary nonnegative area formula on such patches extends by monotone convergence. It does not presuppose that ||Dg|| is integrable.

A particularly direct implementation of the manuscript's partition is available here. Take countably many base neighborhoods U_j on which all sheets exist. Set B_1=U_1 and B_j=U_j minus the preceding neighborhoods. These measurable base sets are disjoint and cover L. On each B_j integrate all distinct sheets. The graph pieces are disjoint across different B_j because their first coordinates differ, and within B_j because the sheets have distinct values. Their areas sum to H^s(G). Since there is at least one sheet over every point and every sheet has derivative norm K(x), this yields the claimed inequality. In the tensor application there are exactly r! sheets, and one can even retain that multiplicity for a stronger estimate; its omission only weakens the upper bound.

Monodromy does not invalidate this construction. There is no need to extend any labeling around a loop, or to produce a continuous global choice of summands. The quantity K is well defined because permutations act by fixed orthogonal maps in the output space.

## 2. Full-measure regular real domain

The section-3 regular-locus paragraph is compressed but sound. The following expansion checks that it does not discard a set of positive input volume or assume the existence of real generic decompositions without justification.

Let S be the nonzero rank-one tensor cone and X=S^r. Its dimension is k=r[1+sum_j(n_j-1)]. This is the space of actual summands, so factor rescaling ambiguities have already been removed. Its complexification is irreducible. Real points of X are Zariski dense: in a factor parametrization, a polynomial identity holding for every real tuple of factor entries holds identically, and the nonzero restrictions do not destroy this density.

The addition map has finite generic complex fibers by identifiability. Hence its image closure has complex dimension k and the differential has rank k on a dense open subset in characteristic zero. The source critical locus has dimension below k; its image has dimension below k as well. The singular locus of the irreducible image closure and a proper algebraic exceptional set for generic identifiability likewise have smaller dimension. Their relevant inverse images and images can be treated by algebraic closure or semialgebraic dimension. Thus the real rank-r image contains a nonempty regular set outside a subset of real dimension at most k-1. Real Zariski density rules out the concern that every real decomposable point lies in the complex exceptional set.

Equivalently, take real rank-r points of the smooth image variety which are complex identifiable and whose ordered decompositions are regular. These conditions define a semialgebraic set. Smoothness and differential rank can be expressed in charts by nonvanishing minors. Existence and uniqueness of decompositions are polynomial first-order conditions after recording real and imaginary parts if complex uniqueness is used; quantifier elimination gives semialgebraicity. One may further restrict to a dense open semialgebraic subset as needed.

All these regularity properties are invariant under simultaneous multiplication of a tensor and its summands by a nonzero real scalar. The exceptional closure can also be chosen conical. Therefore the regular full-measure set can be chosen as the cone M° needed later, rather than as an arbitrary nonconical open set. Its complement in the k-dimensional canonical smooth locus has H^k measure zero. Lower rank tensors, if included by a source's rank-at-most-r notation, also belong to a lower-dimensional set and do not change this conclusion.

Near such a real point, the ambient real algebraic smooth locus is a k-dimensional manifold. The real derivative of addition is an isomorphism between the k-dimensional source tangent space and this tangent space. The inverse function theorem therefore maps a neighborhood of each real ordered decomposition diffeomorphically onto a neighborhood of the tensor. This provides real decompositions for all points in that neighborhood and justifies using the induced tangent metric of the image manifold.

No appeal to a global bijection of the ordered addition map is needed. The stronger, literally incorrect global clause in the source preprint is unnecessary to this verification.

## 3. The normalized graph has the asserted local sheets

The nonzero rank-one cone is smooth: factor charts obtained by selecting nonzero entries yield its usual dimension, and the all-flattenings rank-one equations, together with a nonzero condition, give a semialgebraic description. The addition constraint is polynomial in the actual summands.

Normalization is correctly encoded using t_i>0, t_i²=||a_i||², and t_i u_i=a_i. Positivity selects the actual norm and prevents artificial sign choices. Projecting these variables leaves exactly the normalized graph, by real quantifier elimination. Unbounded values of a_i and t_i in this projection are allowed; semialgebraic projection does not require a proper map or bounded quantified variables.

The resulting G is contained in the product of the input unit sphere with r output unit spheres. Consequently it is bounded even along sequences whose unnormalized summands blow up and cancel. Its closure might contain extra limiting points, but no closed-graph claim is used. The finite-volume theorem applies directly to G.

For a minimal decomposition, two proportional nonzero summands could be combined into one nonzero rank-one summand or canceled entirely. Either case would reduce rank below r. Thus proportional pairs cannot occur, and in particular all normalized summands are distinct. Exactly r! distinct normalized ordered tuples occur at an identifiable point.

There is no hidden covering-map assumption here. Fix a regular A and its r! ordered decompositions. The inverse function theorem gives disjoint source neighborhoods and a common base neighborhood carrying these r! smooth inverse maps. Every nearby point remaining in the identifiable locus has exactly r! ordered decompositions. The already-constructed inverse branches account for all of them, so no additional decomposition can arrive from infinity. Composing with normalization gives all the sheets of G over that neighborhood. This rules out the principal nonproperness concern without assuming properness of addition.

Distinct normalized tuples remain distinct after shrinking the base neighborhood. Differing orderings are fixed permutations of these smooth maps there, so their derivative norms coincide. Restricting to the transverse unit link preserves the smooth local sheet structure. All assumptions of the section-2 lemma have therefore been verified, rather than merely inferred from finite fibers.

## 4. Link and radial integration

Positive scaling preserves M°. At a unit point A the radial vector A is tangent to M° and the derivative of ||A||² in that direction is 2. The unit sphere is consequently transverse. Its intersection L is a smooth semialgebraic manifold of dimension s=k-1. It is nonempty because M° is nonempty and conical. It has positive s-volume because any nonempty smooth manifold has a coordinate patch of positive induced volume; bounded semialgebraicity gives finite total volume.

Homogeneity of the unique summands supplies a compatible local labeling with Psi(tA)=t Psi(A). Normalizing removes t, so f is constant on each positive ray. Differentiating gives Df(A)[A]=0. At unit A,

`T_A M° = span(A) orthogonal-direct-sum T_A L`.

Thus restricting Df to the link loses only a zero direction and preserves the operator norm. Applying the chain rule to f(tA)=f(A) gives Df(tA)[t v]=Df(A)[v]. Since positive scaling identifies the conical tangent subspaces in the ambient Euclidean space, this proves the stated inverse-radius law for the full operator norm. Normalizing the summands inside the derivative is indispensable to this step and is done correctly.

For the polar parametrization (t,A) -> tA, the radial derivative is A and an orthonormal angular tangent basis becomes t times that basis. Their Gram matrix is diag(1,t²,...,t²). The volume Jacobian is therefore t^(k-1), with no further density or metric factor.

All relevant integrands are nonnegative and measurable, so Tonelli applies before finiteness has been established. The numerator separates into the finite link integral from equation (2) and

`integral_0^infinity t^(k-2) exp(-t²/2) dt = 2^((k-3)/2) Gamma((k-1)/2)`.

This is finite exactly for k>1. The hypotheses ensure this with substantial margin. For the denominator the radial integral is

`integral_0^infinity t^(k-1) exp(-t²/2) dt = 2^((k-2)/2) Gamma(k/2)`.

Together with positive finite link volume, it gives 0<Z<infinity. There is no singular probability mass at the origin. Restoring any removed k-dimensional null set leaves the numerator and denominator unchanged, even if the condition number is assigned infinity on that null set. Dividing by Z therefore gives the exact asserted finite expectation.

## Boundaries, scope, and disposition

The proof covers every fixed format/rank in the canonical hypotheses, including perfect formats when they satisfy generic complex identifiability. It does not require a strictly subambient-dimensional image. It is also consistent with the known rank-two result; nothing in the new argument requires r ≥ 3 other than the canonical open range.

Unnormalized summands can diverge; this was explicitly included in the adversarial check and does not break boundedness of G. Conversely, removing normalization would remove the boundedness argument and is not justified. The graph Jacobian controls the first power of the largest singular value, not arbitrary higher powers. Small-radius convergence has been checked independently rather than inferred from Gaussian decay, which only controls large radius.

The argument is analytic and semialgebraic and has no numerical certificate, bit-complexity claim, or finite diagnostic dependency. No computational experiment is used as proof. No counterexample or missing hypothesis was found after checking the full-measure real locus, local-sheet construction, permutation multiplicity, graph measure, and radial exponents.

**Final recommendation: PASS; full affirmative resolution of the existing TR-06 mathematical target.** Preserve the canonical ID, path, tensor-volume probability model and normalized derivative definition. No source or canonical files were edited in this review. This assessment establishes the validity and scope of the reviewed proof, not its historical novelty or acceptance by an external journal.
