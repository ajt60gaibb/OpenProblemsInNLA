# TR-17: independent complete-source proof review

Review date: 2026-09-11. **Verdict: PASS for the full canonical target. Recommended status: Solved, affirmative.** The proof establishes global Frobenius minimality for every allowed Segre–Veronese format and every positive-definite real ambient metric. I found no required mathematical correction. This is independent Codex-agent proof review, not external human peer review, formal verification or historical priority certification.

## Exact source and target

I read the complete 279-line `.cache/tensor20/submission/TR-17/solution.tex`, including all proofs, global assumptions, multiplicity statements, supplementary checks and bibliography. Complete UTF-8 source SHA256, replacing CRLF with LF with no trimming or other normalization:

`dd5e71eb942e6b928264426e6598c4cd47b14a04b08d3c3b82f4d38b5a065c3b`

I read the canonical statement directly with `git show origin/main:tensor-computations/TR-17/README.md`. It asks whether ED_Q(X)>=ED_QF(X) for every k>=1, n_j>=2, d_j>=1 with sum d_j>=3 and every positive-definite symmetric real bilinear form Q on the full partially symmetric tensor space. The ED count is on the smooth nonzero complex cone, with the metric extended complex-bilinearly and with algebraic multiplicities. The Frobenius restriction includes repeated-entry weights. The manuscript uses all these conventions exactly. Its theorem additionally includes lower total degrees; these extra cases do not narrow the canonical claim.

Source locators: main Theorem 1, line 39; positivity Lemma 2, line 67; CSM-basis Proposition 3, line 140; coefficient Lemma 4, line 180; ED formula and sum, lines 199–215; Frobenius comparison, section starting line 218; gap Corollary 5, line 243; checks and scope, line 254.

## Primary references checked

Accessed on 2026-09-11:

- [Kozhasov–Muniz–Qi–Sodomaco, primary v3 text](https://arxiv.org/html/2309.15105v3), Conjecture 3.9, states the global metric comparison. Theorem 3.12 is only local near a Frobenius metric, and the known special cases do not imply the complete target. The submitted proof does not make that inference. [Publication DOI](https://doi.org/10.1090/mcom/4176).
- [Aluffi–Harris, primary manuscript](https://arxiv.org/pdf/1708.00024), §2, equation (2.1), defines projective ED degree via the affine cone's critical-point count. Theorem 8.1 gives EDdeg(Y)=(-1)^dim(Y) chi(Y minus (Q union H)) for smooth projective Y and general H. Equation (7.3) gives the corresponding CSM expression, and (7.4) gives the logarithmic tangent CSM formula for an SNC divisor. These results do not require the original isotropic intersection to be smooth or reduced. The smoothness required of Y itself is satisfied here.

The source checks establish the exact external inputs, not novelty. The proof also uses standard characteristic-zero embedded resolution, Bertini for base-point-free systems, proper functoriality of CSM classes, and the top-Chern formula for an isolated zero scheme. Their hypotheses are accounted for below; they are not computational assumptions.

## 1. Positive form and critical-point argument: PASS

The restriction of Q to a nonzero real pure partially symmetric tensor is positive. Such a tensor is nonzero whenever every real factor vector is nonzero. The resulting q has multidegrees 2d_j and is real. Taking the reduced support of its vanishing divisor is appropriate for the complement; multiplicities will instead appear as residues. Positivity on real product points also excludes the whole Segre–Veronese variety lying in the isotropic quadric.

For the auxiliary lemma, positivity on the compact product of real unit spheres gives a strictly positive lower bound c. Multihomogeneity gives f(x)>=c product_j ||x_j||^(b_j) for real factor vectors. For fixed nonzero real linear forms ell_j, the affine hyperplanes ell_j(x_j)=1 give positive lower bounds on each factor norm. Thus the product lower bound tends to infinity when any factor norm tends to infinity. The positive dehomogenized polynomial is coercive and attains a finite minimum with f nonzero. Its derivative restricted to the affine chart vanishes there.

Euler's identities x_j dot grad_j f=b_j f show that each gradient block is nonzero on f!=0. Its projective class is independent of all choices of homogeneous representatives, so the block-gradient map is a morphism from that open product to the product of dual projective spaces. A critical point of f/product ell_j^(b_j) gives each projective gradient block equal to ell_j. Conversely, that equality and f!=0 force ell_j(x_j)!=0 by Euler; in the chart ell_j=1 the constrained derivative vanishes. This covers precisely the logarithmic critical equations on the required open chart.

Every real tuple of nonzero covectors has a preimage furnished by the real minimum. The real points of the product of projective dual spaces are Zariski dense, so the morphism is dominant. Its irreducible domain and target have equal dimension a. The generic fiber is therefore nonempty and zero-dimensional, hence finite; there is a nonempty open parameter set with that property. The same statement holds scheme-theoretically for the zero set of d log F, because its equations on the chart are the constrained derivative equations with invertible factors removed. Generic real choices exist. The proof does not assume that a minimum is isolated for every covector, or that all complex critical points are real.

## 2. Boundary residues and top Chern class: PASS

An embedded log resolution of div(f), isomorphic outside its support, produces a smooth projective variety and an SNC reduced inverse image E. Every component of E appears with a strictly positive integer multiplicity in the pulled-back zero divisor. The pullbacks of the factor hyperplane systems are base-point-free. General choices can be made smooth and transverse to E's finitely many smooth intersections and to each previous chosen divisor; where a stratum's image is a point, a general hyperplane avoids it. No ample or birational hypothesis for these pulled-back linear systems is needed for this generic Bertini statement.

The general hyperplanes can also avoid containing the image of every E component. Their orders along those components are then zero. Thus in div(pi*F), the E components have positive coefficients mu_i and the hyperplane pullback components have negative nonzero coefficients -b_j. Different chosen divisors share no component. The sum is an SNC boundary; a pulled-back divisor with disconnected components causes no difficulty.

Locally near a boundary point, pi*F is a nowhere-vanishing unit times a product of coordinate powers. Its logarithmic differential is a regular section of the logarithmic cotangent bundle. Along each boundary component the coefficient of dz_i/z_i restricts to the corresponding nonzero integer residue. The regular differential of the unit contributes zero to that coefficient on z_i=0. Even at an intersection of zero and pole divisors, residues lie in distinct basis directions and cannot cancel each other. Hence the logarithmic section has **no boundary zeros**.

Its remaining zero scheme is the finite nonempty interior critical scheme. On a smooth a-dimensional variety, an isolated zero scheme of a rank-a bundle section is cut locally by a regular sequence: the regular local ring is Cohen–Macaulay and the ideal of a isolated zero has height a. Therefore its top Chern degree is the sum of its local scheme lengths, not an unsigned real index or an unjustified count of distinct points. The degree is at least one. This explicitly covers non-Morse critical points.

The logarithmic CSM formula and integration give chi of the complement as the degree of the top Chern class of the logarithmic tangent bundle. Dualizing the rank-a bundle multiplies its top Chern class by (-1)^a. Thus the top-Chern length is exactly (-1)^a chi(V), proving the lemma for arbitrary singular and nonreduced f. The distinction between ordinary and compactly supported Euler characteristics causes no error for these complex algebraic varieties. No boundary point has been discarded from the zero count without justification.

## 3. CSM section basis and positivity: PASS

The proposed basis has leading monomial (-1)^|alpha| h^alpha, and all other monomials have larger componentwise degree. In the finite truncated Chow ring this gives an integral triangular invertible change of basis.

To interpret a coefficient, take m_j-alpha_j general factor hyperplane cuts and remove one more general hyperplane in every positive-dimensional remaining factor. The log resolution may be used for these operations: the base-point-free systems permit smooth transverse successive cuts, and the resulting complement maps isomorphically to the desired section complement. Each cut contributes h_j/(1+h_j) by logarithmic adjunction; deleting a transverse boundary hyperplane contributes 1/(1+h_j). Proper pushforward and the projection formula thus give exactly the manuscript's coefficient formula for chi(U_alpha). Singularities of the original D introduce no unexamined transversality requirement.

For alpha_j=0 the final product section is a point in that factor; the extra factor (1+h_j)^(-1) is harmless when extracting degree zero. General real cuts yield real product-linear sections, and the restricted form remains positive and of the same positive even degree in every remaining positive-dimensional factor. If every factor has dimension zero, the section complement is a single point, since f is positive there.

Substituting a basis term beta in the section formula leaves coefficient [h_j^(alpha_j-beta_j)](1+h_j)^(alpha_j-beta_j-1). If alpha_j-beta_j>0, the polynomial degree is one smaller than the requested degree, so this coefficient vanishes. If all differences are zero, the coefficient is one; terms with beta outside the componentwise range cannot contribute. This proves g_alpha=(-1)^|alpha| chi(U_alpha), with the signs as written. The positivity lemma therefore supplies g_alpha>=1 for **every** index, including all boundary and zero-dimensional indices.

## 4. Nonnegative weights and ED conversion: PASS

Writing beta for a fixed multi-index, expansion of the rational series gives a sum over ell<=beta with sign (-1)^|ell|, binomial coefficients and coefficient [h^(beta-ell)]L^(|beta|-|ell|). Expanding product_j(L-h_j)^(beta_j) gives the identical expression. Thus the weight identity is exact, not a positivity inference from alternating coefficients. Since L-h_j=(d_j-1)h_j+sum_(i!=j)d_i h_i, all coefficients are nonnegative for d_j>=1, including the cases d_j=1 where some weights vanish. B_0=1.

A real positive-definite Q can be taken to the standard bilinear form by an invertible real linear change of ambient coordinates. This carries the smooth Segre–Veronese Y to another smooth projective variety, preserves the affine-cone critical problem, and pulls the ambient hyperplane class back to L=sum d_j h_j. The Aluffi–Harris formula therefore applies with the complement of the reduced zero support of q. It gives ED_Q(X)=(-1)^N integral cSM(U)/(1+L). The distinction between their projective notation and the manuscript's affine-cone notation is reconciled by their explicit definition in §2.

Inserting the basis and setting beta=m-alpha yields the coefficient (-1)^(N+|alpha|), equal to (-1)^|beta|. The remaining numerator is product_j(1+h_j)^(beta_j). Hence the ED sum is exactly sum_alpha g_alpha B_(m-alpha), with no missing embedding-degree factor. Since every g_alpha>=1 and every weight is nonnegative, the asserted lower bound follows.

## 5. Frobenius comparison, equality and sample formulas: PASS

The entrywise Frobenius metric on symmetric tensors gives q_F=product_j(sum_t x_jt^2)^(d_j). This verifies that the manuscript uses the repeated-entry weights of the canonical target. Its reduced divisor is the union of factor quadrics. Each is smooth, including the two distinct points in a projective line. The complement CSM factor is (1+h_j)^(m_j+1)/(1+2h_j).

The finite geometric sum of (-h)^a(1+h)^(m-a) equals ((1+h)^(m+1)-(-h)^(m+1))/(1+2h). Modulo h^(m+1) this is precisely the claimed basis identity. Multiplicativity over the product therefore gives g_alpha(Q_F)=1 for every alpha, independent of the d_j. The ED sum at Frobenius is sum_beta B_beta, attaining the universal lower bound. This proves the global theorem for an arbitrary fixed positive-definite Q rather than only for Q near Frobenius or for generic Q.

The gap is a finite sum of nonnegative integers (g_alpha-1) times nonnegative weights. It vanishes exactly when every coefficient with positive weight has g_alpha=1. Zero weights need impose no equality condition, as the corollary correctly states.

For one factor, the weight is (d-1)^b. For two unsymmetrized factors, the product is h_2^(b_1)h_1^(b_2), so the target coefficient is one only when b_1=b_2; summing gives min(n_1,n_2). For three unsymmetrized two-dimensional factors, the weights by total support size are 1, zero for singletons, one for each of three pairs, and two for the full triple, totaling six. These formulas independently confirm the algebraic signs and indexing in the manuscript; the proof does not depend on these finite cases.

## Computational evidence and limitations

The submitted notes report exact coefficient checks and four saturated critical-scheme examples, including non-Morse and nonreduced cases. I read those notes as supporting claims, not universal proof. This review does not certify those script runs or infer global positivity from them; computational validation is coordinated separately by the parent agent. In particular, generic critical-scheme finiteness, absence of logarithmic boundary zeros and all-index CSM positivity are established by the arguments above rather than by chart enumeration in small formats.

The required positivity is positivity of the restricted real multihomogeneous form; ambient positive definiteness guarantees it. The proof does not assert a corresponding inequality for indefinite metrics, sesquilinear complex distances, expected real critical counts, or arbitrary smooth projective varieties in place of the Segre–Veronese embedding. These are different targets. No canonical cases remain: arbitrary allowed factor counts, dimensions, degrees, metrics and singular/nonreduced isotropic intersections are covered.

## Final recommendation

Record **TR-17 as Solved, affirmative**, retaining its original statement and permanent ID. The complete source proves global minimality of the Frobenius ED degree and the stated nonnegative expression for the excess. The verification level should remain explicitly independent agent proof review, with the complete source hash above; no external human peer review or priority certification is implied.
