# TR-26 — independent complete-source proof review

Reviewer: independent AI proof audit, 11 September 2026. The reviewer did not develop this manuscript. This report is not external human peer review, formal proof verification, or a historical priority determination.

**Verdict: PASS for the full canonical TR-26 target.** The complete argument establishes, for every integer d >= 2 in the fixed standard unweighted embedding over the complex numbers, reduced isotropic degree 2d and reduced nonisotropic degree 6(d-1). It also proves that the former is a union of 2d distinct complex hyperplanes and the latter is irreducible. The multiplicities required to subtract the isotropic degree from the total discriminant degree are established independently within the proof. No material gap or required manuscript correction was found.

**Status recommendation:** resolve the existing canonical TR-26 problem affirmatively, preserving its identifier, path, fixed embedding, bilinear quadratic form, and reduced-set convention. The statement is not extended to arbitrary weighted embeddings or repeated-root denominators.

## Complete source binding and locators

Read the entire manuscript `references/colbrook-unclaimed-2026-09-11/manuscripts/TR-26.md`, including development status, abstract, all eight sections and references, and the complete canonical `tensor-computations/TR-26/README.md`, whose reviewed status is Partially resolved and last-checked date is 2026-09-10.

The manuscript's complete UTF-8 source, replacing CRLF by LF and performing no trimming or other normalization, has **17,497 bytes** and SHA-256:

`4a96398678689820dffd81522991fa4178062789afd657acc73194f0852185f8`

This hash was independently computed from the source read during this audit. It includes the full source and is not the hash of a rendering or an extracted proof body.

Principal locators in that source:

- **Theorem 1**, line 39: exact component and degree claims.
- **Section 2**, lines 47–94; **Lemmas 2 and 3**, lines 77 and 83: binary correspondence and the canonical Jacobian condition.
- **Section 3**, lines 96–118, equation (4): exact isotropic union.
- **Section 4**, lines 120–137, equation (5): nonisotropic irreducibility, dimension and separation from isotropic hyperplanes.
- **Lemmas 4 and 5**, lines 141 and 166: generic root patterns, with the d=2 case separated.
- **Section 6**, lines 170–219; **Lemma 6**, line 196: discriminant support, transversality, multiplicities, and reduced degree.
- **Section 7**, lines 221–234: pullback to symmetric matrix space, including its kernel and constant quotients.

## Target and primary-source comparison

Opened the [June 2026 primary paper, arXiv:2512.06939v2](https://arxiv.org/html/2512.06939v2), including Section 3.2. Proposition 3.10 gives the binary correspondence degree and total discriminant degree; the following ramification decomposition defines the isotropic and nonisotropic parts. Conjecture 3.14 asks for exactly the two degrees in the canonical page. Examples 3.12–3.13 concern small degrees, while the stated checks through d=10 are numerical evidence. The manuscript addresses the general conjecture and does not treat those checks as proof. Factoring isotropic equations into complex hyperplanes is consistent with the primary paper's grouping of factors over the rationals.

The canonical definitions are preserved: matrices are complex symmetric, transpose is bilinear rather than conjugate transpose, the rational normal curve has no binomial weights, and degree concerns each reduced projective algebraic set including all its components. The proof also identifies the precise Jacobian-defined ramification locus; it does not merely compute an unrelated resultant.

## 1. Binary reduction and exact correspondence

With m=2d, the pulled-back denominator is D(a,b)=sum_i a^(m-2i)b^(2i). In the chart a=1, its product with t²-1 is t^(m+2)-1. Since m+2 is even, both 1 and -1 are roots of the numerator. They are canceled simple roots, and the remaining m roots are distinct in characteristic zero. D(0)=1 and D(0,1)=1 exclude both coordinate endpoints. Thus the proof has exactly m finite, nonzero, simple isotropic parameter points; it does not rely on a generic-denominator assumption.

For the numerator map T, the k-th binary coefficient uses only symmetric matrix entries with i+j=k. These antidiagonals are disjoint. For every 0<=k<=2d there is at least one entry, whose coefficient is 1 or 2. This explicitly constructs a nonzero independent coefficient direction for each binary monomial. T is therefore surjective onto all of V, not merely onto a special subspace with restricted jets.

I independently checked the homogeneous Wronskian normalization. Euler's identity in the chart gives N_a=mN-tN' and D_a=mD-tD', so

`(N_b D_a - N_a D_b)/m = N'D-ND'`.

Its homogeneous degree is 2m-2; the possible top affine terms cancel, as they should. The homogeneous form retains projective roots at infinity even when an affine representative loses degree.

At any nonisotropic point, arbitrary value/first-derivative jets of N make evaluation of F_N a nonzero functional. At an isotropic point r it is -D'(r)N(r), also nonzero. Hence the bundle evaluation map is everywhere surjective. Its kernel is a vector bundle, and its projectivization is smooth and irreducible over the irreducible parameter line. The complement of finitely many base fibers is dense. Thus the equation F_N=0 is exactly the closure of the critical correspondence, including all isotropic fibers; no extra irreducible component was created by clearing D². Surjectivity of T gives the same argument directly in matrix space, including matrices with zero numerator.

## 2. Canonical Jacobian condition

On an affine chart of the smooth embedded curve, its ideal has d-1 locally independent normal equations. Inside the product with a matrix chart, adjoining F_N(t)=0 gives the local ideal of the correspondence, since the latter is the smooth hyperplane incidence just identified. When derivatives are taken only in curve-ambient variables, the normal equations contribute rank d-1. The last equation increases the rank by one exactly when its tangent derivative F_N'(t) is nonzero. This proves the threshold rank<=d-1 if and only if F_N=F_N'=0.

There is no dependence on a special global generating set: different sets generating the same local ideal have differential spans equal at a common zero, also after restricting those differentials to the curve-variable directions. In homogeneous coordinates, the radial vector lies in the kernel; in a chart with a nonzero coordinate, Euler's relation makes the removed homogeneous column a linear combination of the remaining ones. Dehomogenization therefore preserves the rank relevant to the threshold. Changes of coordinate or local trivialization multiply the tangent derivative condition by a unit on F_N=0. This checks infinity, isotropic points, and F_N identically zero.

The proof is consequently computing the exact set B of the canonical problem, rather than a set that only agrees away from an unexamined exceptional locus.

## 3. Exact isotropic image

At a simple zero r of D, put s=t-r and impose N(r)=0. Direct expansion gives

`N'D-ND' = (n_2 d_1-n_1 d_2)s²+O(s³)`.

The constant and linear coefficients cancel. Since F_N(r)=-d_1 n_0, the ramification equations at r are equivalent to the single linear condition N(r)=0; the tangent derivative then vanishes automatically. This proves exact equality of the isotropic image with the union of the evaluation hyperplanes, not just containment at generic parameters.

Evaluation at two distinct projective points is not proportional on the full binary-form space: interpolation supplies a section zero at one and nonzero at the other. The m hyperplanes are therefore distinct. A reduced union of distinct hyperplanes has degree m, giving the first target already at this stage.

## 4. Nonisotropic image and generic root patterns

At p with D(p) nonzero, division by D is invertible on jets. Prescribing the entire 2-jet of N therefore proves independence of f'(p)=0 and f''(p)=0. There are m+1 numerator vector coordinates, so the two independent equations give a projective fiber of dimension m-2. The incidence Y over the one-dimensional open set U is irreducible of dimension m-1.

The only numerator with identically vanishing Wronskian is a scalar multiple of D, since the rational function N/D then has zero derivative in characteristic zero. All other numerator fibers of Y are finite. The exhibited numerator with a zero of order exactly three at a nonisotropic point is not proportional to D and belongs to Y. Thus a nonempty open subset of Y has zero-dimensional fibers, and the image closure S has dimension m-1. It is an irreducible hypersurface in P^m. The exceptional numerator [D], with its one-dimensional fiber, does not change this dimension argument.

For each isotropic r, prescribing three zero jets at a distinct nonisotropic p and a nonzero value at r has total length four. Since m>=4, interpolation realizes this. Hence S is not L_r. This also ensures that a general point of any one of these irreducible hypersurfaces avoids all the others.

For m>=6, the triple-root exceptional incidence adds f'''(p)=0 to the two conditions defining Y. Length-four jet interpolation gives three independent linear conditions, so this incidence has dimension m-2. At two distinct nonisotropic points p,q, full 2-jets have total length six, and Hermite interpolation is valid for m>=5. The four derivative conditions are independent. The projective fiber dimension is m-4 and the pair parameter space has dimension two, again giving m-2. Image closures cannot increase dimension. Neither exceptional image can fill S, of dimension m-1. The argument uses the full projective line, with any needed coordinate chosen to avoid finitely many specified points, so infinity is included.

For m=4, the manuscript correctly avoids the unavailable interpolation bound. I independently expanded N=t³, D=1+t²+t⁴ to obtain

`F=t²(3+t²-t⁴)`.

Zero is exactly double. The quadratic 3+u-u² has discriminant 13 and nonzero constant term, giving two distinct nonzero roots, hence four distinct nonzero t-roots. The degree-six coefficient is -1, so infinity is not a root. No isotropic point is a root because -r³D'(r) is nonzero there. The bad projective loci of a triple root or two distinct double roots have the closed parametrizations stated in the proof; coinciding double-root factors yield fourth-order roots, already bad. Thus this example belongs to a nonempty open subset of the irreducible S on which exactly one double root occurs. Its being nonisotropic also persists after removing the finitely many L_r. This proves the required generic pattern in the smallest case.

For a general numerator on L_r, avoiding S and all other L_r' excludes every additional multiple root and every other isotropic root. In the local expansion the coefficient n_2 d_1-n_1 d_2 is not identically zero on L_r: take n_1=0,n_2=1 using length-three interpolation. Thus the remaining root at r is generically exactly double. Both Lemmas 4 and 5 are established without circular use of a reduced discriminant degree.

## 5. Support, multiplicity, and degree

The degree-k binary discriminant, k=2m-2, vanishes precisely when the binary form has a multiple projective root, with the zero form included. The ramification identification partitions this support into S and the m isotropic hyperplanes. S lies in the discriminant because the latter is closed and contains the image whose closure defines S. Conversely every multiple root is either isotropic or nonisotropic, and the zero form already comes from N=cD and is in the stated incidences. Thus equation (7) is an exact support statement. The union is a proper finite union of hypersurfaces, so the restricted discriminant is not identically zero.

The universal discriminant is homogeneous of degree 2k-2 in the binary coefficients. Composing with a homogeneous linear map either gives zero identically or a homogeneous polynomial of the same degree. The previous nonvanishing excludes the first case. Hence the pulled-back polynomial has degree 4m-6. This assertion alone would not give a reduced degree, and the proof correctly does not stop there.

I checked Lemma 6 by factoring off simple roots locally. With the double root moved to zero, the remaining quadratic is t²+ut+v, and the other roots and leading coefficient contribute an analytic unit to the discriminant. At u=v=0, its differential is a nonzero multiple of dv. Evaluation of the whole polynomial at zero also has differential a nonzero multiple of dv. Thus the discriminant tangent functional is nonzero scalar times evaluation of the polynomial perturbation at the double root.

Pulling this differential back to numerator coefficients gives `D(p) dotN'(p)-D'(p) dotN(p)` for the nonisotropic component. Since D(p) is nonzero and first jets are free, this functional is nonzero. For an isotropic component it is `-D'(r) dotN(r)`, again nonzero. A radial numerator perturbation is proportional to F_N and evaluates to zero at the root, so the nonzero functional descends to projective tangent directions; it is not an artifact of affine scaling.

As an additional independent check in the smallest nonisotropic example, perturb N=t³ by epsilon*t. The Wronskian perturbation is epsilon*(1-t²-3t⁴), whose value at the double root zero is epsilon. This explicitly supplies the transverse direction asserted abstractly. At any isotropic root, a numerator perturbation with nonzero value there gives the corresponding transverse direction.

At a general point of each component, Lemmas 4–5 ensure no other component passes through that point and the discriminant differential just computed is nonzero. A polynomial vanishing to exponent at least two along that component would have zero differential there. Hence every irreducible factor has exponent exactly one. Over the complex polynomial ring, equality of the zero sets and unique factorization now give

`Delta = nonzero_constant * G * product_{r in Z} N(r)`

with G an irreducible reduced equation of S. There are no hidden factors supported only in higher codimension. Degree subtraction is now justified and gives deg(S)=(4m-6)-m=3m-6=6(d-1).

## 6. Matrix pullback and exceptional numerators

The proof correctly avoids relying on the projective rational map H -> [N_H] at its indeterminacy locus. A linear splitting of the surjective affine map T identifies the matrix vector space with V times ker(T). Pullback adjoins polynomial variables, preserves irreducibility of G, preserves distinctness of evaluation linear forms, and preserves all nonzero homogeneous degrees. The kernel dimension is d(d-1)/2; in particular the issue already exists for d=2 and cannot simply be ignored.

In the splitting, preimages of affine numerator sets are products with the kernel. Taking closure commutes with this product. At nonzero matrices H with T(H)=0, the original quotient is identically zero off the isotropic set. Their full parameter-line fibers lie in the correspondence and ramification locus; both isotropic and nonisotropic subsets of the parameter line are nonempty. Thus these matrix points belong to both images, exactly as the pulled-back equations require. Nonzero numerators cD give the same conclusion for constant quotients. Such parameters are already contained in the cones and do not introduce extra irreducible components or degree contributions.

## Disposition and limitations

All essential claims, dimension counts, exceptional degrees, projective roots, and multiplicity assertions have been checked. The argument proves an all-order theorem; the proof does not use a numerical experiment or a finite symbolic sample to infer the general result. The complete source supports an affirmative resolution of both parts of TR-26 together.

The simple-root denominator and the surjectivity onto all degree-m numerators are material hypotheses, verified for this exact canonical embedding. No conclusion is certified here for weighted embeddings, repeated denominator roots, other projective varieties, real connected components of the complement, or historical novelty. No original source or canonical file was edited in this audit.

**Final verdict: PASS — full canonical target established, including reduced multiplicities.**
