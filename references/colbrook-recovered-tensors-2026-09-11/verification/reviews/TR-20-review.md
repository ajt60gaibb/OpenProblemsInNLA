# Independent full review: recovered TR-20 manuscript

Review date: 2026-09-11.

**Verdict: PASS for both complete canonical formulas, for every integer \(n\ge2\).** The proof establishes degrees of the reduced nonisotropic hypersurfaces, including generic multiplicity one and generic injectivity of the ramification projection. It is not merely a finite calculation or an unreduced discriminant-degree computation. No mathematical source correction is required by this review.

The manuscript's additional coefficient formula for arbitrary \(m,n\ge2\), and its irreducibility assertion, are supported by the same argument. Subject to the maintainer's overall acceptance process, the mathematical status recommendation for canonical TR-20 is **Solved**, retaining the original ID, canonical path, and both formulas as a single target. No case of either canonical family remains outstanding.

This reviewer did not develop or edit the recovered manuscript. The complete source, including its preamble and references, and the complete diagnostic program were read before execution. There are no external TeX inputs or includes.

## Exact reviewed files

Normalization for these SHA-256 values: read the entire file as UTF-8, replace CRLF by LF, re-encode as UTF-8, with no trimming or any other transformation.

| File | Complete normalized SHA-256 |
| --- | --- |
| .cache/tensor-recovered/tensor_recovered/manuscripts/TR-20/main.tex | 0f30945c0c03fdbff263a2c5f9e9045b3586c92ce6ecaa8675d2700e86cf1f49 |
| .cache/tensor-recovered/tensor_recovered/code/verify_tr20.py | 32bfa238c1f2d561891c83e8d0d9d3af6d1b26aa930cf35f482af58c3b23f0ed |

The diagnostic JSON in this review directory independently records these hashes. Verdict scope is tied to these complete sources.

## Canonical target and primary references

Read the full canonical tensor-computations/TR-20/README.md. The manuscript uses the same ordinary Segre entry coordinates, complex symmetric matrix parameters, bilinear transpose, exclusion of the denominator-zero set, Hessian degeneracy at a critical point, and reduced projective degree.

The two requested conclusions are
\[
 \deg\Delta^{\mathrm{ni}}_{2,n}=24\binom{n+1}{3},\qquad
 \deg\Delta^{\mathrm{ni}}_{3,n}=24n^2\binom n2,\qquad n\ge2.
\]
They match [Borovik–Friedman–Hoşten–Pfeffer, v2, Conjecture 3.18](https://arxiv.org/html/2512.06939v2), with the nonisotropic definition in §3.2. The paper's example for two projective lines gives nonisotropic degree 24, agreeing with the smallest case here. That paper's conjecture and examples are target identification and consistency evidence, not a substitute for this manuscript's proof.

Also checked [Salizzoni–Sodomaco–Weigert, Corollary 5.3](https://arxiv.org/html/2510.17760v1). Substituting projective dimensions \(m-1,n-1\) into its \(\omega=2\) formula gives exactly the generic critical-point count used by the diagnostic. That count is an independent consistency check; it does not determine the discriminant degree.

## 1. Parameter reduction and logarithmic section

**PASS:** Section 1 and Theorem 1 (label thm:general, lines 66 onward).

Products of Segre coordinates span every bidegree-\((2,2)\) monomial. Thus the linear map from symmetric matrices to \(S=H^0(\mathcal O(2,2))\) is surjective. Pullback of an irreducible reduced equation through a surjective linear map amounts to adjoining unused independent variables, preserving irreducibility, reducedness and degree. The projective kernel is correctly treated as the vertex of the cone, not omitted from the parameter set.

The two isotropic factors are smooth divisors meeting transversely. When \(m=2\) or \(n=2\), the corresponding quadric consists of two disjoint points; its product divisor is still smooth as a possibly disconnected scheme. This is not a repeated divisor. The logarithmic cotangent sheaf is therefore locally free.

The section \(\omega_P=dP-P\,d\log Q\) has the stated frame transformation and is global in \(\Omega_X^1(\log D)\otimes L\). On \(U\), it equals \(q\,d(P/Q)\). At a critical point multiplication by \(q\ne0\) does not change Hessian singularity. This makes the nonisotropic ramification condition exactly the canonical condition.

## 2. Jets, the compactification, and a general pencil

**PASS:** Lemma 2 (lem:jets, line 125), Lemma 3 (lem:incidence, line 155), and the paragraph choosing a general line.

Bidegree \((2,2)\) sections contain every local monomial of total degree at most two. Arbitrary value, gradient and symmetric Hessian can consequently be prescribed at every point. This claim is only two-jet spanning, and the later proof does not incorrectly upgrade it to full three-jet spanning.

The local logarithmic components have ranks \(k\) away from the crossing and \(k-1\) at the crossing, exactly as calculated. Their vanishing imposes \(p=p_z=0\) on one boundary divisor and the same \(k-1\) conditions on the codimension-two crossing. Both boundary incidence strata have dimension \(M-1\).

A component of the zero scheme of \(k\) equations in a smooth ambient space of dimension \(M+k\) has dimension at least \(M\). Thus no component can be confined to either boundary stratum. The open incidence is a smooth irreducible kernel-bundle projectivization of dimension \(M\); its closure is the sole underlying component. Correct codimension in a regular ambient space makes the local equations a regular sequence. The resulting Cohen–Macaulay scheme has no embedded components and, being generically reduced, is reduced.

At a crossing the missing differential is \(p_u\,du-p_v\,dv\). The only singular points have \(p_u=p_v=0\), two further independent jet constraints. Hence their locus has dimension at most \(M-3\).

A prescribed nonsingular Hessian gives an incidence point at which the projection differential is an isomorphism. This proves dominance, and equal dimensions give generic finiteness. Since the projection is proper, its non-quasi-finite locus is closed; its dimension is at most \(M-1\), and its image has dimension at most \(M-2\) because its fibers are positive dimensional. A general parameter line avoids this image and the singular image.

The successive pullbacks of general hyperplanes form a basepoint-free system. Characteristic-zero Bertini on the smooth locus, together with avoidance of the singular image, gives the required smooth projective curve. It is finite over the line. Irreducibility or connectedness of this curve is unnecessary for the summed adjunction and Riemann–Hurwitz computation.

## 3. Total ramification

**PASS:** Section 3, equations curveclass and Rtotal (lines 212–232).

For a rank-\(k\) bundle on \(X\times\mathbb P^1\),
\[
 c_k(E\boxtimes\mathcal O(1))=c_k(E)+h\,c_{k-1}(E)
\]
because \(h^2=0\). The determinant of this bundle contributes \(c_1(E)+kh\), and the ambient canonical bundle contributes \(K_X-2h\). Therefore adjunction gives
\[
 K_C=(K_X+c_1(E)+(k-2)h)|_C.
\]
Adding \(2\deg\pi_C\) and using \(c_1(E)=K_X+(k+1)\ell\) yields exactly
\[
 R_{\rm tot}=\int_X(2K_X+(k+1)\ell)c_{k-1}(E)+k\,c_k(E).
\]
The coefficient \(k\) of \(c_k(E)\), including the base contribution, is correct. This is total ramification with multiplicities, prior to any reduced-image interpretation.

## 4. Boundary contributions

**PASS:** Lemma 4 (lem:boundary, line 238).

On a single boundary divisor, eliminate the tangential critical equations using their nonsingular Hessian. The remaining local equation is
\[
 -Bs+\tfrac12\beta u^2+\text{higher terms}=0.
\]
The parameter direction \(B\ne0\) is available by free value evaluation and a transverse general pencil. The Schur complement \(\beta\ne0\) is a free, nonidentically vanishing second-jet condition. Thus the map has local ramification index two and ramification multiplicity one.

At a crossing, with \(p_u=A\ne0,p_v=B\ne0\), the derivative in the point variables has the displayed block matrix. Its determinant is \(-AB\det H\ne0\); the projection is unramified. For \(k=2\), the tangential block is empty, with determinant one. This explicitly handles \(m=n=2\).

Failure of one of the required boundary inequalities adds a proper jet condition to an incidence of dimension \(M-1\), so its parameter image has dimension at most \(M-2\). A general line avoids it.

Zeros of the first jet of \(P|_{D_i}\) count the single-boundary points. The relevant bundle has rank \(k\) on \(D_i\times\mathbb P^1\), whose dimension is \(k\); expansion of its top Chern class gives the stated integral of \(c_{k-1}(J^1(L|_{D_i}))\). Ambient jet spanning restricts to jet spanning on each smooth divisor. On the crossing, the first-jet condition on either divisor imposes an extra normal derivative beyond the crossing incidence, so these special zeros have parameter codimension at least two. The two jet counts therefore contain no crossing contribution on a general pencil.

Disconnected quadric divisors are counted by integration over all components. There is no missing factor of two and no subtraction of ramification at the unramified crossings.

## 5. Reduced hypersurface and generic degree one

**PASS:** Lemma 5 (lem:ordinary, line 302), Lemma 6 (lem:recover, line 345), Proposition 7 (prop:birational, line 384).

After the gradient is set to zero, two-jet spanning still permits every symmetric Hessian. The symmetric determinant variety is irreducible and reduced; its rank-\((k-1)\) locus is dense. Its pullback through the surjective Hessian map remains irreducible, so the ramification divisor over \(U\) is irreducible.

A general Hessian kernel has nonzero tangent components in both projective factors. Orthogonal changes of coordinates can move every nonisotropic point to the chosen origin while preserving \(Q\). The mixed monomials \(u_i^2v_j\) and \(u_iv_j^2\) have zero two-jet but a nonzero third directional derivative for suitable indices whenever both kernel components are nonzero. They suffice to vary the needed third derivative. Full three-jet spanning, which would be false for \(\mathcal O(2,2)\), is not assumed.

Eliminating the nonsingular Hessian block gives a scalar critical equation with nonzero second derivative in the kernel variable and a free parameter derivative. This is a simple fold. In particular, the image is a hypersurface and local ramification multiplicity is one.

The normal-recovery argument establishes the essential global generic-degree assertion. The tensor
\[
 N_{\xi,w}=U_a\otimes B+A\otimes U_b
\]
has flattening rank two and determines the spaces \(\operatorname{Span}(A,U_a)\) and \(\operatorname{Span}(B,U_b)\). Each space has precisely one rank-one direction. Indeed, a combination with nonzero tangent coefficient has the \(2\times2\) coefficient matrix
\(\left(\begin{smallmatrix}\alpha&\beta\\\beta&0\end{smallmatrix}\right)\), with determinant \(-\beta^2\ne0\). Embedding that matrix by the two independent vectors preserves rank, also over \(\mathbb C\), regardless of whether their bilinear Gram matrix is nonsingular. This recovers both underlying projective points.

At a fold this tensor is the normal to the image tangent hyperplane, by linearizing the critical equations. At a general smooth image point every ramification preimage is an ordinary fold with a mixed kernel: the excluded subset is proper in a divisor of dimension \(M-1\), as is its boundary in the compactification, so these images have dimension at most \(M-2\). All preimages give the same projective normal. Recovery forces their points \(\xi\) to coincide. Therefore the generic projection degree is one.

The normal on a boundary first-jet discriminant has flattening rank one, further distinguishing its components from the rank-two normal of the nonisotropic hypersurface. The subtraction counts ramification points, including any boundary projection multiplicities, rather than assuming their degrees without justification.

Consequently the general pencil's remaining simple folds count precisely the degree of the reduced nonisotropic image:
\[
 \deg\Delta^{\rm ni}_{m,n}=R_{\rm tot}-\delta_a-\delta_b.
\]

## 6. Chern classes and the two all-order extractions

**PASS:** Sections 6–7, lines 428–523.

The logarithmic residue sequence yields
\[
 c(F)=\frac{(1-x)^m(1-y)^n}{(1-2x)(1-2y)}.
\]
The twisting formulas for \(c_k(E)\) and \(c_{k-1}(E)\) have the displayed coefficients \(1\) and \(k-i\). The first-jet sequence gives the coefficient \(k-i\) in \(c_{k-1}(J^1L)\) as well. The conormal sequence on \(D_a\) cancels the factor \(1-2x\), leaving \(c(F)(1-2y)|_{D_a}\), and conversely for \(D_b\). Pushing by their classes \(2x,2y\) yields the two \(-4xyT_0\) terms. Their sum explains the \(+8xy\) correction in the final numerator.

Combining terms gives exactly
\[
 [x^{m-1}y^{n-1}]
 \frac{(k-2mx-2ny+8xy)(1-x)^m(1-y)^n}
 {(1-2x)(1-2y)(1-2x-2y)^2}.
\]
All series are used only to the finite degrees surviving in the Chow ring.

The coefficient-substitution identity follows directly from the residue transformation \(y=z/(1+z)\); the Jacobian factor is \((1+z)^{-2}\), as stated. The \(x\) and \(x^2\) extractions and subsequent binomial identities are algebraic identities in \(n\). They establish both requested formulas for all integers \(n\ge2\), not by interpolation from numerical dimensions. The zero convention for binomial coefficients handles \(n=2,3\) correctly.

## 7. Inspected code and fresh diagnostics

The supplied program explicitly labels itself rebuilt during recovery and limits its role to arithmetic and local identities. That is an appropriate scope statement. Its polynomial dictionary operations use exact integers with the correct truncation \(x^m=y^n=0\). The independent direct expression and the Chern/adjunction/jet expression are compared before interpreting their result geometrically.

The unchanged script was copied to .cache/tensor-recovered/tr20-scratch/code/verify_tr20.py and executed there. Its output is .cache/tensor-recovered/tr20-scratch/evidence/TR-20.json. Exit code was zero, reporting:

- 63 Chern/direct coefficient comparisons, including symmetry and the independently sourced critical-point count.
- 98 additional cases of the two target families through \(n=50\).
- Symbolic verification of both coefficient extractions, both polynomial binomial identities, the single-boundary model, crossing determinant and normal-recovery local identities.

Separately, TR-20-diagnostics.json in this review directory records a fresh run of those inspected routines, the source hashes, and 99 additional integer checks of the displayed binomial identities for \(2\le n\le100\). No original package result was overwritten.

The smallest cases give:

| \((m,n)\) | Critical count | Total ramification | Boundary a | Boundary b | Nonisotropic degree |
| --- | ---: | ---: | ---: | ---: | ---: |
| (2,2) | 8 | 32 | 4 | 4 | 24 |
| (2,3) | 18 | 130 | 6 | 28 | 96 |
| (3,2) | 18 | 130 | 28 | 6 | 96 |
| (3,3) | 61 | 780 | 66 | 66 | 648 |

These diagnostics corroborate the arithmetic. The global proof audit above, especially the compactification, boundary and normal-recovery arguments, supplies the mathematical justification that finite code cannot supply.

## Final assessment

Both canonical formulas and their hypersurface assertions are established for every required \(n\ge2\). The proof also justifies the stated general coefficient formula and irreducibility for all \(m,n\ge2\). No substantive gap, unhandled low-dimensional case, hidden uniformity assumption, or multiplicity mismatch was found. No mathematical manuscript or canonical file was edited, and no novelty or external-referee certification is asserted.
