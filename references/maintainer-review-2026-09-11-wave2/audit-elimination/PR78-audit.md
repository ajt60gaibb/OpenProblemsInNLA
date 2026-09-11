# Independent audit of PR #78

Frozen head: `c1cdd202d23c7386451b7d81084999f3a4f90171`.
Snapshot: `/private/tmp/nla-review-wave2-artifacts/pr-78`.
Comparison statements: the original `origin/main` tree in `/private/tmp/nla-review-wave2-20260911`.

## Verdict

**PASS for all eight claimed exact catalog resolutions:** IE-13, IE-14, IE-17, IE-18, IE-19, IE-21, IE-22, IE-23. I independently read every full proof, derived the key inequalities and quantitative estimates, checked the source conventions, and recomputed the finite certificates. No substantive mathematical gap was found. This is independent mathematical review, not formal proof-assistant certification, external peer review, or verification of novelty/priority.

The separate order-five rook example is valid supplementary evidence. By itself it settles neither of IE-15's requested constants and therefore does not justify changing IE-15 from Open. PR #78 correctly leaves that status Open. PR #83 separately proves both requested constants; see the companion report and integration instruction below.

The submitted manuscripts contain historical reconstruction notices. Their assertion that current canonical identifiers or sources were unavailable describes the original reconstruction, not this audit. I checked the actual current mapping and statements rather than accepting provisional labels or attached PASS reports. `canonical-target-comparison.json` records that every changed target's original heading and complete mathematical/reference tail are preserved verbatim. All seven authored TeX manuscript bodies, from their first mathematical section through `\end{document}`, match the supplied TeX bodies; only the wrapper and trailing comment differ.

## Primary source comparison

I read Higham's actual [second-edition book, printed p. 193, Problems 9.15 and 9.18](https://pages.stat.wisc.edu/~bwu62/771/hingham2002.pdf). Problem 9.15 requests sharp partial-pivoting growth for unequal bandwidths and for the tridiagonal pattern with both opposite corners. Problem 9.18 requests small-order rook constants and general lower bounds. These agree with the precise catalog formulations, including the supplementary relevance of an order-five example. The old numerical rook lower bounds are not claimed exact constants.

I read [Fong–Saunders, Sections 6.1–6.2 and Figure 7.5](https://web.stanford.edu/group/SOL/software/lsmr/LSMR-SISC-2011.pdf). The specified projected least-squares approximation is the same quantity, and its claimed empirical LSMR monotonicity is explicitly discussed. The paper says its default matrix norm is usually Frobenius; therefore the submitted proof must be described as settling the catalog's explicit spectral-norm perturbation definition. The updated IE-17 notice already makes this qualification. The dissertation PDF endpoint failed in both the browser reader and a direct fetch here, so I do not claim to have independently read its Section 7.2.1 during this review.

I read [Krzysik–De Sterck–Smith, version 4](https://arxiv.org/html/2312.04776v4), especially the two-step map, four-step matrix (16), two-eigenvector formula, and Conjecture 10/(27). The catalog asks for the finite-step norm maximum, matching the submitted counterexample. The separate orbit/asymptotic conjectures are not settled by one-step amplification evidence.

I read [Hillar–Lin–Wibisono](https://arxiv.org/pdf/1203.6812), the opening ordering convention and Conjecture 8.1 on printed p. 17. The conjecture itself uses entrywise upper bounds, despite adjacent motivation about dominance margins. The counterexample addresses that actual entrywise statement. I also read [Steinerberger, Section 2.3](https://arxiv.org/pdf/2107.05554): both the spherical random limit and the uniform all-unit-row constant are asked there. Finally, [Dokmanić–Gribonval's author manuscript](https://dokmanic.ece.illinois.edu/assets/pdf/DokmanicG17aa.pdf), Example 4.1 and Corollary 4.2/Remark 4.1, confirms the small matrix attribution and distinguishes the direct inverse norm from the product objective.

## IE-13: all unequal bandwidths

Source: `references/colbrook-recovered-2026-09-11/submitted/proofs/IE-13.md`, especially lines 30–58 and 60–97. The result is `G(0,q)=1`; for p>=1, `G(p,q)=h_(p+q)` with h_t=0 for t<=0 and h_t=1+sum_(r=1)^p h_(t-r). It includes p>=1,q=0, all unequal pairs, complex inputs, and all admissible ties.

The sorted-front comparison is sound. If sorted magnitudes y_1>=...>=y_(p+1) lose entry y_a, the sorted triangle-inequality envelopes of the survivors are y_a+y_i with i!=a. For i<a, the inequality needed to compare with y_1+y_(i+1) follows because y_i-y_(i+1)<=y_1-y_a; for i>=a the bound is immediate. Thus removing the largest target-column magnitude gives a valid upper envelope, without assuming that the actual GEPP pivot is selected using that target column.

At stage k, any original row with label at least k+p has zero entries in the previous pivot columns and remains unchanged. It cannot have been selected as a nonzero earlier pivot. This leaves at most p old rows plus one newly accessible row. For a target column j, its first nonzero fresh arrival is stage j-(p+q) when j>=p+q+1. Exactly p+q updates precede elimination of column j. For smaller j the initial old entries are dominated by the all-ones state from one imaginary envelope update, yielding h_j<=h_(p+q). Untouched entries, recorded pivot-row entries, and the truncated front near the matrix bottom are all covered. The p=0 triangular case has zero multipliers.

I independently checked the stated closed forms and the attaining construction's support. The early columns built from L_0 u^(k), after the displayed row-label assignment, occupy only original rows k through k+p; the target column begins at j-q=p+1 and ends at j+p=n. All entries have magnitude <=1. The row order is an admissible sequence of actual GEPP choices: active column k is the pivot times a column of L_0, whose multipliers are 0 or -1. It is not an unauthorized preliminary permutation. The target forward recurrence gives u_i=h_(i-1) for i>=2, and the target pivot equals h_(p+q). Subsequent identity columns and nonzero leading pivots establish nonsingularity. The example order 2p+q+1 is within the canonical allowed range.

## IE-14: cyclic tridiagonal matrices

Source: `submitted/proofs/IE-14.md`, lines 19–73. **The sharp value is c_n=F_(n+1)+1 for every n>=4.**

The two-old-row front contains original labels from the already reached ordinary rows plus the last row. One fresh ordinary row arrives per stage; all other rows have zero previous columns. When its target value is zero, the survivor envelope is `(a+b,a)`. With a fresh value c the sum of the two survivors is at most a+b+c+max(a,b,c), regardless of which front row actually pivots. Both arguments use only multiplier moduli <=1 and hence cover complex matrices.

For the last column, initial old bounds (1,1) followed by n-3 zero arrivals give Fibonacci bounds. The first nonzero late arrival gives total `2F_(n-1)+F_(n-2)+1=F_(n+1)+1`, bounding the final update. I separately checked every other column history: column 1 is initial only; column 2 and the interior columns are bounded by two; column n-1 obeys the stated `F_(n-1)+1` bound. The n=4 edge case uses F_1=1,F_0=0 correctly. Thus this is a bound for every active entry, not just the last pivot.

The L/U construction has unit lower multipliers on its first two subdiagonals, with negative signs; the half entries in the first two U columns enforce the required original pattern under row order `(1,n,2,...,n-1)`. Its final column before row reassignment is `(1,1,0,...,0,1)`, so only allowed rows 1,n-1,n receive nonzeros. Both required corner entries are nonzero. Nonzero diagonal U entries establish nonsingularity; the multiplier bounds establish every selected GEPP pivot, including ties. The attained final pivot is exactly the claimed Fibonacci value.

## IE-17: LSMR backward-error increases

Source: `submitted/proofs/IE-17.md`, lines 5–49, 54–99, 101–174. **Both catalog sequences fail monotonicity on the same full-column-rank 4-by-3 example.** The result concerns matrix-only spectral perturbations with b fixed.

I reconstructed the two iterates from the normal equations for minimizing `||g-Hx||` over span(g,...,H^(k-1)g), independently of their printed values. They are the displayed x_1 and x_2; the normal-equation design has full column rank. Hence neither a minimum-length ambiguity nor early termination affects the counterexample.

For the lower certificate, let u be the unit direction of a nonzero residual of a feasible perturbed problem. Orthogonality gives `(A+E)^T u=0` and `Ex=r-u u^T b`. The two necessary norm bounds are u^T C u and u^T D u. Their convex combination is at least the smallest eigenvalue of tC+(1-t)D. If the new residual is zero, the separate argument using a vector in ker(A^T) is valid because m>n, so this branch has not been omitted.

For the upper certificate, the prescribed row E^T u and column E e have the same scalar intersection d. Their strict squared norms below kappa imply kappa-d^2>0. The displayed rank-two completion factors as two contractions and a two-dimensional orthogonal matrix. Its prescriptions imply perturbed normal-equation feasibility, so it proves an actual upper bound, not merely a necessary condition.

My independent rational calculation verified the explicit completion's normal equations and positive leading principal minors of kappa I-E^T E. At x_2, all leading principal minors of `(5/6)C+(1/6)D-(99/100)I` are strictly positive. This proves

    mu(x_1)^2 <= 1979/2000 < 99/100 < mu(x_2)^2.

The projection formula for the approximation follows by inverting K^T K and yields both printed exact rational values. Independent cross multiplication gives `tilde_mu(x_1)^2 < 1.006 < 1.007 < tilde_mu(x_2)^2`. The dense Hadamard variant scales both errors by two without changing the iterates. No conclusion for a Frobenius perturbation norm is needed or inferred.

## IE-18: finite-step Anderson assertion

Source: `submitted/proofs/IE-18.md`, lines 5–107. **The exact four-step identity is false, even for positive-definite contractions with positive-definite I-M.**

For M=diag(1/10,1/2,3/5), v=(1,1,1), direct rational evaluation gives the displayed intermediate vectors and squared norm ratio `1920682/21289638243`. The largest pair expression is 1/121 as a norm amplification, so the required squared comparison is against 1/14641. The strict rational inequality is correct; there is no missing square or square root. All denominators are positive on this example. The semidefinite second example also satisfies the canonical assumptions.

I independently differentiated the analytic family M_e=diag(e^2,1/2,1/2+e). At zero, alpha=4/3, alpha'=2/9, the second coefficient beta=2, beta'=2, and the second residual derivative is `(0,-1/12,1/12)`. The numerator and denominator defining beta are nonzero at the expansion point. Consequently actual amplification is `e/(6sqrt(6))+O(e^2)`. The middle eigenvalue pair contributes `e^2/4+O(e^3)`, and the remaining pairs are O(e^4). Thus the ratio diverges as stated. The claim is a failure of a uniform finite-step bound, not an assertion that every such transient amplifies along an asymptotic orbit.

## IE-19: entrywise upper bounds and inverse norm

Source: `submitted/proofs/IE-19.md`, lines 5–60. **The canonical inequality is false; the stated replacement infimum is correct.**

For n=3,m=alpha=1, the displayed J has diagonal 2 and off-diagonal 1/2, satisfies all strict-positivity, entrywise-bound and diagonal-dominance assumptions, and has inverse infinity norm 7/9. The comparison S has inverse infinity norm 5/4. The original source's order convention is entrywise, so replacing it by Loewner order or by bounds on dominance margins would change the question.

For the replacement, the quadratic-form decomposition has nonnegative terms and forces x_i+x_j=0 for every pair in its nullspace. With n>=3 and positive off-diagonals, this forces x=0, establishing positive definiteness. Cauchy–Schwarz gives `(J^-1)_ii >= 1/J_ii`, strictly because e_i cannot be an eigenvector with nonzero off-diagonal column entries. Thus every admissible norm exceeds 1/(alpha+m). The family with fixed diagonal D=alpha+m and off-diagonal epsilon belongs to the class for every 0<epsilon<=m; its explicitly inverted norm tends to 1/D. The claimed formula, gap, and nonattainment all check out.

## IE-21 and IE-22: random limit and uniform optimum

Source: `submitted/proofs/IE-21-22.md`, lines 5–213. **Both exact quantifier statements are proved**, including a quantitative random estimate and an upper bound uniform over every m>=1.

The variational minimum is zero when the retained map is rank deficient. This convention, the floor k=floor(theta m), and k=0 are all handled. Interchanging finite row-subset minimization and compact direction minimization is legitimate. The threshold expression for the sum of the k smallest nonnegative values is an exact piecewise-linear identity. The population trimmed functional is 1-Lipschitz under L1 coupling by conditional expectation of feasible selectors.

For a fixed direction, Y=n u_1^2 has mean one and continuous law for n>=2. Its theta-quantile b is at most 1/(1-theta). Hoeffding controls both the number and sum below b, while the event that at least k samples fall below L=2/(1-theta) is controlled separately. The replacement argument changes at most m epsilon+1 terms, each bounded by L, proving the quoted pointwise tail bound. No upper bound n is used that would ruin the asymptotic.

The spherical moment bound gives `E|Y-1|^r <= 4^r r!`; summing its centered exponential series for |lambda|<=1/8 gives the stated 32lambda^2 bound. Chernoff and a 1/4-net give the covariance tail `2*9^n exp(-m t^2/512)`. On the covariance event, each retained quadratic form has norm at most 1+t, so their minimum is `2(1+t)`-Lipschitz on the unit sphere. The fine-net union bound for the trimmed form follows without assuming differentiability of that minimum.

Coupling a uniform direction with an independent chi-square radius yields `E|Y-G^2| <= sqrt(2/n)` exactly as used. With Q=m/n and `t=epsilon=delta=32sqrt(log Q/Q)`, all parameter restrictions eventually hold for every diverging Q. The covariance exponent is `n log9-2n logQ`; the trimmed net exponent is dominated by `-2048n logQ`. Both tend to minus infinity with no extra relation between n and Q. The error tends to zero, proving both covariance normalization and the requested random ratio limit. The stated quantitative error follows.

For the deterministic upper bound, remove r largest covariance eigendirections. The remaining matrix B has `||B||^2<=m/(r+1)` and row norms <=1. Its correlated Gaussian projections are not assumed independent. Each individual variance <=1 gives `E Psi_t<=h_theta`; Gaussian Poincare gives `Var(Psi_t)<=4t/(r+1)` using the gradient bound and the projected operator norm. The nonsmooth hinges are Lipschitz, so the cited smooth-approximation argument applies.

Chebyshev on a threshold grid makes this expectation bound simultaneous with positive probability. A separate quadratic-form variance bound ensures the average squared projection Z<=2. This forces the kth order statistic below L, so the trimming supremum outside the finite grid interval cannot invalidate the argument. The chi-square norm lower bound permits normalization to a unit direction. The resulting inequality

    (n/m) s_theta(A)^2 <= n/[(n-r)(1-delta)] * (h_theta+2delta)

holds for some direction for every input matrix, provided the three explicit failure estimates sum below one. Choosing r=floor(n^(2/3)), delta=n^(-1/6) makes this true for all sufficiently large n, independently of m and A. The leading failure term is O_theta(n^(-1/6)). Hence the uniform squared-error remainder is of that order. The random theorem supplies matching deterministic realizations along every high-aspect-ratio sequence, establishing the stated supremum and eventual-uniform optimality quantifiers. There is no unjustified interchange of minimum and expectation.

## IE-23: induced-norm minimizer nonuniqueness

Source: `submitted/proofs/IE-23.md`, lines 5–75. **The direct-inverse uniqueness claim is false for every 2<p<infinity; the stronger minimizer descriptions are also correct.**

Every right inverse B+N of A has B^*N=0 for B=A-dagger, hence squared outputs add pointwise. This proves B's minimality while allowing another inverse to tie the maximal norm. The displayed 2-by-3 example has B^*B<=I and X^*X=I. The sharp l_p-to-l_2 vector inequality gives the common upper bound, attained at the flat vector (1,-1). This works over both real and complex fields.

For all minimizers, testing that norming vector forces the kernel perturbation to annihilate it, leaving N=t(-1,1,1)^T(1,1). The other flat vector bounds |t|<=1/3, which is also sufficient from the Gram eigenvalues. For the higher-dimensional complex family, the nonconstant Fourier vectors are flat norming vectors and span 1-perp. Thus every optimal N equals u 1^*, and the remaining flat direction forces `||u||<=1/sqrt(m+1)`. Its Gram formula proves sufficiency. The m=1 case is uniquely minimized by Euclidean orthogonality, so 2-by-3 really is the smallest size. The source explicitly already contains the small matrix for a spectral-norm example; its attribution is appropriate, and no claim about the separate product objective is inferred.

## Exact checks, PDF QA, and integration

I read `submitted/verification/exact.py`, `checks.py`, and `rook_partial.py` before loading their functions. The rerun writes only `audit-elimination/reviewed-script-rerun.json`, not the frozen source. All finite certificates pass, including 60 band witnesses and 27 cyclic witnesses. Separately, `independent_checks.py` reimplements elimination using SymPy, derives the LSMR iterates/certificates from their defining systems, differentiates the Anderson family symbolically, and checks both rook constructions and the order-five example. Its output is `independent-check-results.json`. These are supporting finite/symbolic checks; the universal proof review is the reasoning above.

All 20 pages of the seven authored manuscript PDFs and all 18 pages of PR #78's nine changed canonical PDFs were rendered and visually inspected. The seven-page PR #83 proof and its two-page canonical PDF were also inspected, giving 47 pages total. No clipped text, missing formula, overlap, missing-glyph block, or other acceptance-blocking rendering problem was found. Some final reference pages are sparse. The full PDF inventory, extracted text and six page contact sheets are in `pdf-qa/`.

**Integration requirement:** retain IE-15 at its permanent existing path. Once #83 is accepted, use its Solved status and its exact order-three/order-four theorem. Retain #78's order-five construction as separate supplementary evidence, but revise its present-tense sentence “IE-15 remains Open” (`linear-systems-and-elimination/IE-15/README.md:15`) to historical wording. The original target stays unchanged, and the order-five lower bound does not acquire a claim of optimality.


Archival note: local snapshot and runtime paths identify the audit environment. This published record includes review prose, independent check sources and JSON results; transient PDF page images, build trees and copied contributor inputs remain in the local audit archive. The original submissions are identified by the frozen Git commits above.
