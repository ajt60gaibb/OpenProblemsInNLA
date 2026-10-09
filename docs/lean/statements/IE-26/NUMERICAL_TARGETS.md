# IE-26: exact mathematical and numerical specification

Author: OpenAI Codex AI agent /root/statement_design, 2026-09-28. This is a preimplementation specification; two independent approvals are required before Lean implementation. No Lean target, target proof or numerical certificate is supplied here.

Permanent ID IE-26; canonical path linear-systems-and-elimination/IE-26/README.md; campaign base 80c0e3e638b2f26dcb3a00353651fc3d2215dd65. Existing status is Solved. The entire original README, including both original bounds, attribution, resolution and historical audits, is preserved byte-for-byte in ORIGINAL.md. No canonical ID, path, statement or status is changed. There are no existing Lean files in this canonical problem directory at the campaign base.

## Bound complete sources

| Source | Raw-byte SHA-256 |
| --- | --- |
| linear-systems-and-elimination/IE-26/README.md | bf8d00fe55b44b5bbeeeebffd17de62ab9135684a2747d3a3a268574ef9529ea |
| linear-systems-and-elimination/IE-26/problem.tex | 2bb30c7ef2c43569a7cfb2e0024df6b276e8ef5eb818eda143a52b532851032a |
| linear-systems-and-elimination/IE-26/solution.md | e312eeb6a40b8f1d84030a9e2322637beb775d83caeb58d1acef78c0b995c7b3 |
| linear-systems-and-elimination/IE-26/solution.tex | 0b6c0d2d2a2a7f531cc318e2cab82a05e247479f0a2061b723f4034af74c4b82 |

## Both original targets and constant uniformity

The complete target is a conjunction of these two independently named propositions.

FirstBound: there exists one real C>0 such that for every natural N>=2, every real alpha with 0<alpha<1/2, and every permitted real shift vector s,
Lambda_N(s) <= C * ((N:Real)^(2*alpha)-1) / (alpha*(1-2*alpha)).

SecondBound: for every real alpha with 1/4<alpha<1/2 there exists a real C_alpha>0 such that for every natural N>=2 and every permitted real shift vector s,
Gamma_N(s) <= C_alpha * (N:Real)^(4*alpha-1).

C is chosen before alpha as well as N,s and is absolute. C_alpha is chosen after alpha but before N,s. All powers with real exponents are actual positive-base real powers; subtraction in 4*alpha-1 is real. Both inequalities are non-strict. No logarithmic factor is permitted in the second bound. The exact first numerator is N^(2*alpha)-1, and the full denominator is alpha*(1-2*alpha).

The first alpha domain includes arbitrarily small positive values, but does not include alpha=0. Its logarithmic limiting interpretation is explanatory background, not an additional endpoint clause. Neither alpha=1/2 nor alpha=1/4 in the second bound is included. A matching lower bound, optimal numerical value of C, rectangular oversampling or restricted isometry is not a separate subquestion of this canonical target.

## Exact indexing, nodes and Fourier matrices

Put m=2*N+1 and h=2*pi/(m:Real). Use indices Fin m for both sampling nodes and frequencies. For an index k define its signed integer frequency
nu(k)=(k.val:Int)-(N:Int),
or use the exactly equal real expression (k.val:Real)-(N:Real). Do not subtract N in the natural numbers before casting, which would truncate negative indices. The signed frequencies run through every integer from -N to N exactly once.

A shift vector is s:Fin m->Real, with Admissible(alpha,s) meaning forall k, abs(s(k))<=alpha. Define the actual real node representative
x_k=(nu(k)+s(k))*h.
Using these representatives without an explicit modulo operation is equivalent to the original circle nodes, since all frequencies are integers and the complex exponential is 2*pi-periodic in these evaluations. No node wrapping, sorting, randomization, average shift restriction or endpoint perturbation restriction is imposed.

Define the unnormalized square matrix W with row k for nodes and column j for frequencies:
W_(k,j)=Complex.exp(I*(nu(j)*x_k)).
All real quantities in this expression are embedded into Complex, and I is the ordinary complex imaginary unit. Define the normalized matrix
F_(k,j)=((1/Real.sqrt(m:Real)):Complex)*W_(k,j).
This is exactly m^(-1/2)[exp(i*j*x_k)] with m rows and m columns. The scale is not m^(-1), m^(1/2), or omitted. Data vectors have one complex entry per node; coefficient vectors have one complex entry per frequency.

For admissible shifts and 0<alpha<1/2, each neighboring gap, including the circular gap across the last and first nodes, is at least h*(1-2*alpha)>0. Thus the m circle points z_k=exp(I*x_k) are distinct. W factors into the invertible diagonal row factor z_k^(-N) times the ordinary square Vandermonde matrix [z_k^(j.val)]_(k,j). All z_k are nonzero. The Vandermonde determinant is therefore nonzero, and W and F are invertible. This is a mathematical correspondence fact explaining the domain, not a new determinant premise that may be added to weaken the target.

## Concrete interpolant and the exact Lebesgue quantity

For y:Fin m->Complex, define its coefficient vector by the actual matrix inverse:
c_j=sum_k (W^(-1))_(j,k)*y_k.
Set
T(N,s,y)(x)=sum_j c_j*Complex.exp(I*(nu(j)*x))
for every real x. On the admissible domain W is genuinely invertible, so this is exactly the unique trigonometric polynomial with all frequencies -N,...,N and with T(x_k)=y_k. It has degree at most N, without imposing real coefficients, conjugate symmetry, smoothness of input data or a mean-zero condition. The original interpolation map is not a least-squares or oversampled replacement.

Define Lambda_N(s) as the actual real supremum of the set
{ r:Real | exists y:Fin m->Complex, (forall k, norm(y_k)<=1) and
           exists x:Real, -pi<=x and x<=pi and r=norm(T(N,s,y)(x)) }.
Here norm is the ordinary complex modulus; the coordinate condition is precisely the complex data infinity-norm unit ball. All y and all x on the complete closed interval are retained.

This joint supremum is equivalent to sup_(||y||_infinity<=1) ||T_N y||_(L-infinity[-pi,pi]). Each interpolant is continuous, so its L-infinity essential supremum equals its usual maximum on the interval. The finite complex polydisk of y and the interval are compact, the evaluation depends continuously on both, and the set is nonempty (take y=0,x=0). Thus the real sSup is a genuine finite maximum and cannot invoke an empty or unbounded fallback. Repeating the periodic endpoint value at -pi and pi does not change it.

An implementation may equivalently define Lambda as sup_x sum_k norm(ell_k(x)), where ell_k is the exact cardinal polynomial T_N e_k, but only with explicit correspondence reviewed: the upper inequality is the triangle inequality, and for each fixed x one chooses unit-modulus complex data phases to align all nonzero ell_k(x), with arbitrary phase for a zero term. The current preferred boundary is the joint supremum above because it directly retains the original operator norm and avoids an extra cardinal-polynomial construction.

The unnormalized W inverse in T is intentional. Using F inverse in that same coefficient formula without a compensating factor 1/sqrt(m) would multiply the interpolant by sqrt(m) and change Lambda. A later implementation must review this normalization explicitly.

## Exact Fourier inverse norm

Define Gamma_N(s) as the operator norm of the actual complex Euclidean map represented by F^(-1), for example
norm(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (F^(-1)))).
The pinned Matrix.toEuclideanLin is the map between Euclidean (WithLp 2) spaces, and its continuous-linear-map norm is the induced spectral norm. It is not the entrywise matrix supremum, Frobenius norm, interpolation infinity norm, or an unnormalized coefficient norm.

The imported total matrix inverse must be used only with the mathematical correspondence that F is nonsingular throughout the target's admissible input domain. Defining helpers off that domain is harmless, but no proof of the target may exploit the singular-matrix fallback. The second bound is for this square normalized F and no other matrix shape.

The two bounds measure different operators and cannot be identified by a norm conversion that loses powers of N. Each named proposition must use its own concrete Lambda or Gamma as specified, and Target must include both.

## Complete endpoints and source correspondence

Preserve N=2, all larger dimensions, every weakly admissible shift including |s_k|=alpha, zero shifts, arbitrary mixtures of signs, repeated shift values and all near-collision gaps allowed by alpha<1/2. Nodes themselves remain distinct for all those inputs. All constants must have exactly the quantifier scopes given above. No lower bound on 1-2*alpha, finite maximum N or rational-only shift set is permitted.

The complete canonical README and the retained Stepaniants solution were read. Section 1 Theorem 1 states both bounds with the exact quantifier distinction. Section 7 explicitly uses nodes as rows, the normalized square Fourier matrix, and E=F_0*F^(-1), confirming the second norm convention. Section 8 repeats the absence of an alpha=1/4 endpoint assertion and that the first constant is absolute. Section 4's cardinal-polynomial analysis is a proof technique and is not an alternative numerical target.

George Stepaniants retains the credited resolution; Austin and Trefethen retain the original conjectures and prior analysis. The retained proof's Hilbert-transform estimate, grid-product inequalities and no-logarithm matrix estimates are future proof material, not assumptions to be passed into the proposition. Its finite diagnostics are not universal certificates.

## Preimplementation and final verification requirements

Two independent reviewers must check both complete quantifier chains, signed indices, exponential sign, node-versus-frequency orientation, exact m^(-1/2) scaling, W-versus-F interpolation normalization, the full complex data unit ball, continuum interval supremum, both actual Euclidean norms and all open/closed parameter endpoints before code.

The final Lean statement must be a closed safe Target : Prop, with separately named FirstBound and SecondBound if practical, concrete matrix/complex-exponential/real-power/supremum definitions, and no target axiom, uninterpreted interpolator or assumed stability inequality. Define actual helper meanings; proving invertibility, interpolation uniqueness, norm correspondence and the two estimates is separate proof work. No target-dependent semantics parameter is allowed.

Use the shared pinned LeanCert kernel setting, #assert_statement and #assert_trust kernel, and bind actual local helper imports and dependency pins in final independent reviews. A shared helper module is appropriate if live and frozen copies would otherwise duplicate recursive definitions. Fresh actual statement identity must be checked, not merely textual similarity. No quadrature, sampled shifts, complex floating-point inversion, finite cutoff or artificial interval computation is needed merely to state these exact universal bounds. No successful build or identity comparison proves either conjecture or changes the catalog status.
