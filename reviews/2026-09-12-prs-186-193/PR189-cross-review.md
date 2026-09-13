# PR 189 / TR-14 independent cross-review of the universal exact-rank proof

**Verdict: PASS for Theorem 1.1 and its complete proof in Sections 1–5. No logical blocker found.** I independently read and checked the argument without relying on either earlier PASS verdict. This is an informal mathematical source review, not a Lean/formal-verification result, external human peer review, or a novelty determination.

Reviewed immutable head: `5d79588e225376c81f1a664f3ec128a482bf7103`.
Reviewed mathematical source: `tensor-computations/TR-14/solution.tex`.
SHA-256: `0089d218f9f578e2ab21542c238a4025a4d98d7a32f66b25656c282716c14bc6`.
The bounded cross-review covers the full ordinary-rank lower bound, its moment-algebra hypotheses and both matching symmetric upper bounds. It does not independently re-audit the later border-rank, maximum-rank, or appendix claims.

## Original target and finite moment algebra

The theorem retains every complex moment vector, all orders `m ≥ 3`, all dimensions `n ≥ 2`, and unrestricted ordinary decompositions. Zero is treated separately. Nonzero tensors are represented exactly by `H(p₁,…,p_m)=L(p₁⋯p_m)` on polynomials of degree at most `q=n−1`; products span all monomials through degree `D=mq`, so a nonzero Hankel tensor supplies a nonzero moment functional. A binary-coordinate change induces an invertible, identical change on each degree-q mode and therefore preserves both ranks. It can move infinity outside the finite root set of any chosen nonzero minimal-degree apolar polynomial.

For the resulting monic polynomial g of minimal apolar degree r, the recurrence defines λ on `A=C[t]/(g)` and reproduces **all** supplied moments through D. The Frobenius proof is valid: the pairing radical is an ideal; if nonzero, quotienting corresponds to a monic proper divisor g′ of g. Because λ kills that ideal and still reproduces the moments, g′ supplies a lower-degree apolar recurrence throughout its required range, contradicting minimality. This argument also rules out the zero functional/zero quotient exception under `H ≠ 0`.

The elementary column/row count proves `r ≤ floor(D/2)+1`. Both middle-degree polynomial spaces thus surject onto A, and pulling back the nondegenerate pairing gives middle catalecticant rank exactly r. For every subset of whole local factors, polynomial reduction has image dimension `min(n,r_J)` by reduction modulo their product polynomial. Finally, `(m−1)q ≥ r−1`, so the products of every collection of m−1 unnormalized mode spaces span A. This last surjectivity is the actual hypothesis used later; no individual-mode surjectivity is asserted when `r>n`.

The minimal-apolar-kernel distinction is also sound. If `D≥2r−1`, the testing degrees through `D−r` surject onto A and force every minimal-degree apolar polynomial to be a multiple of g. If `D=2r−2`, testing through r−2 supplies r−1 independent constraints on A, and the degree-at-most-r reduction map has one-dimensional kernel, leaving an apolar kernel of dimension two.

## Both upper bounds, including the balanced case

For a local factor `C[z]/(z^ell)`, writing its Frobenius functional as top-coefficient extraction after multiplication by a unit u is correct. Nonvanishing of its top-coefficient pairing is exactly what makes `u(0)` nonzero. A truncated m-th root w exists in characteristic zero over C. Reducing each `w p_i` modulo `z^ell` preserves the coefficient of degree ell−1 in the product, hence realizes the original functional.

The Fourier construction uses `N=(m−1)(ell−1)+1`. Among degrees 0 through `m(ell−1)`, the only degree congruent to ell−1 modulo N is ell−1: subtracting N is negative, and adding N gives `m(ell−1)+1`. This remains correct for ell=1. Each evaluation is the **same linear functional in every mode**, so the construction bounds symmetric rank by `Σ_a((m−1)(ell_a−1)+1)`. These evaluations need not be Vandermonde evaluations on the original modes, and the proof does not require that extra restriction.

For the second bound, coefficient extraction τ on the monic quotient is Frobenius. The representing element u in `λ(a)=τ(ua)` is a unit because λ is Frobenius. Its inverse representative b has degree at most r−1 and annihilates the required test moments through r−2; their total degree is at most `2r−3≤D`. Thus the degree-v homogenization of b is genuinely apolar for `v=D−r+2≥r`, not merely orthogonal in an insufficient moment range.

This polynomial B is coprime to G: b is a unit modulo g, and G has no zero at infinity. One can choose Q of degree v−r avoiding B's finitely many zeros and not vanishing at infinity. The pencil `B+cGQ` has degree v for c nonzero. Its rational-function critical-value argument is valid even with repeated roots of GQ: those poles are not roots of the pencil, by coprimality. The characteristic-zero nonconstant rational function has only finitely many finite critical values, so some pencil member is squarefree and has no zero at infinity. The Vandermonde recurrence then matches all required moments through D. When r=1 the proof's separate rank-one argument applies; when `D=2r−2`, v=r and the constant Q pencil yields the necessary squarefree member of the two-dimensional apolar kernel.

Consequently both symmetric upper bounds hold on the entire stated domain. In the balanced case their minimum is r regardless of the chosen minimal G, because `(m−1)r−(m−2)s≥r`.

## Transformation, auxiliary algebras, and finiteness

The transformation lemma has a complete proof rather than an unverified appeal to a general Kneser inequality in a nonreduced algebra. Scaling U by a chosen unit a and V by any unit reduces to `a=1∈U`, `1∈V`; undoing these scalings preserves the stabilizing algebra in the commutative setting and restores the required inclusion `aV⊆T_a`.

For a unit e in V, `U_e=U∩Ve⁻¹` and `V_e=V+Ue` both contain one, their product lies in UV, and the dimensions sum to `dim U+dim V` by the intersection formula. If `U_e` is proper, induction applies. Otherwise units span V, so `UV=V` and the algebra generated by U stabilizes V. The assertion that units span a subspace containing a unit is valid: a finite-dimensional complex commutative algebra has finitely many local residue factors, and its nonunits are the union of the corresponding residue hyperplanes.

The crucial extra step is supplied **before** any finiteness assertion. If z is nilpotent in an auxiliary algebra K_a, its `C^R` coordinates vanish. Since `z aVQ⊆T_aQ⊆W`, the annihilating functional gives `λ_A(z_A a_A π_A(VQ))=0`. Here `π_A(VQ)=A` is exactly the all-but-one hypothesis for U_j, and a_A is a unit. The Frobenius pairing forces z_A=0. Thus every K_a is reduced; no reduction of the ambient A is assumed.

There really are only finitely many reduced unital subalgebras of this B over C. Each is a product of copies of C and is spanned by its primitive idempotents; an idempotent in each local factor of B is either zero or one. Therefore such subalgebras correspond to partitions of the **finite set of whole local factors**, with no continuous parameters or infinitesimal lifts.

The polynomial curve `a(c)=1+c x₂+…+c^(d−1)x_d` avoids nonunits except at finitely many c. Finitely many possible K_a imply infinitely many parameter values share one K, hence d distinct such values can be selected. Their a(c)'s form a basis of U by the Vandermonde determinant. The containments in the transformation lemma then imply `UV=Σ T_a`, making K a subalgebra of `Stab(UV)` and giving the desired contextual dimension inequality. This pigeonhole step is justified; it would not be justified without the preceding reducedness proof.

The same Frobenius argument makes `Stab(W)` reduced. Partial-product stabilizers embed into the final stabilizer by multiplying through the remaining subspaces, so a trivial final stabilizer gives the stated iterated dimension bound.

## Arbitrary ordinary decomposition and primitive-block count

A minimum-length CP decomposition has linearly independent decomposable tensors: a nonzero linear relation allows one summand to be eliminated after absorbing scalars into the remaining factors. This is valid for arbitrary mode-dependent complex linear factors, without symmetry or Vandermonde assumptions.

The graph subspaces record precisely those factors. A unit can be selected in each graph by avoiding the proper hyperplanes from local residue evaluations and the nonzero CP factors. Multiplying by its inverse puts one in each normalized mode. The adjusted λ_A is the original Frobenius functional multiplied by a unit, hence still Frobenius; every `C^R` coefficient remains nonzero. All-but-one product images remain A, since normalization only multiplies each original image by fixed units. Thus every contextual hypothesis has actually been proved.

Independence of the R decomposable tensors makes the product-evaluation map onto `C^R`; normalization merely rescales its coordinates. This is the precise use of minimality, and it remains valid even if an individual graph parametrization has a kernel.

For `K=Stab(W)`, primitive idempotents split B into whole-local-factor blocks. Stabilization gives `W=⊕e_jW`. A block containing only decomposition coordinates would, by surjectivity onto `C^R`, have `e_jW=B_j=C^{R_j}`. The functional cannot annihilate that entire block because all its coordinate coefficients are nonzero. Hence each block contains at least one local factor of A, giving `t≤s`, `Σr_j=r`, `ΣR_j=R`.

Each block inherits all contextual hypotheses and has stabilizer exactly `C e_j`: any extra block stabilizer extends by zero to a member of K, contradicting primitiveness. Its mode projections have dimensions `min(n,r_j)` after multiplication by units. The trivial-stabilizer bound and the nonzero annihilating functional therefore imply

`m min(n,r_j)−m+1 ≤ dim W^(j) ≤ r_j+R_j−1`,

hence `R_j≥m min(n,r_j)−r_j−m+2`. No tensor-rank additivity assumption is made.

If any `r_j≥n`, nonnegativity of the other decomposition-coordinate counts gives `R≥D−r_j+2≥D−r+2`. Otherwise summing yields `R≥(m−1)r−(m−2)t≥(m−1)r−(m−2)s`. These exhaustive cases establish the claimed lower bound for an **arbitrary** minimum ordinary decomposition, including `r>n` and any mixture of repeated support points. Combining it with the two symmetric upper bounds and `R≤R_sym` proves the full universal exact-rank formula and the original retained conjecture.

No extra numerical tests were needed for this cross-review. The essential lower-bound steps are universal algebra and dimension arguments; the potential failure points requested by the coordinator have explicit valid resolutions in the current manuscript.
