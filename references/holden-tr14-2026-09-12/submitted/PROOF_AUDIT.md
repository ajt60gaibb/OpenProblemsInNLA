# Proof audit

## Scope

The theorem concerns ordinary and symmetric **exact** rank over the complex numbers for every equal-mode Hankel tensor of order m≥3 and mode dimension n≥2. There is no genericity assumption. The proof is not an argument that equality on a dense open set extends to exceptional tensors.

The universal statement is established in Sections 2–5 of the manuscript. Section 6 supplies a separate border-rank result. The exact-rank argument does not depend on the border-rank argument or its matrix identity.

The argument has not received independent peer review or proof-assistant verification. This audit records explicit logical checks, rather than substituting a numerical experiment for a proof.

## Dependency map

| Result | Dependencies | Role |
|---|---|---|
| Lemma 2.1, finite moment algebra | Minimal apolar recurrence and polynomial division | Produces a Frobenius algebra of dimension r |
| Lemma 2.2, minimal-polynomial choice | Frobenius pairing and degree bounds | Resolves ambiguity in the balanced case |
| Proposition 3.1, local upper bound | Chinese remainder theorem; root-of-unity interpolation | Symmetric decomposition with (m−1)r−(m−2)s terms |
| Proposition 3.2, binary upper bound | Top-coefficient pairing; squarefree apolar pencil | Symmetric decomposition with D−r+2 terms |
| Lemma 4.1, linear transformation | Beck–Lecouvey's transformation; proof included | Auxiliary algebra and product-space dimension bound |
| Lemma 4.2, contextual inequality | Lemma 4.1; Frobenius nilpotent exclusion | Justifies finite-support uniformization in a nonreduced ambient algebra |
| Proposition 5.1, ordinary lower bound | Graph of a minimum ordinary decomposition; Lemma 4.2 | Matching lower bound without symmetry restrictions |
| Theorem 1.1 | Both upper bounds and Proposition 5.1 | Exact-rank equality and formula |
| Theorem 6.1 | Recurrence perturbation; fixed Koszul factorization | Equality of the three border ranks |

## Moment-algebra checks

**Projective coordinates.** A common binary linear change acts invertibly on every degree-(n−1) mode. It therefore preserves the two ranks being compared. A coordinate chart avoiding the finite projective support makes the minimal apolar polynomial monic. Roots at infinity are not discarded. In the rank code they are counted explicitly; in the decomposition code an invertible rational shear moves them to a finite chart.

**Frobenius nondegeneracy.** The functional is not declared nondegenerate merely because a moment representation exists. If its multiplication pairing had a nonzero radical, quotienting by that radical would give a proper divisor of the minimal apolar polynomial and hence a lower-degree recurrence for all required moments. This contradicts minimality. This argument also handles the balanced degree.

**Middle rank.** Both middle polynomial spaces surject onto the moment algebra because their degrees are at least r−1. Pulling back a nondegenerate pairing through two surjections has rank r. This verifies the identification between the minimal apolar degree and the middle matrix rank.

**All-but-one surjectivity.** This is the crucial degree condition. Products of m−1 mode polynomials span every polynomial of degree at most (m−1)(n−1). That degree is at least r−1. Thus these products surject onto the entire moment algebra even when a single mode does not, particularly when r>n.

**Balanced ambiguity.** If D≥2r−1, all degree-r apolar polynomials are multiples of the chosen one. Otherwise D=2r−2 and the smallest apolar kernel has dimension two. In that case D−r+2=r, while the other upper bound is at least r for every root count s. No canonical choice of a polynomial is required.

## Symmetric-construction checks

The local functional on C[z]/(z^ell) has the form “coefficient of z^(ell−1) after multiplication by a unit u.” Taking an mth root of u in that local algebra puts the same linear functional in every tensor mode. This is why the construction gives symmetric rank-one tensors rather than merely ordinary ones.

With N=(m−1)(ell−1)+1, the only integer in [0,m(ell−1)] congruent to ell−1 modulo N is ell−1. There is no hidden wraparound term in the root-of-unity interpolation formula. The case ell=1 is included.

For the other upper bound, the top-coefficient pairing identifies the moment functional with multiplication by a unit. Its inverse produces an apolar polynomial B of complementary degree that is coprime to the minimal apolar polynomial G. A base-point-free pencil has a squarefree member in characteristic zero; the manuscript supplies the rational-function critical-value argument. The finite-root Vandermonde system then reconstructs all moments by recurrence.

The two constructions are independent upper bounds. A local construction is not asserted to be optimal when the binary bound is smaller, nor vice versa. Ordinary and symmetric optimality follow only after the matching lower bound is proved.

## The main potential obstruction: infinitely many nonreduced subalgebras

A general Kneser product inequality cannot simply be applied to A×C^R with the assumption that this ambient algebra has finitely many subalgebras. It may not. Nor does proving that the final stabilizer is reduced, by itself, suffice to justify that application.

The proof addresses the stronger requirement: **every auxiliary algebra K_a in the transformation lemma is reduced**. For a partial product, write U=U_j, V=U_1⋯U_(j−1), Q=U_(j+1)⋯U_m. The transformation gives aV⊂T_a⊂UV and K_a T_a=T_a.

For a nilpotent z in K_a, the component in C^R is zero. Hence

    z a VQ ⊂ T_a Q ⊂ UVQ = W.

The annihilating functional therefore gives

    Lambda_A(z_A a_A pi_A(VQ)) = 0.

Now pi_A(VQ)=A by the all-but-one hypothesis, a_A is a unit, and Lambda_A is Frobenius. Consequently z_A=0 and z=0. This argument applies to every partial-product step, including the early ones; it does not require that an early partial product already surject onto A.

A reduced finite-dimensional complex algebra is a product of copies of C. In each local factor of the ambient algebra, every idempotent is 0 or 1. Reduced unital subalgebras are thus determined by partitions of a finite set of local factors. There are finitely many **of these**, regardless of the number of other subalgebras.

The one-parameter vectors 1+c x_2+⋯+c^(d−1)x_d are units for all but finitely many c, and d distinct values are a basis by the Vandermonde determinant. One reduced auxiliary algebra occurs for infinitely many values. Summing the corresponding T-spaces puts that algebra in the actual stabilizer of UV and proves the dimension inequality. This is the precise point where finiteness is used.

## Arbitrary-decomposition and support-partition checks

A minimum ordinary decomposition has linearly independent decomposable summands: a linear relation would let one summand be removed by rescaling others. No symmetry, equal-mode factors, or Vandermonde parameterization is assumed for these summands.

The graph construction uses the abstract direct product A×C^R. It does not require that the decomposition points and apolar points be geometrically disjoint. It therefore remains valid when some of those points coincide in an ambient projective space.

Each graph subspace contains a unit: a polynomial can avoid the finitely many root-evaluation and decomposition-factor hyperplanes. Dividing each graph space by such a unit puts 1 in it. Multiplying the functional by the product of those units preserves its Frobenius restriction to A and its nonzero coefficients on the scalar factors. The all-but-one surjectivity survives because the change on A is multiplication by a unit.

Independence of the ordinary summands makes the product graph project onto all of C^R. A primitive stabilizer block cannot consist solely of scalar decomposition factors: its product space would be the whole scalar block, which cannot be annihilated by a functional with nonzero coordinate coefficients.

The stabilizer idempotents partition **whole local factors** of A. In particular, a derivative coordinate of a repeated root cannot become a separate reduced support point in this argument. If a block contains apolar length r_j, its projection of a mode has dimension min(n,r_j), by polynomial reduction modulo a degree-r_j divisor of g. This dimension does not require generic root positions.

The stabilizer inside each primitive block is scalar. Otherwise an additional stabilizer, extended by zero, would enlarge the original stabilizer on that primitive block. The contextual product inequality now gives

    R_j >= m min(n,r_j) − r_j − m + 2.

If one block has r_j≥n, then R≥D−r+2. If all blocks have r_j<n, summing gives R≥(m−1)r−(m−2)t, and t≤s gives the other lower bound. These two alternatives establish the minimum of the two upper bounds. No rank lower bound is passed through an unjustified restriction, and no tensor-rank additivity theorem is assumed.

## Border-rank checks

For even order, the middle catalecticant is a submatrix of an ordinary flattening. For odd order, the manuscript specifies an explicit matrix E and verifies

    K = E [ 0  C ; −C^T  0 ] E^T.

E has full column rank independently of the moments. K therefore has rank 2r for every moment vector, including exceptional ones. On an arbitrary rank-one compressed tensor, K has rank at most two, giving the ordinary border-rank lower bound. When n=2 two extracted middle coordinates coincide; duplication is still a linear map, so this case is valid.

The upper border bound perturbs a monic recurrence polynomial to squarefree polynomials while keeping the initial r moments fixed. Recurrence extension is continuous in its coefficients. This supplies length-at-most-r Vandermonde approximants and does not infer exact rank by taking limits.

## What the computations do and do not establish

`checks/ranks.json` tests the exact apolar calculation, projective root count, and rank-formula implementation on 162 profiles and reversals. Its expected ranks are obtained from the theorem's formula; these are implementation regressions, not independent unrestricted-rank certificates.

`checks/identities.json` verifies 96 Fourier index ranges and 128 Koszul matrix identities over the integers. It also records finite-field matrix ranks, 3,081 finite-field tensor-entry checks, and a mixed graph example. The field and prime are stated explicitly. These tests are not presented as a proof of a characteristic-zero theorem.

`checks/certificates.json` adds exact characteristic-zero checks. Ten implicit algebraic-root decompositions are verified by rational polynomial remainders, including 1,053 entries of the original tensors, nonconstant local functionals, the balanced case, and roots at infinity. These establish the stated decompositions for those inputs, not a universal rank lower bound.

Appendix A gives an independent substitution lower bound for single-support terminal moment sequences. The general lower bound remains the mathematical argument in Sections 4–5; it is not dependent on successful script output.
