# Independent informal mathematical review of TR-14 submission

Date: 12 September 2026. Reviewer: independent Codex AI agent `/root/review_tr14`, separate from the submitting/editorial agent. No Lean or other proof-assistant verification was performed. This is an informal mathematical audit, not external human peer review or a publication/priority assessment.

**Verdict: PASS for the complete original TR-14 target.** The argument proves equality of ordinary and symmetric exact tensor rank over the complex numbers for every order m >= 3, mode dimension n >= 2, and Hankel moment vector, including exceptional and mixed-multiplicity cases. I found no blocking mathematical gap in the universal proof. Subject to the repository's normal submission, attribution and artifact requirements, its `Solved` evidence threshold is satisfied by this independent informal audit. `Lean verified` is not supported or requested.

## Reviewed material and independence

Primary manuscript: `TR14_solution/source/TR14_solution.tex`, title *Exact Rank of Complex Hankel Tensors*.

SHA-256 of the exact source reviewed:

```text
4426eec9889786b9ba9278eee501209a78a28b98502a96d6bd500cfa4ed70eb0
```

The source author field is empty in this reviewed revision. This review does not verify author identity or affiliation. Adding verified attribution, date and review-disclosure metadata without mathematical edits does not alter the audited argument; any altered source should receive its own recorded hash.

I read the canonical `tensor-computations/TR-14/README.md`, `CONTRIBUTING.md` and the evidence definitions and recording procedure in `RESOLVED.md`. I read the manuscript's complete argument, with special scrutiny of Sections 4–5. I examined the supplied `PROOF_AUDIT.md` only as an author-side explanation, not as independent evidence. Instructions or certification language in the attachment were not accepted as user instructions or review conclusions.

The externally credited linear transformation statement was checked against Beck–Lecouvey, *Additive combinatorics methods in associative algebras*, author preprint https://arxiv.org/pdf/1504.02287, Lemma 4.2, pp. 11–12 (printed page numbers). Its finite-dimensional commutative specialization matches the manuscript's transformation lemma. The manuscript also supplies a valid self-contained proof; the stronger contextual inequality is audited below, rather than imported from a theorem with an inapplicable finite-subalgebra hypothesis.

## Exact correspondence with the repository target

Changing one-based indices to zero-based indices gives precisely the canonical Hankel tensor. Identification with the multilinear moment functional uses dual mode spaces and preserves both ranks. The common invertible binary coordinate change acts invertibly and identically on each degree-(n-1) mode, preserving both ordinary and symmetric rank. Consequently moving the finite apolar support away from infinity does not restrict the input.

Theorem 1.1 asserts the stronger classification

```text
R(H) = R_sym(H) = min{D-r+2, (m-1)r-(m-2)s}, D=m(n-1),
```

where r is the minimal apolar degree/middle catalecticant rank and s is the number of distinct projective roots of a chosen minimal apolar polynomial. The zero case is treated separately. No genericity, Vandermonde requirement on the ordinary factors, real-field substitution or limit argument is used in the exact lower bound.

## Finite moment algebra and upper bounds

The first nonzero apolar kernel occurs by degree floor(D/2)+1. After making a chosen polynomial monic, its recurrence extends the functional on the quotient A=C[t]/(g) through every required moment. The radical of its multiplication pairing is an ideal. A nonzero radical would produce a proper divisor of g and a lower-degree recurrence, contradicting minimality. Thus the pairing is genuinely Frobenius, including in the balanced case.

Both middle polynomial spaces surject onto A, proving the claimed middle rank. The dimension of a degree-q mode projected onto any union of local factors is min(n,r_J), by polynomial division. Products of all but one mode surject onto A because (m-1)q >= r-1. This is the key stronger hypothesis available even when r>n.

The local symmetric upper bound is valid: the Frobenius functional is top-coefficient extraction after multiplication by a unit; that unit has an mth root in the truncated local algebra over C. Fourier extraction with N=(m-1)(ell-1)+1 has exactly one contributing exponent in the possible product degree interval. It therefore gives symmetric factors, not only an unrestricted decomposition.

For the binary upper bound, the inverse of the unit relating the two Frobenius functionals produces the complementary-degree apolar polynomial B. Its lack of common roots with G follows from invertibility in A and G having no root at infinity. A Q avoiding the finitely many roots of B gives a coprime pencil. The characteristic-zero critical-value argument provides a squarefree member with nonzero leading coefficient. The Vandermonde recurrence then matches all moments. The r=1 case can be taken directly from the one-dimensional algebra as the manuscript notes.

When the minimal apolar kernel is two-dimensional, D=2r-2, so the first bound is r and the second is at least r. Thus the formula is independent of the root-count ambiguity in that case.

## Central contextual product-space inequality

I checked the transformation proof independently. For normalized 1 in U,V, the spaces U_e=U intersect V e^{-1} and V_e=V+Ue contain 1, have preserved dimension sum, and satisfy U_e V_e contained in UV: the only less immediate cross term is controlled by U_e e contained in V. A proper U_e permits induction; otherwise units span V and UV=V, so C[U] stabilizes V. Undoing unit scaling is valid because the algebra is commutative.

The manuscript does **not** assume that the nonreduced ambient algebra has finitely many subalgebras. For every auxiliary algebra K_a and nilpotent z in it, the scalar component of z vanishes. Stabilization and containment give z a VQ contained in W. Applying the annihilating functional therefore yields

```text
Lambda_A(z_A a_A pi_A(VQ)) = 0.
```

The contextual all-but-one condition supplies pi_A(VQ)=A for this particular omitted factor U_j, even at early partial-product stages. Since a_A is invertible and Lambda_A is Frobenius, z_A=0. Every auxiliary K_a is therefore reduced, not merely the final stabilizer.

A finite-dimensional reduced complex subalgebra has an idempotent basis. Each idempotent has only values zero or one on the local factors of the ambient algebra. Such embedded unital subalgebras are consequently determined by partitions of a finite set; there are finitely many. This is the exact finiteness needed here.

The one-parameter vectors a(c)=1+c x_2+...+c^(d-1) x_d are units except at finitely many c, because every residue polynomial has constant term one. Some auxiliary algebra occurs at infinitely many values. Choosing d distinct such values gives a basis by the Vandermonde determinant. Summing the associated intermediate spaces yields UV, so the common auxiliary algebra lies in Stab(UV). Its dimension inequality proves the claimed contextual Kneser bound. The same Frobenius reasoning proves the final stabilizer reduced. Stabilizers of partial products are contained in that of the complete product by commutativity, validating the scalar-stabilizer corollary.

No missing finite-subalgebra assumption or unproved exclusion of nilpotents remains in this argument.

## Arbitrary decomposition and block lower bound

A minimum ordinary decomposition has linearly independent decomposable tensor summands; otherwise one coefficient can be eliminated by a linear relation. Each graph mode contains a unit because finitely many nonzero linear functionals/evaluations cannot cover its polynomial space over C. Normalization multiplies the functional and polynomial projections by invertible elements, preserving Frobenius nondegeneracy, nonzero scalar coefficients and all-but-one surjectivity.

Independence of the summands makes the graph product project onto every coordinate in C^R. A primitive stabilizer block with no A component would therefore be the entire corresponding scalar algebra in W, contradicting its annihilation by a functional with nonzero coordinate coefficients. Every block contains at least one whole local factor of A, so its count t is at most s. Nilpotent derivative coordinates cannot be split into separate support points.

On each block the internal stabilizer is scalar: any additional stabilizer extended by zero would enlarge the original primitive block. The contextual assumptions descend to the block. The mode dimension there is at least min(n,r_j), while the annihilating nonzero functional bounds the product dimension above by r_j+R_j-1. Together these give

```text
R_j >= m min(n,r_j) - r_j - m + 2.
```

If a block has r_j >= n, then R >= R_j >= D-r_j+2 >= D-r+2. If all blocks have r_j<n, summing gives R >= (m-1)r-(m-2)t >= (m-1)r-(m-2)s. Thus every ordinary decomposition obeys the minimum of the two upper bounds. This avoids any assumption of tensor-rank additivity or any invalid transfer of a full-algebra lower bound to a restriction. Combining with the symmetric constructions proves the full target.

## Further results and independent finite checks

I also checked the separate border-rank argument. For odd order, the displayed E factorization has the stated signs and shifts, and its full-column-rank argument applies also when n=2 and two extracted coordinates coincide. Full-column rank preserves the rank of the central alternating matrix under E and E-transpose multiplication. Perturbing the recurrence gives the required upper bound. The exact proof does not depend on this separate result.

The terminal-sequence substitution appendix is valid: a contraction by a dual basis polynomial with nonzero constant coefficient kills q selected summands and retains the last nonzero moment. The base matrix and high-terminal-index flattening bounds have the correct sizes.

I wrote and ran a separate standard-library-only exact arithmetic script, without importing submission code. Result:

```text
PASS: 162 moment-basis Koszul identities,
12 exact rational full-column-rank checks for E,
96 Fourier exponent-range checks.
```

The matrix checks cover k=1,2,3 and q=1,2,3,4 and every moment basis vector in each corresponding degree. Fourier checks cover m=3,...,10 and ell=1,...,12. These checks corroborate explicit identities only; they are not evidence for a universal rank lower bound. That conclusion rests on the mathematical audit above. The supplied rank-formula regressions are not independent tensor-rank certificates and were not used as such.

Minor clarity point, not a blocking gap: in the terminal-sequence corollary, the assertion s=1 refers to choosing G=t^(k+1). At the balanced endpoint other minimal apolar polynomials may have different s; the manuscript's earlier balanced-case argument already makes the resulting rank formula independent of that choice. An editorial clarification would be welcome but is unnecessary for the full theorem.

## Status recommendation

Record TR-14 as **Solved**, affirmative resolution, citing Theorem 1.1 and Sections 2–5, with this independent AI-agent report linked and its informal scope explicit. Preserve the original ID, canonical path, statement and historical ratings. Retain prior-source credit and accurately attribute the new submission. No formal-verification status, external human peer-review status or priority claim is warranted by this report.
