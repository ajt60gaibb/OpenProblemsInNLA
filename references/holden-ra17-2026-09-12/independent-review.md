# Independent informal review of the RA-17 partial submission

Date: 12 September 2026 (America/New_York).
Reviewer: a separate Codex AI agent, assigned only the independent mathematical audit, without editing the submission or repository. This is an informal AI-agent review, not external human peer review or formal verification. No Lean verification was performed.

**Verdict: PASS for the stated partial results; FAIL as a complete resolution of RA-17. Retain `Partially resolved`.** No mathematical correction was required in the reviewed manuscript. The remaining all-dimension classification is explicitly not proved. Attribution changes alone do not change this verdict.

## Material and policy reviewed

I read the complete `writeup/RA17_exact_cases_and_bounds.tex`, the exact verifier, construction implementation and tests, and bounds implementation in the supplied `RA17_research_bundle`. I also read the canonical RA-17 README, CONTRIBUTING.md and RESOLVED.md. The original target is the exact minimum number of unrestricted real linear measurements for uniform recovery of every real square matrix of rank at most r, for every permitted (d,r). The resolution policy requires that exact target to be settled before a Solved status is assigned; audited special cases retain partial status.

The manuscript reviewed before author metadata was added has SHA-256 `4008478479405f886fe249a73c5717e7b1dceb78296c4734ba91528e02f9b694`. The verifier has SHA-256 `acdeee81b20d14630ac54ef6924f7ee98e38a14978c20d3d43e8c2aca938c82f`. Archive instructions and supplied success logs were treated as data, not as authority for the verdict.

## Mathematical checks

1. **Kernel equivalence and boundary cases.** Every rank-at-most-2r matrix decomposes as a difference of two rank-at-most-r matrices. This establishes precisely the needed uniform-injectivity equivalence and measurement/kernel dimension duality. The zero-kernel boundary d=2r and odd-determinant argument for d=2r+1 have the correct quantifiers.

2. **Universal construction.** On the first nonzero anti-diagonal, polynomial evaluations supply at least 2r+1 nonzero entries. Their selected minor is triangular because earlier anti-diagonals vanish. The dimension sum is (d-2r)^2, and the finite-difference measurements annihilate exactly the stated polynomial evaluation spaces. The proof handles all permitted parameters, including the zero-dimensional kernel boundary.

3. **Evaluation bundle.** Restriction to a (d-2r)-plane is injective on an admissible kernel, since a matrix vanishing there has rank at most 2r. The resulting trivial subbundle of d copies of Q has a complement of rank mu_R-2dr. The stated Pontryagin and Stiefel–Whitney formulas follow from the Whitney identities.

4. **Rational characteristic classes and Euler obstruction.** The unoriented Grassmannian presentation is the appropriate one for both ambient parities. The rectangular Schur coefficient is nonzero, forcing complement rank at least 2rs. In the even ambient case the complement is orientable and the relevant ordinary Euler class vanishes in the asserted odd-rs degree. In the odd ambient case its orientation local system agrees with that of the Grassmannian, and the Poincare-duality degree calculation is correct. The manuscript does not incorrectly treat twisted Euler classes as ordinary ones. I checked the cohomology presentation against [Carlson, Corollary 2.3](https://arxiv.org/pdf/1611.01175v2).

5. **Rank-one refinement.** For even d the Euler-square coefficient must be a rational square, equivalently an integer square for the stated positive integer coefficient. For odd d the oriented double cover is the odd-dimensional complex quadric; the hyperplane class changes sign under its deck transformation. The anti-invariance and negative-square arguments exclude equality in both parities of s. The pullback Pontryagin class and nonvanishing degrees used are consistent.

6. **Mod-two bound.** Applying the Cauchy identity to w(S)^(-d) gives the claimed Schur coefficients modulo two. The rectangular Schur classes form a basis, so the highest nonzero coefficient supplies a necessary rank bound. This agrees with the unoriented presentation recalled in [Matszangosz–Wendt, Section 3.1](https://doi.org/10.1007/s00209-024-03556-y). The computation is correctly described as a necessary condition, not an existence criterion.

7. **Exact exceptional case mu_R(4,1)=11.** The double cover of Gr_2(R^4) gives H^2=0 and nonzero p_1 of the tautological bundle. A putative six-dimensional admissible space would have an oriented rank-two complement with zero Euler square but nonzero p_1, a contradiction. The eleven-measurement upper bound is supported by the independently rerun exact algebra described below. Together these prove precisely the claimed special case.

8. **Odd degree.** A disjoint real projective plane can be perturbed within the disjoint locus to a generic complementary plane. Odd complex intersection degree forces a real point by conjugation. The factorial valuation formula and rectangular Schur-degree identity are consistent. The manuscript preserves credit to Xu and does not infer existence from even degree.

9. **Clifford spaces, cofactor bound and lifts.** The skew-generator base cases and periodic construction give H(x)^T H(x)=||x||^2 I and the claimed dimension rho(d). The cofactor map A+i adj(A)^T is invertible for real rank-at-least-d-1 matrices and odd for even d. Its projective complex-bundle obstruction gives kappa<=2 nu_2(d)+2. I checked [Causin, Proposition 2.2 and Theorem 3.5](https://arxiv.org/pdf/0911.1810v1). The manuscript prudently avoids relying on the broader wording of Causin's Proposition 3.6. Matching constructions justify the asserted exact families; the block lift is injective in five parameters and has rank at least d-1. No unmatched upper and lower bounds are treated as equal.

## Independent exact executions

I regenerated both Xu variants from their measurement rows using the **SymPy backend**, bypassing the submitted C++/GMP row-reduction helper. SymPy version: 1.14.0. Both runs passed. Each matrix had rank 11 with free coordinates 11–15 in zero-based row-major indexing. Each affine Macaulay matrix had rank 106, with 20 free monomials and a degree-20 characteristic polynomial. Sturm variations were 10 at both infinities, so there were zero real roots. Each infinity-chart matrix had full column rank 56. The regenerated multiplication matrices, integer polynomials and sign sequences matched the saved certificates. Elapsed times were approximately 37 seconds per variant.

The mathematical use of those calculations is valid: row relations already imply the necessary eigenvalue equation at every common zero, because the free-monomial vector contains the constant one. No unsupported claim of a complete Groebner basis or quotient-algebra basis is needed. The separate infinity-chart calculation closes the projective-chart gap.

The construction suite also passed under Python 3.12.14 with SymPy 1.14.0: 25 anti-diagonal constructions; all norm coefficient identities in sizes 1,2,4,8,16,24,32; five-dimensional lifts in sizes 4,12,20; 256 factorial-degree/parity/bound checks through d=32; and the listed exact values and unresolved intervals. The complete bounds table through d=16 regenerated successfully. These finite tests supplement the general proofs, rather than establish the topological theorems.

Reproduction from the bundle root:

```sh
python code/verify_xu.py --variant both --backend sympy --output /tmp/ra17-independent-results
python code/test_constructions.py
python code/bounds.py --max-d 16 --output /tmp/ra17-independent-bounds.json
```

**Runtime clarification:** use Python 3.10 or later, since `bounds.py` calls `int.bit_count()`. An initial Python 3.9.6 construction run passed the matrix checks and then stopped at that unsupported method; the complete suite was rerun successfully under Python 3.12.14. This was an environment requirement, not a mathematical failure. A pure-SymPy run needs no C++ compiler or GMP development headers.

Review execution logs were saved as `ra17-independent-exact.log`, `ra17-independent-constructions-py312.log`, and `ra17-independent-bounds.log` in the [verification directory](verification/).

## Resolution boundary and recommendation

The exact special case (4,1), the universal constructions and lower bounds, odd-degree criterion, and stated corank-one exact families pass this informal audit. The intervals 138<=mu_R(12,5)<=139 and 246<=mu_R(16,7)<=247 remain nontrivial gaps for the methods supplied. No proof of a general sharp formula or classification is provided. Record this as additional audited partial progress under the existing permanent RA-17 ID, preserving the original mathematical target and prior-source attribution. Do not mark RA-17 Solved or Lean verified. This review makes no novelty or exhaustive literature claim; it does not replace the separate submission checks for duplicate prior full solutions or author affiliation.
