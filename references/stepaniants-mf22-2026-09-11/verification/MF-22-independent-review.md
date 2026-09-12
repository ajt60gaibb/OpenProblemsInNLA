# Independent mathematical review: MF-22

Reviewer: Codex agent `/root/review_aa01`  
Date: 11 September 2026  
Author of reviewed proof: George Stepaniants  
Verdict: **PASS for the complete canonical MF-22 target.** This is independent mathematical agent review, not external human peer review or formal verification.

## Frozen source and exact scope

The reviewed file is `/tmp/nla-fresh-round1/mf22/RESULT.md`, SHA-256 `4b2b030d0284014d2eabfc79ce56c4293bc83be7cb80f86deda31d3dddab5f4f`.

The conclusion reviewed is eventual invertibility and the bound κ2(Hn(ρ))≤Kρ n for each fixed real ρ>0, with Kρ independent of n. It is stronger than the requested unspecified polynomial bound. It covers exactly the uncorrected pure block Toeplitz family at the retained MF-22 path, with n counting its 2-by-2 blocks. It makes no uniform-in-ρ assertion and allows finitely many exceptional small sizes, exactly as the target permits.

I independently read the canonical statement, the complete candidate, and the primary source's block-coefficient displays (5.22) and following (5.32), its definition of the j−k Toeplitz orientation, and Proposition 5.14. I rederived the recurrence and finite Green estimate and implemented separate exact coefficient checks. I did not author or collaborate on the candidate before this review.

A preliminary draft had the incorrect literal value Rr(−i)=conj(a). I independently flagged that error; the frozen source correctly states Rr(−i)=−ia. The intended nonvanishing argument was not affected, and all checks below concern the corrected frozen version.

## 1. Exact finite-matrix recurrence

Multiplying the canonical Hn by 80 gives coefficient blocks 6i times the displayed integer B blocks minus r times the integer C blocks. Their entries are exactly the six scalars A,B,C,D,E,F and the remaining constants in equation (1). In particular, the lag −1 block has only its first column nonzero. Therefore the right boundary is un=0 and no condition is imposed on vn. At the left boundary, u−1=v−1=v−2=0 are precisely the missing Toeplitz terms. These remain correct at n=1.

Solving a block row for (u(j+1),vj) produces the matrix L and the four-state transfer in equation (3), with det L=24a. Since Im(a)=−10r is nonzero for r>0, no positive parameter makes the transfer undefined. The state wj, forcing Gfj, initial state e u0 and terminal scalar condition eT wn=0 in equation (4) encode all 2n equations and all their boundary conditions, with exactly one free initial scalar.

## 2. Generating function and coprimality

Summing the two homogeneous row equations with u0=1 gives equation (5): the advance term contributes (U−1)/z, and the backward terms contribute zU,zV,z²V. Thus the stated numerator and denominator in U=N/d follow directly. Both expansions, including the common factor 24, pass my separate exact polynomial checks.

For a possible common root, Aℓ=Bh and αℓ=h² imply either h=ℓ=0 or Ah=Bα, because A is nonzero. The quadratic resultant excluding the first case is correct and has strictly positive real part. In the second case the exact subtraction yields the stated factor z times a linear polynomial. The zero root cannot occur since d(0)=a≠0. The other candidate z0 has a nonzero denominator because its real part is 7r²+30>0. Substitution into N gives exactly R(r²)+ir I(r²), divided by that denominator squared. Since r>0, vanishing would force both real polynomials to vanish; the displayed combination 70R+867I is strictly negative for r²≥0. This exhausts the alternatives. Hence no numerator cancellation occurs for any permitted parameter.

The rational identity U=eT(I−zT)−1e then implies det(I−zT)=d(z)/a, because the reduced denominator d has degree four and the determinant has degree at most four and constant term one. I also checked this independently from the 2-by-2 companion-block determinant, which yields the same characteristic polynomial p/a.

## 3. Root classification and all exceptional parameters

The factorizations p=(t−1)q and q(1)=120ir are correct, so the root t=1 is simple for every positive r. The Cayley homogeneous-cubic identity is correct. The discriminant is the stated negative polynomial: its quadratic factor in y=r² has positive leading coefficient and discriminant −5280431, and the remaining terms are strictly negative.

For r≠sqrt(10), the Cayley polynomial is a true cubic and has exactly one real root and two distinct conjugate nonreal roots. A real Cayley root gives a unit-circle t; the conjugate nonreal roots give one t inside and one outside the unit circle. The exceptional points of the transformation cause no loss: Rr(−i)=−ia≠0 excludes its pole, Rr(i)=i conj(a)≠0 excludes t=0, and q(−1)=48(r²−10)≠0 excludes the point corresponding to infinity. These identities use r>0 and a≠0.

At r=sqrt(10), the Cayley polynomial is the displayed genuine quadratic with negative discriminant −14600. Its two roots remain distinct and nonreal, and t=−1 is the missing third Cayley root. It is simple since q′(−1)=−100ir at this parameter. Thus this otherwise easily missed parameter is fully covered. The additional unit root never coincides with t=1 because q(1)≠0.

Consequently T has four distinct nonzero eigenvalues: one expanding, one contracting, and two distinct unit eigenvalues, for every r>0. Its diagonalizability and the uniformly bounded remainder Rj in equation (17) follow. No claim of uniform diagonalizer conditioning in r is needed.

## 4. The expanding mode is visible at both scalar boundaries

Let Π be the expanding rank-one spectral projector. If γ=eTΠe were zero, the scalar resolvent eT(I−zT)−1e would have no pole at z=1/λ, because this eigenvalue is simple. That contradicts the proved coprimality of N and d. Thus γ≠0.

The boundary denominator $a_n=\gamma\lambda^n+b_n$, with bounded $b_n$ and $|\lambda|>1$, is nonzero for every sufficiently large n. The normalized denominator dn tends to one exponentially and satisfies |dn|≥1/2 eventually. This domination avoids any issue of unit-root phases becoming close to a resonance; no arithmetic assumption or subsequence of matrix sizes is being used. The candidate therefore establishes eventual invertibility for every large integer n, as required.

## 5. Finite Green cancellation and the spectral-norm estimate

Solving for u0 from the terminal condition gives equation (19) exactly. Since Π is a rank-one projector, Π e eT Π=γΠ holds even though eT is an ordinary transpose and the transfer matrix need not be normal. Inserting the expanding-mode decomposition into the boundary correction gives the double-projector term λ^(j−1−ℓ) ΠG/dn and exactly the three cross terms in equation (21).

For 0≤j≤n and 0≤ℓ≤n−1, the exponents in all three cross terms are nonpositive, and their other factors are uniformly bounded. If ℓ≥j, the absent forward term leaves a double-projector exponent at most −1. If ℓ<j, the large double-projector contribution cancels the forward contribution, leaving $\lambda^{j-1-\ell}(1-d_n^{-1})\Pi G$. Its magnitude is bounded uniformly because $j-1-\ell\le n-1$ and $1-d_n^{-1}=O(|\lambda|^{-n})$. All remainder powers have nonnegative indices and are uniformly bounded. Therefore every 4-by-2 Green block is bounded independently of n,j,ℓ.

The output coordinates are recovered correctly: uj is the first coordinate of wj, and vj is the second coordinate of w(j+1), including the last variable. Applying Cauchy–Schwarz to each Green row and summing over the 2n output coordinates gives $\|M_n^{-1}\|_2\le\sqrt{2}C_rn$. The fixed finite bandwidth gives ||Mn||2≤sum ||80(iBk−rCk)||2 independently of n. Multiplication by 80 leaves κ2 unchanged. This proves the stated eventual linear bound.

## Separate exact checks and review limits

I wrote `/tmp/nla-fresh-round1/mf22/independent-review/exact_identity_check.py` without using the author's checker. It implements polynomials in (r,z) over Gaussian integers using the standard library only. Its 31 exact identities check all 16 canonical block entries, det L, the generating numerator and denominator, the resultant, the two coprimality elimination steps, the Cayley identity and excluded points, the discriminant, and a direct companion-block characteristic determinant. No floating-point calculation is used. The result is saved in `independent-review/exact_identity_check.json` and bound to the frozen source hash.

The asymptotic Green argument and exceptional-parameter reasoning were checked mathematically; the finite symbolic identities alone are not presented as a proof of the infinite-size theorem. No unresolved gap was found in the complete argument. The review does not certify historical priority, the public-branch audit, final source conversion, or PDF visual quality, and does not perform any repository publication operation.

Primary source checked: M. Bogoya, A. Böttcher, M. Ferrari, S. M. Grudsky and S. Serra-Capizzano, *Condition numbers of block Toeplitz matrices and stability of space-time IgA approximations for the wave and Schrödinger equations*, arXiv:2608.24151v1, equation (5.22), equation (5.32) and its following display, Proposition 5.14: https://arxiv.org/html/2608.24151v1
