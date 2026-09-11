# Independent complete-proof review: MF-05 and MF-07

Date: 2026-09-11. Verdict: **PASS for both complete canonical targets.** Recommend **Solved, affirmative** for MF-05 and MF-07. The shared proof gives a dimension-only uniform polynomial product bound and a uniform two-family Hölder estimate of exponent 1/d on every spectral-norm bounded region. No mathematical correction is required. This is independent Codex-agent review, not external human peer review or formal certification.

## Full source identity and review scope

I read the complete 294-line source `.cache/proposed-solutions/nla_submission/MF-05_MF-07/uniform_growth_and_holder.tex`, including all statements, proofs, constants, sharpness examples, scope qualifications and references. I compared both actual canonical files `matrix-functions-and-stability/MF-05/README.md` and `matrix-functions-and-stability/MF-07/README.md` in full. No source or canonical files were edited.

Complete UTF-8 source SHA256, after replacing CRLF with LF, with no trimming or other normalization:

`233df2a51c7666e447ac14bd51558704a3d3cb53db3e1738b79fe63d109406b5`

The numbered results share one counter:

| Result | Source locator |
| --- | --- |
| Theorem 1: uniform product bound | line 45; proof begins line 195 |
| Theorem 2: uniform Hölder estimate | line 59; proof begins line 247 |
| Lemma 3: rounded approximate extremal norm | line 69 |
| Lemma 4: triangular damping | line 106 |
| Proposition 5: quantitative comparison at all thresholds and lengths | line 130 |
| Corollary 7: controlled eccentricity | line 224 |
| Sharpness and verification boundaries | section beginning line 263 |

The intervening principal-block remark is numbered 6. This review concerns mathematical completeness, not the historical preparation environment's submission hold or an exhaustive search for priority. The manuscript's blank author field supplies no human-authorship evidence.

## Exact targets and source verification

MF-07 requires a constant Theta_d depending only on d for every nonempty compact complex matrix family of joint spectral radius one, with every switching product of length k bounded by Theta_d(Lk)^(d-1), where L is the largest spectral norm in the family. Theorem 1 establishes exactly this, and in fact allows arbitrary nonempty bounded families over either field.

MF-05 asks for one Hölder constant valid for **both varying families** in a neighborhood of every fixed compact family, not merely a pointwise estimate with one argument fixed. Theorem 2 provides the stronger bound

`|rho(M)-rho(N)| <= d(2d+1) L^(1-1/d) d_H(M,N)^(1/d)`

for every pair of nonempty compact families in the radius-L spectral-norm ball. To see the canonical quantifiers explicitly, fix M0, let L0=max_(A in M0)||A||_2, choose neighborhood radius one and L=L0+1. Every family at Hausdorff distance less than one from M0 lies in this common norm ball. The displayed constant therefore works simultaneously for all pairs M,N in that neighborhood. This also works when rho(M0)=0. For d=1 the manuscript proves the sharper Lipschitz constant one.

Primary sources accessed on 2026-09-11:

- [Epperlein–Wirth, The joint spectral radius is pointwise Hölder continuous, v2](https://arxiv.org/html/2311.18633v2), §2, Conjecture 3 (L1) and (L3), states the two targets with the complex Hausdorff model and dimension-only trajectory constant. The distinction between local and pointwise regularity is explicit there. Its Lemma 27 addresses dimension two, whereas the submitted comparison applies in every dimension. [Journal DOI](https://doi.org/10.1016/j.laa.2024.09.016).
- [Epperlein–Wirth, Auerbach bases, projection constants, and the joint spectral radius of principal submatrices, v1](https://arxiv.org/html/2504.17505v1), introduction and §3, discusses norm normalization and the obstruction to controlling all higher-dimensional principal submatrices. The manuscript's caution is consistent with that source; the proof does not assume the false principal-submatrix monotonicity property.

The universal proof below uses elementary finite-dimensional arguments supplied in the manuscript rather than an unproved external regularity or extremal-norm result. Source checks confirm scope and background, not novelty. The separate MF-06 Lipschitz lower-bound target is not resolved or claimed here.

## Independent proof audit

### Lemma 3: approximate extremal norm and complex rounding — PASS

For a>rho, choose b strictly between rho and a. The defining root limit gives a_k<=b^k for all sufficiently large k, while finitely many earlier terms are finite by boundedness of the family. Thus sup_k a^(-k)a_k is finite even when rho=0. The k=0 term bounds the proposed v below by Euclidean norm; the uniform upper bound makes it a finite continuous norm. Each generator contracts v by at most a because adjoining it to a word gives another allowed word. No compactness or finite cardinality of the generator family is needed here.

The v-unit ball is compact and has nonempty interior. Maximizing the absolute determinant of d columns over that ball produces an invertible matrix T. Every maximizing column has v-norm one: otherwise scaling it up would increase the determinant. Replacing one column by a vector in the ball shows that the corresponding coordinate of T^(-1)x has modulus at most one. This uses complex determinant multilinearity and absolute values equally well over C; it is not limited to real determinant signs. Consequently ||z||_infinity<=v(Tz)<=||z||_1.

For T=QDR*, QD=TR. The Euclidean norm is unchanged by R, so the infinity/one norm inequalities give ||z||_2/sqrt(d)<=v(QDz)<=sqrt(d)||z||_2. The scaling w=sqrt(d)v(QDz) therefore gives ||z||_2<=w(z)<=d||z||_2. It also gives ||D^(-1)Q*A QD||_w<=a for every generator. Finally |(Q*A Q)_ij|<=||A||_2<=L, hence |B_ij|<=L sigma_j/sigma_i. All orientation and scaling factors agree.

This argument uses an approximate extremal norm at a>rho. It never asserts existence of an exact extremal norm at rho for a reducible or defective family.

### Lemma 4: triangular damping — PASS

Each sign matrix S_l is orthogonal or unitary and self-adjoint. The coefficients (1+t_l)/2 and (1-t_l)/2 are nonnegative and sum to one. The map Phi_l is therefore a spectral-norm contraction. In a block crossing that cut it multiplies the entry by t_l; elsewhere it acts identically.

Composing the maps gives multiplier h_i/h_j on lower block (i,j), since h is nonincreasing. The upper blocks of X vanish, while diagonal blocks have multiplier one. Thus the composite equals HXH^(-1) exactly. This is a legitimate norm contraction on the stated block-lower-triangular space. It would not justify the same claim for a general full matrix, which the proof never makes. A single block is also covered.

### Proposition 5: truncation, rescaling and arbitrary switching — PASS

The singular values in D are sorted decreasingly. For threshold s>=1, every removed upper block crosses a consecutive singular-value ratio greater than s. All other ratios are at least one. Hence its old-coordinate entries obey |E_ij|<=L/s; the Frobenius norm bounds the spectral norm by dL/s. Norm equivalence gives ||E||_w<=d||E||_2<=d^2L/s, and so every C=B-E has w-operator norm at most u=a+d^2L/s.

Submultiplicativity in this one common w norm bounds every length-t C product by u^t in that norm, hence by d u^t in spectral norm. This includes the empty product with the harmless upper bound d. No assumption about spectral radii or norms of principal blocks has entered.

Capping each consecutive singular-value ratio at s produces a diagonal D' with condition number at most s^(d-1). The diagonal H=D'^(-1)D is constant within each block and nonincreasing between blocks: a wide old gap q>s contributes ratio q/s>1 to H, and every uncapped gap contributes one. Products of the C's remain block lower triangular. Applying Lemma 4 to each **whole product** gives the same d u^t bound for the corresponding products of C'=HCH^(-1). This avoids multiplying a per-factor constant d to the total word length.

Although upper blocks are amplified by H, their entries remain small by a separate direct estimate. The conjugated full generator is B'=D'^(-1)Q*A QD'. Across every nonzero E' block, D' has at least one ratio exactly s, and all other ratios are at least one. Therefore |E'_ij|<=L/s and ||E'||_2<=dL/s=v. This statement is still true when s=1, when a gap equals rather than exceeds s, and when there are no wide gaps.

For any fixed switching word of length n, expansion by the k locations occupied by E' gives k+1 C' segments, possibly empty. Their lengths sum to n-k. The norm of each such term is bounded by d^(k+1)u^(n-k)v^k. There are binomial(n,k) choices, so the complete sum is bounded by d(u+dv)^n=d(a+2d^2L/s)^n. Undoing the D' similarity costs at most s^(d-1); Q costs nothing. The bound is uniform in the switching word, and taking its supremum proves the displayed bound with a.

All norm and coordinate choices disappear from the right-hand side before taking a down to rho. Therefore no convergence of Q,D,w, no common subsequence and no exact extremal norm is necessary. This proves

`a_n <= d s^(d-1) (rho+2d^2L/s)^n`

for every s>=1 and n>=0. Both quantifiers are needed in the later corollary; the manuscript proves them simultaneously.

### Theorem 1 and MF-07 — PASS

For d>=2 set m=d-1. When rho>0, rho<=L and the choice s=2d^2Ln/(m rho) is at least one for every n>=1. Substitution produces exactly

`d (2d^2Ln/(m rho))^m rho^n (1+m/n)^n`.

Using (1+m/n)^n<=exp(m) gives the manuscript's constant Theta_d=d(2ed^2/(d-1))^(d-1), its power (Ln)^(d-1), and its power rho^(n-d+1). Negative exponents of rho when n<d-1 cause no issue because this case assumes rho>0. At rho=1 this is precisely the entire canonical MF-07 assertion with a dimension-only constant.

When rho=0, keeping n fixed and sending s to infinity gives zero for every n>=d because the remaining power is s^(d-1-n). Thus every such product is zero. This stronger auxiliary statement follows from the already proved comparison and does not rely on a separate nilpotence theorem. For d=1, the joint radius is the supremum of absolute scalar generators, so both growth and zero-radius statements are immediate. L=0 is separately trivial.

### Corollary 7 and Theorem 2: uniform two-family Hölder bound — PASS

For epsilon in (0,2d^2L], the threshold s=2d^2L/epsilon is at least one. Proposition 5 gives a_k<=d s^(d-1)(rho+epsilon)^k for every length k, with one constant valid for all k. Consequently the supremum defining p_epsilon is finite and satisfies ||x||_2<=p_epsilon(x)<=d s^(d-1)||x||_2. Its generator bound is rho+epsilon and its eccentricity is at most d s^(d-1). The positive denominator rho+epsilon prevents a zero-radius singularity.

Every perturbation E has p_epsilon-operator norm at most the eccentricity times ||E||_2. If delta=d_H(M,N)>0, compactness gives for each B in N an A in M within distance delta. For delta<=L choose s=(L/delta)^(1/d) and epsilon=2d^2L/s. The two perturbation terms become respectively 2d^2 L^(1-1/d)delta^(1/d) and d L^(1-1/d)delta^(1/d). Their sum is exactly d(2d+1)L^(1-1/d)delta^(1/d).

The joint radius of N is bounded by its largest generator operator norm in any fixed equivalent norm, by submultiplicativity and norm independence of the root limit. This gives the one-sided comparison; interchanging M and N gives the absolute difference using the same constant. This is genuine local two-family continuity rather than an estimate whose constant depends on one variable family. At delta=0 the compact families coincide. At delta>=L, both radii lie in [0,L], and the stated right side is at least L. At d=1 the supremum of scalar moduli is Hausdorff 1-Lipschitz. All canonical boundary cases are therefore included.

### Sharpness and exclusions — PASS

For the single upper Jordan block I+N, the top-right entry of its nth power is binomial(n,d-1). Its norm is at least that entry's modulus, proving that the exponent d-1 cannot be decreased with a constant independent of n. The individual matrix norm is fixed for this example, so the factor L does not affect that conclusion.

For the upper nilpotent shift N, adding delta E_d1 makes a weighted cyclic shift with characteristic polynomial z^d-delta. Its eigenvalues have modulus delta^(1/d), its columns are orthogonal with lengths delta,1,...,1, and its spectral norm is at most one for 0<delta<=1. The singleton Hausdorff distance is exactly delta. This proves sharpness of the exponent at the fixed zero-radius singleton; d=1 also has the analogous scalar conclusion. The constants themselves are expressly nonoptimal.

The proof allows reducible families, arbitrary switching, infinitely many generators and complex matrices. It does not infer a Lipschitz lower bound with exponent one for MF-06, nor does it provide an algorithm for computing the joint spectral radius or the existence-defined extremal norms.

## Diagnostics and evidential limits

I inspected the complete `verification/verify_triangular_comparison.py`. Its exact rational check verifies one block-damping identity; its numerical tests sample real/complex lower block matrices and finite products after diagonal rescaling. The implementation checks the relevant old and new perturbation bounds and whole-product damping and does not estimate a joint spectral radius from a finite word search. These are suitable supporting diagnostics, but their finite ranges and floating-point tolerances cannot prove the universal bounds.

Fresh diagnostic runs are coordinated separately by the parent agent. This reviewer did not duplicate those runs, and the PASS verdict does not depend on their supplied labels or numerical outcomes. The crucial identities, every-word expansion, limiting argument and target quantifiers were checked analytically above.

## Final status recommendation

**MF-05: Solved, affirmative**, including every nonempty compact complex family, reducible cases and zero joint spectral radius, with both neighboring families varying. **MF-07: Solved, affirmative**, in every dimension with Theta_d depending only on d and with no cardinality or family-dependent factor. There are no remaining cases of either displayed canonical target under the reviewed model. Retain their permanent IDs, original targets and historical partial-result evidence when recording these resolutions.
