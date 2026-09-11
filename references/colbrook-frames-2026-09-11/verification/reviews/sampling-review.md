# FR-02 / FR-10 sampling manuscript: independent review — 2026-09-11

**Verdict: PASS for the stated partial regimes.** The sharp leading constants for real Walsh sparsities 1, 2, 3 and 4, full-space sampling of an arbitrary unitary matrix, and sparsity s=N-o(N) for flat unitary matrices are proved. Neither canonical problem is resolved throughout its full sparsity range. No material mathematical gap was found in the stated theorems.

This is an independent Codex mathematical audit. The complete manuscript and `verify_sampling.py` were read. The probabilistic proofs, dependence calculations, constants and threshold quantifiers were checked independently rather than inferred from the attached verification labels. No manuscript or canonical file was edited; this review does not certify publication or historical priority.

## Complete-source identity and locators

Reviewed source: `.cache/colbrook-frames-submission/frames_submission/manuscript/sampling_thresholds.tex`, including its standalone preamble and bibliography. SHA256 below hashes the **complete original UTF-8 text after CRLF-to-LF replacement, with no trimming or terminal-newline removal**, re-encoded as UTF-8.

| Input | Normalized bytes | SHA256 |
| --- | ---: | --- |
| Complete `sampling_thresholds.tex` | 17747 | `1412478dd874f64675071687d89e1cb73a729e03a5c307844276138f79ad902e` |
| Canonical FR-02 README before this update | 3498 | `045a402aa684b60c30cfa895b9837f0b46eef0adf26d3d0fcfa7afd026b51194` |
| Canonical FR-10 README before this update | 2971 | `e9c9150aa04a35d1db581d1fd6d4078e61c9424219d954288d46ef2e7e6d5e6d` |

| Claim | Original source locator | Verdict |
| --- | --- | --- |
| Low-sparsity Walsh thresholds | Theorem 1, `thm:low`, line 36 | PASS for fixed k=1,2,3,4 |
| Full and nearly full sparsity | Theorem 2, `thm:full`, line 53 | PASS within its stated unitary/flatness assumptions |
| Balanced four-cell second moment | Lemma 3, `lem:types`, line 68 | PASS |
| Three-sign MGF envelope | Lemma 5, `lem:mgf`, line 131 | PASS |
| Two-sparse argument | Section 3, line 114 | PASS |
| Three-sparse argument | Section 4, line 125 | PASS |
| Four-sparse argument and exact rate comparisons | Section 5, line 190 | PASS |
| Occupancy argument and minimum-sample uniformity | Section 6, line 243 | PASS |

The intervening remark is numbered 4 by the shared theorem counter, so the MGF lemma is Lemma 5.

## Exact canonical scope and primary sources

FR-10 uses N=2^d, real sparse vectors, independent uniform Walsh rows with replacement, distortion 1/2 and success probability 0.9. Theorem 1 matches that model exactly by taking tau=0.9. Its constants are per d, rather than per log N: d=log N/log 2. The theorem concerns fixed k, not arbitrary k growing with N.

FR-02 instead uses cyclic complex Fourier matrices for every integer N, complex sparse vectors, distortion 1/3 and success probability 2/3. The Walsh k=2,3,4 results do not transfer to that group. Theorem 2 does apply to its full and nearly full regimes because cyclic Fourier matrices are flat unitary for every N. For complex U, full-space and sparse distortion in that theorem must be understood over complex vectors, as required by its spectral Gram identity and conjugated-row test vector; for real Walsh matrices they are over real vectors. This is the scope used here.

[Haviv–Regev, Theorem 1.1](https://arxiv.org/html/1507.01768) treats independently sampled rows with replacement of flat/bounded-entry unitaries and gives the general upper bound with log-squared sparsity dependence. [Błasiok et al., Theorem 3.1](https://arxiv.org/html/1903.12135v3) concerns a specified intermediate Walsh sparsity range and Bernoulli row inclusion. Its subgroup obstruction is not an all-parameter formula or a cyclic-Fourier conclusion. The submitted endpoint arguments are separate from those general-range results.

## Balanced type lemma: exact dependence audit

For fixed q>1/4, selecting k0 nearest qm in the residue class m modulo 3 gives k0=qm+O(1) and ell=(m-k0)/3=(1-q)m/3+O(1). For sufficiently large m these are valid nonnegative counts, with k0>ell. There are `(N-1)(N-2)/6` two-dimensional character subspaces and four choices of distinguished cell, giving L=2(N-1)(N-2)/3. The multinomial mass has logarithm `-m D(q||1/4)+O(log m)` by Stirling's bounds. Its rate is exactly the binary divergence because the other three cells share the remaining mass equally.

If two character planes intersect trivially, four independent linear functionals give independent two-bit label sequences, so the two events are independent. If they share a line, the common character's favored count must be k=k0+ell. Since k/m tends to (1+2q)/3>1/2, inconsistent favored values give disjoint events for large m.

For consistent favored values, condition on the complete common-character sequence. Conditional on its having k favored positions, the two remaining character sequences are independent fair-bit sequences. Each event has the same conditional probability

`a = binom(k,k0) binom(m-k,ell) 2^(-m)`.

The probability of the required common count is s=binom(m,k)2^(-m), so p=sa and the joint probability is sa^2=p^2/s exactly. The shared-character rate is J(q)=D((1+2q)/3||1/2). This verifies the dependence correction; replacing exact balanced types by arbitrary overloaded cells would not justify the same formula.

For a fixed character plane, choose one of its three nonzero lines, then any other plane containing that line. There are N/2-2 such planes, and two compatible labels on each. Thus each event has 6(N/2-2)<=3N potentially positive-covariance partners. Different labels on the same plane are disjoint, since k0 differs from ell. Dropping negative covariances and bounding diagonal variances by p gives

`Var Z/(E Z)^2 <= 1/(Lp)+3N/(Ls)`.

With m=O(log N), the Stirling prefactors are powers of log N. The strict limsup conditions mI(q)/log N<2 and mJ(q)/log N<1 dominate them, and both variance terms tend to zero. Chebyshev proves existence with probability tending to one. The resulting counts differ from their prescribed fractions by O(1), stronger than the claimed o(m). All small-dimension and bounded-m concerns are excluded by the lemma's asymptotic hypotheses m tending to infinity.

## k=1 and k=2

Each Walsh column has exactly unit sampled norm, so m1=1 for every d and every tau in (0,1). For two distinct columns their inner product is r_v for a nonzero character v, and the Gram eigenvalues are 1+-r_v. Therefore delta2=max_(v nonzero)|r_v|.

The strict bad event corresponds to a fair binomial count outside [m/4,3m/4]. Rounding the endpoints by at most one changes its log probability only by O(log m), so its rate is D(3/4||1/2). Distinct nonzero characters over F2 are linearly independent; their full sequences and bad indicators are independent, even though the entire collection is not mutually independent. Pairwise independence suffices for Var Z<=E Z.

The union bound gives the upper threshold and the second moment gives the lower threshold at m/log N=1/D(3/4||1/2). When m<d the sampled rows have a nonzero common annihilator; its empirical character is identically one and delta2=1. For d<=m below a fixed subcritical multiple of d, the divergence error is uniform and E Z grows as a positive power of N divided by a polynomial in log N. These facts establish uniform lower failure over every smaller positive m, without assuming monotonicity of the success probability.

## k=3: the sharp positive tail and the other deviations

After translating a support, any three distinct Walsh frequencies are {0,a,b} with a,b independent. Frequency translation merely multiplies each measurement row by a sign and preserves its Gram matrix. Thus at most N^2 translated Gram types are needed. An independent global sign converts (1,epsilon_a,epsilon_b) into three independent signs without changing squared measurements.

For fixed s>=0, differentiating log cosh(s sqrt u) shows that its first derivative is proportional to tanh(v)/v. This ratio decreases for v>0 because `v sech^2(v)-tanh(v)<0`, equivalently `2v<sinh(2v)`. Hence the asserted function is concave, including its continuous derivative at u=0. The Gaussian exponential identity and Jensen's inequality applied pointwise to the three squared coefficients give the MGF envelope. The equal-magnitude vector attains the comparison distribution, namely squared response 3 with probability 1/4 and 1/3 with probability 3/4.

Optimizing the Bernoulli MGF at energy 1+u gives the displayed rate D(1/4+3u/8||1/4), in the relevant range around u=1/2. In particular the upper-deviation rate is I3=D(7/16||1/4).

For the lower tail, the sign expansion gives E X=1 and E X^2=3-2 sum x_j^4<=7/3. Thus Var X<=4/3. One-sided Bernstein is valid for the centered variable 1-X with upper bound 1; a two-sided bound of 1 is not needed. At u=1/2 its exponent is 1/12. The manuscript's exact rational upper bound I3<=40191/482944<1/12 verifies strict separation of those rates.

For every three-column Gram matrix, positivity and trace three imply ||G-I||<=2. A 1/m-net on the real unit sphere gives quadratic approximation error at most 4/m and has polynomial cardinality. Therefore one can union bound both signs over all vectors and all N^2 Gram types, with rate I3-O(1/m). The polynomial net factor does not change the leading constant. The same bound tends uniformly to zero for all m above a fixed supercritical multiple of log N: the exponential decay eventually dominates polynomial m even when m is much larger than log N.

For the matching lower bound, a signed flat vector on {0,a,b} has squared response 3 on the chosen cell and 1/3 elsewhere, so its energy is 1/3+8q/3. This violates the upper bound exactly when q>7/16. The dependence condition for balanced types holds strictly at the threshold: the logarithmic identity for 16(I3-2J) reduces to `7^7 2^32>3^3 5^20`. Hence for any fixed c<2/I3, choose one q>7/16 close enough that cI(q)<2 and cJ(q)<1. The type lemma gives a violation uniformly for d<=m<=c log N. For m<d, delta3>=delta2=1. This proves the claimed threshold and the minimum-sample statement for every fixed success level tau in (0,1).

## k=4: affine planes and affine rank three

A four-point Walsh support has affine rank two or three. Rank-two supports are exactly affine planes; after translation they contain all four characters of a two-bit system. Diagonalizing their empirical Gram matrix by the four-by-four Walsh transform gives eigenvalues 4C_j/m. Thus their upper-occupancy threshold is 3/8 and their rate is I4=D(3/8||1/4). The lower-occupancy threshold is 1/8 and has a strictly larger rate. Independently, the latter comparison can be verified exactly from

`8[D(1/8||1/4)-D(3/8||1/4)] = log(7^7/(3^5 5^5)) >0`,

since 823543>759375. A union bound over O(N^2) planes gives their upper threshold.

For affine-rank-three supports, translating to {0,a,b,c} with independent a,b,c and adding a global sign gives four independent signs. Squared response is at most four, has mean one and variance at most 3/2. Bernstein with X-1<=3 gives exponent 1/16 at u=1/2; with 1-X<=1 it gives 3/40. A fixed-dimensional net and at most N^3 Gram types yield failure bounded by `N^3 poly(m) exp(-m(1/16-o(1)))`. Because the exact rational bound I4<=203/5280<1/24 implies 2/I4>48, this contribution vanishes at any fixed supercritical affine-plane sampling rate. Supports of smaller size are contained in a four-point support for all sufficiently large N.

The signed flat vector on a plane has squared response four on the chosen coset and zero elsewhere. Balanced occupancy q>3/8 therefore gives a violating vector. The second required dependence comparison is exactly `2^24 3^42>5^5 7^28`, equivalent to 24(I4-2J)>0. Continuity and the same deterministic low-m argument give the matching uniform lower threshold. This establishes the full delta4 result; it is not just a statement about affine-plane supports.

## Full and nearly full sparsity: exact occupancy constant

With row counts C_j and lambda=m/N, the Gram matrix is unitarily similar to diag(NC_j/m). Its full-space distortion is therefore exactly max_j|C_j/lambda-1|, independent of U. Binomial Chernoff bounds give upper- and lower-occupancy rates h_+(delta) and h_-(delta). Their difference has derivative -log(1-delta^2)>0 and vanishes at zero; h_- is strictly larger on (0,1). Thus the upper threshold is N log N/h_+(delta).

For the matching lower bound, the first binomial mass strictly above (1+delta)lambda gives a uniform lower tail estimate `p_N>=exp[-lambda h_+(delta)-O(log(lambda+2))]` when lambda is bounded below by 1/2 and above by O(log N). This follows by expanding the binomial mass with k=(1+delta)lambda+O(1): k=O(log N), the finite-population correction is O(k^2/m+lambda/N)=o(1), and Stirling's factorial error is O(log(lambda+2)). The integer rounding changes the exponent only by a bounded amount.

High-occupancy indicators are negatively correlated: conditional on C_i=k, C_j is Binomial(m-k,1/(N-1)), and its upper-tail probability decreases in k. The covariance of that decreasing function with the increasing overload indicator is nonpositive. Hence Var Z<=E Z=Np_N. At any fixed subcritical factor of N log N/h_+, Np_N tends uniformly to infinity and the probability of no overload tends to zero. Rank rules out full-space isometry when m<N. This proves the asymptotic for the smallest qualifying m at every fixed tau, with no appeal to exact finite-m monotonicity.

If U is flat, truncate the conjugate of any row j to s coordinates and normalize. Its inner product with the same unscaled row has squared magnitude s/N. Each sampled occurrence of that row therefore contributes s/m to its sampled energy. All other contributions are nonnegative, so sparse upper isometry requires `C_j<=(1+delta)m/s` for every j. In lambda units the effective distortion is delta'_N=(1+delta)N/s-1, which tends to delta whenever s=N-o(N), with no additional rate requirement on N-s.

The binomial estimates remain uniform for this convergent distortion sequence. For m>=s, lambda>=s/N>=1/2 eventually, including the interval s<=m<N that the full-space rank argument would not cover. For m<s, rank on any fixed s-column support gives a sparse null vector. Thus the same leading lower constant applies. The full-space upper bound supplies the sparse upper bound. This confirms both the near-full regime and its minimum-sample uniformity.

For FR-02 the resulting leading constant per N log N is `1/[(4/3)log(4/3)-1/3]`; for FR-10 it is `1/[(3/2)log(3/2)-1/2]`. These are with-replacement results. They say nothing equivalent about sampling every row once without replacement.

## Code audit and limitations of diagnostics

The complete `verification/verify_sampling.py` was read. Its rational logarithm bounds use the positive atanh series with a valid geometric upper bound on the tail; its two critical I-2J comparisons are integer comparisons. The incidence formula and shared-character joint probability are checked exactly, including enumeration of all 8^6 three-bit row sequences in one small case. I independently derived these identities above.

The remaining exhaustive Gram calculations use floating-point eigensolvers and tolerances; they are numerical diagnostics, not exact certificates. The finite MGF grid likewise does not prove the uniform MGF inequality. Optional Monte Carlo for k=4 checks only affine-plane supports and is correctly labeled as not full RIP. The analytic affine-rank-three bound is essential for the theorem. The code neither proves asymptotic thresholds by simulation nor assumes that a finite verification label settles all sparsities. Root-run execution results should be retained separately from this mathematical audit.

## Recommended canonical treatment

- **FR-10: Partially resolved**, if the catalog records established regimes: k=1 exactly; sharp fixed-k leading constants for k=2,3,4; and the full/nearly full regime. Arbitrary intermediate k, including k growing with N, remains unresolved.
- **FR-02: Partially resolved**, on the same regime-recording convention: sharp leading asymptotics for s=N-o(N), including s=N. The Walsh fixed-sparsity results are not cyclic-Fourier results. The sharp order uniformly over every 2<=s<=N remains unresolved.

Neither entry should receive a blanket solved status. The results are leading asymptotics for fixed distortion and success levels, not exact finite-dimensional minima or a uniform all-sparsity formula. No mathematical repair is needed; explicitly stating the complex-vector convention in Theorem 2 would improve exposition without changing its proof.
