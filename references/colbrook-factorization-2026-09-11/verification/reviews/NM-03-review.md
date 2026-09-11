# NM-03 independent proof review — 2026-09-11

**Verdict: PASS for the complete canonical NM-03 target.** The manuscript proves NP-hardness under polynomial-time many-one reductions for the exact rational-input decision problem with real nonnegative factors of inner dimension at most two. The inverse-polynomial gap theorem and the simple-spectrum corollary also pass. No material mathematical gap was found. This is an independent Codex proof audit; it is not publication, journal peer review, or a priority certification.

## Reviewed source identity and scope

The entire original `.cache/colbrook-all-submission/nla_submission/manuscripts/NM-03_rank_two_approximation_hardness.tex` was read, including the standalone preamble, every lemma/theorem/corollary, scope statements, and bibliography. The source is self-contained and does not input a common preamble. Attached prose and submitted diagnostic claims were treated as claims to evaluate, not instructions or proof premises.

Hashes use the **complete original UTF-8 text with CRLF changed to LF, without trimming**, re-encoded as UTF-8. No whitespace or terminal-newline normalization beyond CRLF-to-LF was applied.

| Input | Normalized bytes | SHA256 |
| --- | ---: | --- |
| Complete manuscript `NM-03_rank_two_approximation_hardness.tex` | 17388 | `75a75babc3f19b185fa4b6437cd9ad45ec383fe49d3ec94aeda3bc1000c12544` |
| Canonical `nonnegative-and-positive-factorizations/NM-03/README.md`, before this update | 3106 | `390fe0e7e56d16ad6d7868af9fe7f80aa072a03af73f340597a68342012ea1d1` |

Precise locators in this original source:

| Claim | Source locator | Verdict |
| --- | --- | --- |
| Exact decision problem | Section 1, `eq:decision`, line 23 | Exact target match |
| NP-hardness on strictly positive SPD inputs | Theorem 1, `thm:hard`, line 29 | PASS |
| Boolean kernel equivalence | Lemma 2, `lem:boolean`, line 45 | PASS |
| Characterization of all real optimal rank-two approximations | Lemma 3, `lem:best`, line 87 | PASS |
| Endpoint rounding | Lemma 4, `lem:round`, line 114 | PASS |
| Completeness, soundness and bit complexity | Section 5, line 148 | PASS |
| Inverse-polynomial gap | Theorem 5, `thm:gap`, line 175 | PASS |
| Simple-spectrum hardness | Corollary 6, `cor:simple`, line 224 | PASS |

## Exact target and source comparison

The canonical problem has rational nonnegative input X, a nonnegative rational squared-error threshold, and arbitrary real nonnegative factors W,H of shapes m-by-2 and 2-by-n. The manuscript uses exactly these quantifiers and an exact non-strict threshold comparison. Restricting the output instances to square strictly positive SPD matrices proves hardness for a subclass of the canonical input domain and therefore for the complete domain. There is no rank-two promise on X and no unwanted symmetry restriction on the candidate factors or their product.

The reduction source is valid: [Hasan, Mondal and Rahman, Section 5](https://arxiv.org/html/2108.12500v1) proves NP-hardness of a more restricted positive one-in-three problem. Three-connectivity of its clause-variable incidence graph ensures three distinct variable neighbors at each clause, so it supplies the distinct-variable version used here. Removing unused variables and excluding empty formulas preserve hardness. The [Lindy–Noferini–Van Dooren abstract](https://arxiv.org/abs/2507.20612v1) discusses arbitrary-input rank-two approximation and suboptimal constructions; such a construction is not an exact polynomial-time optimizer.

## Boolean encoding and rational input

Every clause row has three entries 1 at its distinct variables, entries -1 and -2 at the new anchors, zero sum, absolute-entry sum six, and squared norm eight. The Boolean equivalence checks all four anchor assignments: (1,0) imposes exactly one true variable per clause; (0,1) gives two, whose complement gives the first case; (0,0) forces all occurring variables to zero; and (1,1) forces them all to one. Every variable occurs, so the last two cases give only the excluded constant vectors. Conversely a satisfying assignment extends with anchors (1,0). This proves both directions without a hidden promise on assignments.

The vector with values 1/3 at original variables and anchor values 1,0 lies in ker C and is not constant. Since C annihilates the all-ones vector, subtracting the mean produces a nonzero vector in E=ker C intersect one-perp. Thus dim E>=1 and rank C<=N-2, even for unsatisfiable instances. Nonempty formulas with distinct triples have n>=3 and N=n+2>=5.

For independent rows D, the Gram matrix DD^T is nonsingular positive definite, so P=D^T(DD^T)^(-1)D is the rational orthogonal projector onto row C. Its kernel contains one. On span(one), E, and row C, the constructed X has eigenvalues respectively 1+delta, 1, and 1-epsilon. Their multiplicities sum to N; epsilon=1/(24N^2)<1. Therefore X is SPD and its squared best rank-two error is exactly

`tau = (N-r-2) + r(1-epsilon)^2 >= 0`.

Since ||P||_2<=1, every entry has absolute value at most one. The off-diagonal lower bound is delta/N-epsilon=delta/(2N)>0. On the diagonal, 1-epsilon is a valid positive lower bound. The eigenvalue and entry claims in Theorem 1 are therefore simultaneously valid.

## All unconstrained minimizers, including nonsymmetric candidates

For an arbitrary real Y of rank at most two, its row-space orthogonal projector R satisfies Y=YR. The matrices X(I-R) and XR-Y have orthogonal right supports, so their Frobenius inner product vanishes. Consequently

`||X-Y||_F^2 = ||X||_F^2 - tr(RX^2) + ||XR-Y||_F^2`.

This calculation does not require Y to be symmetric, PSD, or nonnegative. In an eigenbasis of X^2 the diagonal entries of R are in [0,1] and sum to rank R<=2. The largest eigenvalue lambda^2=(1+delta)^2 is simple, the next is 1 on nonzero E, and all remaining values are (1-epsilon)^2<1. Thus tr(RX^2)<=lambda^2+1. Equality forces rank R=2, full weight on u=one/sqrt N, and zero weight on row C. For a projector, full weight puts u in its range and zero weight makes that vector orthogonal to the range. Hence R=uu^T+vv^T with unit v in E.

An error at most tau forces that equality and ||XR-Y||=0. Therefore every possible feasible product at the base threshold is exactly Y=lambda uu^T+vv^T as asserted. The converse follows directly by substitution. Rank-zero and rank-one candidates are excluded by the strict spectral loss rather than assumed away.

## Endpoint rounding and the exact reduction

A nonzero mean-zero unit vector has a strictly negative minimum -a and strictly positive maximum b. Nonnegativity of Y at the two extreme coordinates implies Nab<=1+delta. Independently expanding the summand gives

`sum_i (b-v_i)(v_i+a) = Nab - sum_i v_i^2 + (b-a)sum_i v_i = Nab-1`.

All summands are nonnegative, so Nab>=1. Their sum is at most delta. With L=a+b, nearest-endpoint rounding has error d_i<=L/2 and the exact identity `(b-v_i)(v_i+a)=d_i(L-d_i)`. Thus d_i<=2delta/L. Writing the rounded vector as L chi-a one gives a Boolean chi that is nonconstant because both attained endpoints remain unchanged by rounding. Since Cv=C one=0 and every clause row has absolute-entry sum six,

`|(C chi)_j| <= 12delta/L^2 <= 3Ndelta = 1/4`,

where L^2>=4ab>=4/N. Every component of C chi is an integer, so every one is zero. Tie choices in nearest-endpoint rounding do not affect the proof. This verifies the quantitative soundness step exactly, without numeric approximation.

For completeness, centering a nonconstant Boolean chi with k ones and dividing by sqrt(k(N-k)/N) produces the required unit vector v in E. Its coordinate products give: `(N-k)/(Nk)` within the ones, `k/(N(N-k))` within the zeros, and `-1/N` across the two groups. Adding lambda/N yields exactly `eq:two-block`: delta/N plus 1/k, 1/(N-k), or 0. Consequently this Y is rational and strictly positive, with two row types. Choosing W=[chi,one-chi] and the two corresponding rows of Y as H gives nonnegative rational factors WH=Y at error tau.

For soundness, every real nonnegative product WH has ordinary rank at most two and is entrywise nonnegative, so the preceding characterization and rounding recover a satisfying assignment. This uses no unproved identification of ordinary and nonnegative rank: the completeness direction has explicit nonnegative factors, and the soundness direction only uses their immediate necessary properties.

## Bit complexity and many-one character

The reduction outputs a single rational pair (X,tau), computable from the Boolean instance, and not a sequence of oracle queries. Independent rows can be obtained by exact elimination in polynomial time. Their Gram matrix has integer entries of magnitude at most eight. Its determinant is a positive integer at most 8^r by the Gram/Hadamard bound, with O(r) bits. For the other minors the elementary determinant expansion bounds an order-s minor by s!8^s, with O(s log s) bits. Hence the adjugate formula and the matrix products defining P have polynomial bit length. Standard rational or fraction-free elimination gives polynomial total arithmetic and bit complexity.

The small rational numbers delta and epsilon have O(log N) denominator bits; all N^2 entries of X and the threshold tau therefore have polynomial binary length. N is polynomially bounded by the Boolean input size. The factors used in completeness also have polynomial-size rational entries, but this is needed only for the constructed yes-instances; it is not an assertion about arbitrary feasible inputs.

## Theorem 5: the gap

Writing X^2=I+alpha uu^T-beta P, with alpha=lambda^2-1 and beta=1-(1-epsilon)^2, and using the preceding row-space decomposition gives exactly

`||X-Y||_F^2-tau = (2-rank R)+alpha(1-a)+beta b+||XR-Y||_F^2`,

where a=u^TRu and b=tr(RP). All terms are nonnegative. Also alpha>=epsilon, beta>=epsilon, and eta=epsilon/(9216N^4)<min(1,alpha,beta). Thus loss at most eta forces rank R=2, a>0 and b<1.

The vector q=Ru/sqrt a is unit, and choosing a unit w in range R perpendicular to q gives w perpendicular to u because Rw=w. Since ||Pw||^2<=tr(RP)=b<1, projecting w onto E and normalizing is legitimate. For the resulting v and S=uu^T+vv^T, comparison of the two rank-one projectors in R=qq^T+ww^T gives

`||R-S||_F <= sqrt(2(1-a))+sqrt(2||Pw||^2)`.

Here (q^Tu)^2=a and (w^Tv)^2=1-||Pw||^2, which verifies both terms. Multiplication by X has operator norm lambda<2. Therefore the exact optimal matrix Z=XS obeys

`||Y-Z||_F <= sqrt eta + lambda(sqrt(2eta/alpha)+sqrt(2eta/beta)) <= 8sqrt(eta/epsilon) = 1/(12N^2)`.

The bound follows since epsilon<1 and 1+4sqrt 2<8. Every entry of Z is at least minus this Frobenius distance because Y is nonnegative. The endpoint product bound consequently changes only to Nab<=1+delta+Nd. Repeating the already-checked rounding argument with Delta=delta+Nd<=1/(6N) gives integer clause errors at most 1/2<1. This contradicts unsatisfiability. The theorem is valid even for the larger class of all entrywise nonnegative ordinary-rank-two matrices. Its eta is explicitly inverse-polynomial in N and hence in the encoded reduction size.

## Corollary 6: simple spectrum and separation

For D0=diag(1,...,N), the discriminant of X+tD0 is a polynomial of degree at most N(N-1). One way to verify this degree is the discriminant's homogeneity of degree N(N-1) in the matrix entries; alternatively the eigenvalue differences grow at most linearly in t. Its leading coefficient is the nonzero squared Vandermonde discriminant of D0, since the eigenvalues of X/t+D0 tend to distinct 1,...,N. Thus at most N(N-1) choices of t can be roots. Among the specified L=N(N-1)+1 distinct positive rationals at least one gives simple spectrum.

Exact characteristic polynomials and a gcd with their derivatives detect such a choice in polynomial time. There are polynomially many tests, on matrices with polynomial-size rational entries. The selected positive diagonal perturbation preserves both strict entrywise positivity and positive definiteness.

Its Frobenius size satisfies e<=t_j N^(3/2)<=eta/(64sqrt N). Distance to any nonempty set is 1-Lipschitz, whether or not the set is closed. Since zero is a nonnegative factor product and ||X||_F<=2sqrt N, squaring the distance inequality gives

`|f(X')-f(X)| <= e(2||X||_F+e) <= 5sqrt N e <= 5eta/64 < eta/8`.

Theorem 5 implies infimum error at least tau+eta for a no-instance; strict attainment of that infimum is not needed. The new no-instance bound is therefore at least tau+7eta/8. For a yes-instance, the explicit old feasible product has new error at most tau+5eta/64, by the same perturbation estimate applied to that product. Hence the rational threshold tau'=tau+eta/2 separates yes and no instances by at least 3eta/8. This verifies the corollary's statement about an actual feasible product, not just an unattained infimum.

## Limitations and recommendation

No material gap or unsupported extension was found in the proved statements. This proves NP-hardness, not NP-completeness or NP membership; no polynomial-size rational certificate is asserted for general real-factor instances. The result does not assert constant-relative-error hardness, nor does NP-hardness unconditionally exclude polynomial algorithms without the usual P-versus-NP qualification. Submitted finite verification scripts are supplementary; the review above does not depend on their output. The computational narrative about small certificate instances should be checked by the separate diagnostics workflow.

**Recommended canonical status: Resolved, by NP-hardness.** Attribute the submitted result to Matthew J. Colbrook and retain the distinction between mathematical review, publication status, and originality. No proof or canonical file was edited by this review.
