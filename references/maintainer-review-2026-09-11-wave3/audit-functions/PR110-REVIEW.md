# Independent rigorous review of PR #110

Head reviewed: `7d00fde9b72f55268dca3c61cd57e93085aeec87`.
Published comparison base: `aaa88c40fbf58e8cebc335021b3c5cd108c357e4`.
Date: 2026-09-11. Snapshot: `../pr-110`.

**Verdict: PASS. No mathematical, scope, code-evidence or final-document blocker
found.** MF-05, MF-07 and MF-12 each receive a complete affirmative resolution of
their original targets. This review independently read both complete proofs and
checked the supporting code and computations; it did not treat embedded PASS
reports as evidence. This is AI-agent mathematical review and reproducible
checking, not proof-assistant certification, external human peer review, or a
determination of novelty or priority.

## Preserved identities and source questions

The entire `problem_ids.json` is byte-identical to the published base. For all
three canonical READMEs, everything from `## Context and notation` through the
end is byte-identical to the base. Thus definitions, quantifiers, original
problem statements, paths and historical references remain unchanged. The
changes add preceding resolution records and update status metadata. See
`identity-checks.json`.

The primary [Epperlein–Wirth paper, Conjecture 3](https://arxiv.org/html/2311.18633v2)
separately states local exponent-1/d Hölder continuity (L1) and the dimension-only
polynomial trajectory bound (L3). These match MF-05 and MF-07. The proof actually
gives a uniform Hölder bound on each common norm ball, which implies the original
local two-family assertion; it does not claim the different pointwise Lipschitz
lower bound in MF-06.

The primary [Varney–Morris paper, §7 Question 2](https://arxiv.org/html/2209.00449)
asks whether every nonnegative exponent is attainable by a finite real family
with growth comparable to n^alpha. MF-12's every-length, finite-family target is
met by a fixed pair after the exponent is chosen. The submitted proof establishes
its own identities, bounds, and tensor argument, so it does not require accepting
an unproved generalization of the older construction.

Both final manuscript bodies from `begin{abstract}` to the end are identical to
the preserved original TeX sources. Their added frontmatter states that the old
pending-review/access remarks in those bodies are historical. This is an explicit
provenance disclosure, not an outstanding mathematical HOLD. Source hashes are
recorded in `reviewed-input-sha256.json`.

## MF-07 and MF-05: detailed mathematical audit

Read all 299 lines of `manuscripts/uniform_growth_and_holder.tex`, including
general-radius/zero-radius cases, the complex-field normalization, comparison
at arbitrary thresholds, the approximate norm construction and sharpness.

**Approximate extremal norm (Lemma 3).** For a>rho(M), the submultiplicative
product sequence makes sup_k a^-k a_k finite, so the displayed supremum defines
a finite norm v equivalent to Euclidean norm and v(Ax)<=a v(x). No extremal norm
at exactly rho(M), irreducibility, or finiteness of the family is assumed.

The determinant-maximizing column basis exists in the compact v-unit ball and
is invertible. Replacing one column proves every coordinate of T^-1 x has modulus
at most 1 on that ball, over both R and C. Thus ||z||_infinity<=v(Tz)<=||z||_1.
An SVD T=QDR* and the scaling w(z)=sqrt(d) v(QDz) give
||z||_2<=w(z)<=d||z||_2. B_A=D^-1 Q* A Q D has w-operator norm <=a and entries
bounded by L sigma_j/sigma_i. These steps do not lose dependence on the family
in an unrecorded constant.

**Triangular damping (Lemma 4).** If X is block lower triangular and the positive
block scalars h_1>=...>=h_b decrease, each cut map
Phi_l(Y)=((1+t_l)/2)Y+((1-t_l)/2)S_l Y S_l, with t_l=h_(l+1)/h_l, is a convex
combination of unitary conjugations and contracts the spectral norm. Its effect
on the lower (i,j) block is multiplication by the product t_j...t_(i-1)=h_i/h_j.
All upper blocks of X vanish. Therefore the composite is exactly HXH^-1.
This contraction applies to a whole lower-triangular product, which is the
essential point; bounds on individual transformed factors would not suffice.

**Uniform comparison (Proposition 5).** Split singular values at ratios >s,
s>=1. Every entry of the strictly upper block part E_A is <=L/s. Hence
||E_A||_w<=d^2 L/s and C_A=B_A-E_A has w-norm <=u=a+d^2 L/s. Every C-segment,
including an empty segment, has spectral norm <=d u^t.

Cap consecutive singular-value ratios at s to form D'. Its condition number is
<=s^(d-1). H=D'^-1 D is constant within each block and nonincreasing between
blocks, so damping controls whole C'-segments by the same d u^t. The transformed
upper part E'_A still has entries <=L/s: each nonzero entry crosses a capped
ratio equal to s, and all other consecutive ratios are >=1. Thus ||E'_A||<=dL/s.

Expanding a word with k E'-factors leaves k+1 C'-segments and gives the bound
d^(k+1)u^(n-k)(dL/s)^k. The binomial sum is d(a+2d^2L/s)^n. Undoing the similarity
and taking a down to rho(M) yields, for every s>=1 and n>=0,

    a_n(M) <= d s^(d-1) (rho(M)+2d^2 L/s)^n.

Although the intermediate coordinates depend on a, the final right side does
not, so this limit is legitimate without compactness of those coordinates. The
proof never assumes that principal submatrix families have smaller JSR; that
shortcut is unavailable in general, consistently with the separate primary
[Epperlein–Wirth projection paper](https://arxiv.org/html/2504.17505v1).

For d>=2 and r>0, take s=2d^2Ln/((d-1)r), which is >=1 because r<=L. Applying
(1+(d-1)/n)^n<=exp(d-1) gives precisely

    a_n(M) <= d(2ed^2/(d-1))^(d-1) (Ln)^(d-1) r^(n-d+1).

This proves the MF-07 constant uniformly over dimension-d families and their
cardinalities. When r=0, letting s grow gives a_n=0 for n>=d; shorter nilpotent
products need not vanish. The scalar case is separate and exact. Jordan powers
show the exponent d-1 is sharp; no optimal constant is claimed.

**Hölder estimate (Corollary 7 and Theorem 2).** Choose s=2d^2L/epsilon and
h=r+epsilon. The all-length comparison makes
p_epsilon(x)=sup h^-k ||A_k...A_1 x|| finite, with eccentricity <=d s^(d-1) and
generator norm <=r+epsilon, including r=0. A perturbation E has p_epsilon-norm
<=d s^(d-1)||E||_2.

For 0<delta=d_H(M,N)<=L, choose s=(L/delta)^(1/d). Nearest elements exist by
compactness. The preceding norm gives

    rho(N)-rho(M) <= 2d^2L/s+d s^(d-1)delta
                 = d(2d+1)L^(1-1/d)delta^(1/d).

Interchanging the families gives the absolute difference. Delta=0, delta>=L,
L=0 and d=1 are explicitly covered. Restricting both families to a Hausdorff
neighborhood of any fixed compact family supplies one common finite L and the
canonical local statement. Nilpotent cyclic shifts with characteristic polynomial
z^d-delta establish the sharp exponent. No continuity theorem is used circularly.

## MF-12: detailed mathematical audit

Read all 295 lines of `manuscripts/arbitrary_growth_exponents.tex`. All hypotheses
and constants suffice, including n=1, repeated P factors, integer exponent zero,
arbitrary real fractional exponents, and fixed dimension after parameter choice.

For 0<alpha<1 choose 0<lambda<=1/4 and mu=lambda^(1-alpha), so lambda<mu<1.
The stated U,V give UV=I_2, P=VU and P^2=P. With
A=diag(1,J_lambda,J_mu,1), the Jordan power identity gives exactly

    T_q=U A^q V=[[1-q lambda^q, q mu^q],[0,1]],  q>=0.

Writing ell_q=q lambda^q and b_q=q mu^q gives 0<=ell_q<=1/4 and
b_q=q^alpha ell_q^(1-alpha) for q>0; the q=0 term vanishes. There is no hidden
growth from consecutive projections because T_0=I_2 and P is idempotent.

For every arbitrary list of nonnegative gaps, the upper-right entry of the
compressed product is z=sum_i b_qi w_i with
w_i=product_(j>i)(1-ell_qj). Telescoping gives
sum_i ell_qi w_i=1-product_i(1-ell_qi)<=1. Hölder with exponents 1/alpha and
1/(1-alpha) then gives z<=(sum_i q_i)^alpha, including zero/empty lists. This is
an all-words estimate, not a calculation only on a proposed extremal pattern.

Every word with projections factors as A^r V (compressed product) U A^t. The
end factors satisfy ||A^r||<=H=(1-mu)^-1, ||U||=sqrt(3), ||V||=sqrt(2).
The middle spectral norm is <=1+n^alpha. Pure A words are bounded as well, so
all length-n words obey the explicit C n^alpha with C=2sqrt(6)/(1-mu)^2.

For n>=1/lambda, choose q=floor(log_(1/lambda)n), k=floor(n/(q+1)), and
r=n-k(q+1). The word A^r(PA^q)^k has exactly length n. Its action on V e_2
has first coordinate (b_q/ell_q)(1-(1-ell_q)^k), and ||Ve_2||=sqrt(2).
The floor inequalities imply n>=4^q>=2(q+1), k>=n/(2(q+1)), lambda^q>=1/n,
and hence k ell_q>=1/4. Also (mu/lambda)^q=(lambda^-q)^alpha>=(lambda n)^alpha.
Using (1-ell_q)^k<=exp(-k ell_q) yields exactly the stated lower constant
c=(1-exp(-1/4))lambda^alpha/sqrt(2). For n<1/lambda, ||A^n||>=1>c n^alpha.
Thus the lower bound holds at every length, with no subsequence restriction or
length-dependent generator. The upper bound plus A's eigenvalue 1 gives JSR=1.

For gamma=m+alpha, tensor both generators with the same order-(m+1) Jordan block
J. Every length-n product is its base word tensored with J^n; equality of spectral
norms under tensor products proves the exact factorization of maximum growth.
The Jordan bound m^-m n^m<=||J^n||<=(m+1)n^m is valid also for n<m by the identity
term. The pair {J,0} handles every integer m>=0 with distinct generators. This
proves the stated dimensions and all real exponents.

For alpha=a/b rational, lambda=2^-b and mu=2^-(b-a) satisfy all conditions and
give dyadic entries; tensoring preserves them. Lambda=1/4, mu=1/3 gives the
claimed irrational exponent because rationality of log(3)/log(4) would contradict
unique factorization. Density follows already from the rational exponents.
The theorem asserts comparability only, not a limit of a_n/n^alpha, nonnegative
generators, optimal dimension, or uniform constants across different exponents.

## Code inspection and fresh executions

Read both complete construction scripts/tests and all three mathematical
verification programs before running them. The exact rational interface preserves
Fraction values and refuses floats, invalid parameters, and resource-limit
violations; these limits do not limit the real-exponent mathematical theorem.
Its two example outputs were regenerated and are identical to the supplied JSON.
The finite diagnostic programs use explicit tolerances and label floating-point
results accordingly. Their enumeration visits all binary words, correctly
reconstructs the reported winner, and does not infer JSR from finitely many words.

Fresh executions all passed:

| Check | Actual rerun coverage |
|---|---|
| Exact rational construction tests | All six tests PASS |
| Symbolic growth identities | Jordan induction, compression, projection and Gram identities PASS |
| Growth diagnostics | 46 parameter sets; 46,000 gap lists and 46,000 full words |
| Lower-word diagnostics | 9,936 lengths, including extremely large n, plus 40 tensor checks |
| Triangular diagnostics | 10,000 real/complex damping cases; 5,000 finite-horizon cases |
| Binary enumeration at alpha=1/2 | Every word through length 24: 33,554,430 nonempty words, all bounds PASS |
| Fresh independent exact damping | All 63 block partitions through dimension 6, with complex rational entries |
| Fresh independent sharpness checks | Cyclic characteristic polynomials through dimension 10; 150 Jordan-power identities |
| Fresh independent gap-budget checks | 3,444 exact rational lists across 21 rational exponents |
| Fresh independent lower-word thresholds | 567 exact breakpoint/neighbor cases, including hundreds-digit lengths |

`independent_checks.py` imports no submitted code. It raises rational-exponent
budget inequalities to integer powers, so the reported 3,444 inequalities use
exact rational arithmetic rather than rounded roots. The exact lower-threshold
checks use integer bit lengths and rational comparisons. These finite checks
corroborate the analytic proofs; no collection of such cases substitutes for
their universal quantifiers. All logs and structured results are retained under
`runs/`, with independent results in `independent-checks.json`.

## Final PDF QA and recommendation

Rendered and visually inspected all 18 pages in the three canonical PDFs and two
final manuscripts. No clipping, missing glyphs, unresolved references, stale
mathematical statements, or unreadable formulas were found. Rebuilt all five
unchanged TeX sources twice with XeLaTeX and shell escape disabled. All page counts
and extracted text match exactly and no build warnings occurred. Both manuscript
rasters and the MF-07 canonical raster are identical. MF-05/MF-12 canonical first
pages have tiny vertical-spacing differences, inspected side by side; their
content and legibility are identical. QA records are `pdf-qa/report.json` and
`pdf-source-rebuild-results.json`; contact sheets and comparisons remain local.

The frozen PR110 head is reasonable to accept as three solved entries under their
unchanged original IDs, canonical paths and targets. No mathematical corrections
are required. MF-06 and other distinct targets receive no resolution from this
submission, and historical ratings/reference sections remain retained context.
