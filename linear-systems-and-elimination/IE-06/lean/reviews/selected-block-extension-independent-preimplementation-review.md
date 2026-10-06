# Independent B4 preimplementation review

Reviewer: /root/independent_math_review. Approved the complete current exact
contract in selected-block-extension-specification.md before implementation;
reviewed SHA-256 `782a3d6bd339869db741cf849c9180cb4c2defe1b101a92548c557297c98359a`. This reviews the proposed mathematics, not an assertion
that its probabilistic/measurability bridges are already proved.

The fixed-row Gaussian fiber and candidate masking route conditions only on
outside-row coordinates. A frame of ker(M) can be chosen after each fixed M
because the final event is intrinsic and measurable. The two stacking failure
events require a union bound, not independence. A6's source indices match:
with j=floor(d/2), 2j<=d and the smaller source index m+s-d has the larger
singular value. Its bad event therefore implies the A6-index bad event.
The half-factor in R makes the non-strict failure event valid without an
unsupported boundary-null assertion. Full row rank is an explicit fiber
hypothesis disposed of later using actual Gaussian nonsingularity, not inferred
from a finite pseudoinverse norm.

All displayed coarse numerical choices are sound. Here is the exact check
of the potentially sensitive estimate for u: writing a=sqrt(C_A)/mu*exp(x0/k),
u/a=48*sqrt(k)+sqrt(2x/(j+1)). With x<=(beta+5)k*lambda and j+1>=d/2,
the second term divided by sqrt(k) is at most 2*sqrt((beta+5)lambda/d),
hence at most exp((beta+5)z). Since lambda/k<=z, the proposed constant 50
and exponent (2beta+6)z safely dominate. For the overcrowding term,
j^2/4>=d^2/36 and D_beta=64(beta+6) absorb
(j+1+s+beta+1)lambda<=(beta+6)k*lambda. All x values are positive and
0<theta<=1 follows from z>=0. The lower bound on ell follows from
sqrt(s)=2sqrt(k), j>=d/3.

Since mu<sqrt(k), 1+u is at most
(1+50sqrt(C_A))*sqrt(k)/mu*exp((2beta+6)z). Multiplying by ell^-1 and
adding a gives exactly the stated denominator bound with H. H>1 ensures
log(2H)+1>0, so the final C_beta safely absorbs both the factor 2H and
the extra exponential. Dimension assumptions imply k>=1600 and n>5k;
all reciprocal and logarithm comparisons are properly guarded. The cost
2exp(-x0) is paid once, whereas the two per-candidate terms are multiplied
by the number of sets; at most n^s such sets gives total
4exp(-(beta+1)lambda)<=exp(-beta*lambda) for n>=4. No factorial loss,
extra public event, global success conditioning, or changed final IE-06 rate
is introduced. The code must still prove every rank, measurability, finite
counting, row-permutation and conditional integration bridge listed in the
contract, as the author explicitly states.
