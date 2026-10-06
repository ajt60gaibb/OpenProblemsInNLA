# Actual stage smoothing: exact B1+B2 assembly

Proposed by root before implementation. Let 1<=r<t and t+4r<=n,
tau>=0 and x>0. Let T_t be the actual canonical selected block. Define

  zeta = sqrt(1+(2+4x)*tau),
  K = 2^(4r)*zeta*(1+sqrt(8r+4x)*sqrt(3*exp(2+x/r)/r)).

Prove for the literal square Gaussian law that

  P[A.det != 0 and sigmaInvSum(T_t,r)<=tau and
    exists active/padded row i with rowNorm(E_(t+4r),i)>K]
  <= (2*n+1)*exp(-x).

The event may quantify all padded rows; inactive rows are zero. Every basis
choice is made inside a fixed selected-block T fiber. The public event
contains only actual selected blocks and elimination rows, hence no chosen
basis and no new measurability hypothesis.

Within each fixed order pi and Good(T) fiber, choose the proved genuine
inverse truncation T^-1=Z+HV^T, with V^TV=I and ||Z||_F^2=Sigma_r(T).
The product restricted-row bound costs at most (n-t)*exp(-x)<=n*exp(-x)
for a row of the retained elimination component to exceed zeta. On its
complement, the proved fixed Gaussian smoothing bound costs at most
(n+1)*exp(-x). It applies to the actual subsequent J, with row l1 bound
2^(4r) and J E_t Gstar=0, on the nonsingular-input event. Unioning those
costs gives 2n+1. No future pivot success is conditioned on.

The exact F7-plus-future tested law integrates these pointwise T-fiber
bounds; its order weights sum to one. Singular inputs are an explicitly
excluded event here and have proved Gaussian measure zero when transferred
to the final row-cap statement.

Coordinate helper: for t+s<=n, split FutureBlock(n,t), indexed by original
columns j>=t, into the next s columns as a literal n by s Gaussian matrix
and FutureBlock(n,t+s). The exact product law and an explicit measurable
assembly inverse follow by partitioning the original column indices at
t+s. This avoids cast-dependent dimension rewrites and includes s=0.

For final all-stage use, no t<=r truncation branch is needed: stages u<=5r
use deterministic row norm<=row l1<=2^u<=2^(5r). For u>5r take t=u-4r>r.
The latter staging simplification was independently approved by
/root/independent_math_review before implementation; it changes only the
universal constant in the final exponential.

Independent review of this exact stage event/count and coordinate helper
is requested before their implementation.
