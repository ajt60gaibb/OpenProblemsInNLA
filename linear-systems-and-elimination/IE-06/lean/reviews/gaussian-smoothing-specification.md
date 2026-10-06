# Exact finite-dimensional Gaussian smoothing bound

Proposed by root before implementation. Let E,X be fixed n by n matrices,
Y,Q fixed n by q matrices, E=X+Y Q^T, Q^TQ=I. Let r>0, q<=r, s>=3r,
and let G have the actual iid standard Gaussian n by s law. Let zeta,L>=0
and suppose every row of X has Euclidean norm at most zeta.

For every x>0, simultaneously outside an event of probability at most
(n+1)*exp(-x), the following bound holds for every J whose row l1 norms
are at most L and which satisfies J E G=0:

  max_i rowNorm(J E,i) <=
    L*zeta*(1+sqrt(2*s+4*x)*sqrt((3/r)*exp(2+x/r))).

Equivalent formulation with any function J(G), even before a separate
measurability proof, is an outer-measure bound on the actual bad event with
its stated algebraic and row-l1 premises. This is adequate for later
measurable GEPP specialization. It makes no Gaussian independence claim
about J, XG, or Q^TG.

Proof: each row X_i G is an s-dimensional centered Gaussian vector with
scalar variance ||X_i||^2. The proved Gaussian Frobenius bound, or the
weighted scalar quadratic bound, gives rowNorm(XG,i)<=sqrt(2s+4x)*zeta
outside probability exp(-x). Union over the n rows. The fixed compression
Q^TG has the proved q by s Gaussian law; its row Gram is positive definite
almost everywhere, including the empty-row case q=0. The established A2'
threshold is exactly (3/r)*exp(2+x/r). Apply the independently reviewed
deterministic cancellation bound. Use only a union bound, not independence
of the two good events. No dimension-dependent loss besides n+1 occurs.

Independent preimplementation review pending.

Preimplementation independent review by /root/infrastructure: approved.
The transposed s by n Gaussian times a fixed n by 1 vector gives the exact
row tail, including zeta=0. Compression, the vacuous q=0 rank case, and A2'
give the displayed reciprocal threshold. The good events imply the bound
simultaneously for every J by deterministic algebra; no J independence or
measurability is required for outer-measure domination. The union count and
all constants are correct.
