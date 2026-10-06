# Independent radial Gaussian review

Reviewer `/root`, independently of author `/root/infrastructure`. Reviewed
`NLA/IE06/GaussianSmallest.lean`, SHA-256
`2e8146e370ea2c0df99f711386957f36b13364837f53a312120b86bc0453cfb1`.
The exact density and moment statements were approved before implementation.

The density is with respect to genuine Euclidean volume, and the coordinate
map is proved volume preserving. Its factor is (sqrt(2 pi)^d)^(-1), consistent
with d independent standard normal coordinates. The finite product proof also
handles dimension zero.

The radial integral uses the Euclidean norm, positive dimension, and exponent
a>-d. Both integrability and its Gamma evaluation are proved. The recurrence
I(a+2)=(d+a) I(a) uses a positive Gamma argument, so no singular Gamma identity
is invoked. Positive moments are then the product of d+2j, with zero dimension
and zero order handled explicitly. Inverse moments use a=-2q, with 2q<d,
so all factors d-2(j+1) are positive. The totalized reciprocal at the origin
is consistent with the radial integration and its integrability proof.

The coordinate wrappers transfer the exact statements to the literal product
Gaussian law used by IE-06. No chi-square law, inverse moment formula, or random
matrix estimate is taken as an axiom. Adapted local source provenance is
recorded separately; no RRF module is imported.

Mathematical and exact statement review approved. This file supplies radial
building blocks only. The Gaussian regression identity, true pseudoinverse
norm comparison, and rectangular inverse tail remain to be proved separately.
