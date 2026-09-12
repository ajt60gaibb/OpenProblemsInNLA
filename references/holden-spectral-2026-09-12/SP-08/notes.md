# Notes — SP-08

The useful new reduction is the identity M=uv^T+vu^T for a difference of two
rank-one eigenprojectors. After a generic perturbation and ordering |u_i/v_i|,
the signs of M become d_i d_j epsilon_min(i,j). This compresses exhaustive
endpoint enumeration from 2^(n(n+1)/2) matrices to 2^(2n-1) patterns up to
permutation similarity. It does **not** prove rank two for an extremizer.

The degeneracy argument is important: generic perturbations need not remain
normalized eigenprojectors. They are only auxiliary linear objectives. Taking
a constant subsequence of endpoint maximizers then transfers maximality back
to the original objective. Omitting this step would leave zero-entry cases open.

The finite upper-bound proof uses characteristic polynomials. There can be many
patterns with the same polynomial, so one root certificate per distinct
polynomial suffices after coverage is proved. SHA256 hashes are integrity aids,
not mathematical substitutes for equality of the regenerated coefficient sets.

The a=1/2 case is represented by integer endpoints {1,2}; its squared-spread
bound 292 must be divided by four. The other integer bounds are 133 and 161.
No assertion for n=8 and all a, or for a=0 and all n, follows from these data.

Primary comparison: Calkin et al., arXiv:2510.15919v1, Sections 7-8, proves the
previous recorded finite ranges. The current audit inspected the HTML text;
no external Maple execution was used as support for this pack. A bounded search
did not establish publication novelty for the present reduction or finite cases.
