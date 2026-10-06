# Independent preimplementation review of A3 moment route

Reviewer: `/root/independent_math_review`. Proposal SHA-256: `adc9366b273c91468d860b082dc1844a8a9293a310cdf19975f8a0490f6ce5e1`.

Approved mathematically as a proof route for the exact proposed A3 target. No implemented A3 theorem is asserted by this review.

The source indices are consistent: retaining m=n−2q rows leaves r=m−(n−j)+1=j+1−2q small squared singular values. Row deletion decreases the forward singular values at the indicated index, and inversion of the positive Gram spectrum gives r inverse eigenvalues at least t⁻². The elementary symmetric sum/principal-minor identity and the union/Markov factor N^(q+1) are correct.

The conditional residual dimension is n−(m−r)=j+1. Bartlett's independent residual lengths have dimensions j+1−a, and the qth reciprocal-square moments have factors j+1−a−2b. The smallest dimension is 2q+1, so every moment exists. Bounding its denominator by (2q−1)!! ≥ q! is correct. The claimed factorial estimate q! ≥ (q/e)^q and binomial estimate N ≤ (em/r)^r give the displayed constants with c=1/(4e).

Writing j=4a+b, b in {0,1,2,3}, verifies qr≥j²/8 for all j≥4; consequently 2rq≥j²/4. With 0<theta≤1, the direction of the exponent comparison is correct. The remaining outside factor N≤n^r≤n^(j+1) preserves the exact target.

Implementation must prove the residual conditional Gaussian law, block inverse formula, determinant product and joint negative moment/integrability, spectral interlacing, and symmetric-sum identity. None can become a premise of the final A3 theorem. Singular exceptional sets contribute zero measure, and all inversions in the spectral implication require the stated positive threshold and almost-sure positive-definite Gram matrix. The proposed route is Gaussian-specific, which matches the IE-06 input law; it does not claim the stronger general-iid source theorem.
