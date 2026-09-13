# Notes

The dual formulation removes the independent polar factors from optimization. A positive R may be diagonalized without loss by simultaneous unitary conjugation of all X_j; this justifies the diagonal R used in the search. Searching real matrices gives lower bounds only because the canonical field is complex.

The all-m dilation must extend the effects on ker S before defining W. Simply restricting R to the support of S can change ||RX_j||_1, so the proof does not make that restriction. Instead the isometry acts on the entire original space and embeds both R and S.

Approaches not justified: interpolation of the nonlinear denominator from p=1 and p=2; a universal rank-one ansatz; a universal dimension cap; replacing the full m-outcome positive decomposition by projections in the same dimension. The binary convexity argument does not automatically extend to a general m-outcome decomposition; the dilation is what resolves that issue at the level of the unrestricted-dimension supremum.

The source already contains subquadratic counterexamples to the earlier closed formula. Reproducing them would not determine the replacement C_p(m), so they are not counted as a negative resolution of MI-20.

Promising next step: exploit the projective normal form as a block-matrix norm problem, while tracking rank and dimension rather than assuming scalar blocks suffice.
