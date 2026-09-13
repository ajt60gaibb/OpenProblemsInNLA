# Notes

The earlier handoff contained the rank-one perturbation parametrization but no derivation or optimizer. `result.md` supplies both, including the previously dangerous alpha<beta regime.

The useful general ingredient is the minimal-support maximizer lemma for symmetric multiaffine polynomials. Positivity of the polynomial's coefficients is not needed. Confusing this lemma with a statement that every maximizer has uniform support would be an error: degenerate coefficient choices can have nonuniform maximizers as well.

A finite exploratory rational grid suggested that, when alpha<beta, the best support might always be either 2 or n. That stronger simplification is NOT proved or used. The exact n-candidate formula is already valid without it. The exploratory grid checked n=3,4,5,6,10,20,40 and (beta-alpha)/beta in {1/200,...,1}; it is not evidence for all parameters.

Promising extension: two exceptional eigenvalues introduce an orthonormal two-frame and coupled simplex constraints. Any attempted smoothing must preserve their orthogonality; the one-vector argument cannot be copied without that check.
