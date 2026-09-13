# Scope and status

## Canonical request

RA-05 has two related targets: determine the optimal worst-case joint dependence on rank and accuracy, and decide whether its displayed additive formula is a universal upper bound. This package distinguishes them.

## Completed within the manuscript

**Displayed formula:** a complete negative argument is supplied separately for every fixed real `p > 2`, not merely one counterexample exponent. Corollary 1.2 uses a polynomial separation that survives every fixed logarithmic factor.

**General new lower bound:** Theorem 1.1 proves
`Omega_p(k^(p/2)/(epsilon^beta_p + log(k)/k))`
for every sufficiently large rank and every accuracy in `(0, 1/2)`. There is one input per rank, independent of accuracy.

**Even powers in a precise regime:** combining this result with the cited Lin–Mirrokni–Woodruff upper bound gives the optimal order up to logarithms for every even `p >= 4` when `epsilon >= sqrt(log(k)/k)`.

**Explicit independently checkable fallback:** Section 8 proves the quartic mutually-unbiased-basis construction from the beginning, including a finite-field construction in Appendix C. That lower bound even permits signed weights.

## Not completed

The best joint size is not classified for non-even `p`. In the stated moderate-accuracy range, the lower bound has accuracy exponent `2 - 2/p`, whereas the cited upper bound has exponent `2`.

The best joint size is not classified for all smaller accuracies, including at even `p`. The principal lower bound saturates at approximately `k^(p/2+1)/log(k)`. The sparse-mean proof cannot infer more after the small-subset singular-value range is exhausted. The explicit quartic family supplies an additional bound but does not close the whole gap.

The paper does not give a uniform matching upper bound of the form of Theorem 1.1. Nor does it claim that `beta_p` is the optimal exponent for non-even powers.

## Evidence level

This is an internally audited mathematical manuscript with reproducible finite checks. It has not been independently peer reviewed, and no Lean or other proof-assistant certificate was produced. The imported restricted-invertibility theorem is identified explicitly and was checked against the primary source's theorem statement; it is not re-proved in the package.

For the broader optimal-joint-size entry, the appropriate scope description remains **PARTIAL, subject to review**, not an unqualified full classification. The narrower displayed existence bound has a negative resolution in this manuscript. No external repository status was changed.
