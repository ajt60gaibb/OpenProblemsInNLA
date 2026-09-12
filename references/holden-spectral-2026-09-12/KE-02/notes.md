# Notes and remaining work — KE-02

The initial bundle's useful input was sorting diagonal entries and allocating
bounded displacements. This audit simplified the construction to an arithmetic
ramp and added Theorem B: phase-equivalent tridiagonal Toeplitz inputs at **all**
coupling strengths. Theorem B was not present in the old ZIP.

## What makes the new subcase distinct

The weak-coupling theorem alone requires eta=O(delta/n). In Theorem B, r is
unrestricted. Large r is handled by the existing spectral spacing; small r is
handled by a diagonal ramp. The algorithm need not calculate the sine spectrum:
it uses only a comparison of squared magnitudes and a linear number of arithmetic
operations. Its universal exponent is 3, not a parameter depending on dimension.

For example, tau=0, r=1/4, any choice of complex phases and any n>=2 gives a
normalized matrix (row-sum norm <=1/2). For sufficiently small delta, it is well
outside Theorem A while covered by Theorem B. This prevents describing the
strengthening as merely a restatement of the weak-coupling hypothesis.

## Tempting extensions that are not proved

Sorting the diagonal does not sort the full tridiagonal spectrum. If eta is of
order one, gamma-2eta may be negative. No conclusion can be taken from that
bound. A long chain with unequal couplings need not have the Toeplitz sine
spectrum. Replacing the b_j by their mean would change off-diagonals and violate
the allowed output, and is not used here.

A decomposition into short blocks leaves the problem of separating eigenvalues
across blocks while preserving the nearly-linear cost. Merely computing all
eigenvalues at a higher cost would not meet KE-02. These are forward-looking
obstructions, not a claim that extensive failed experiments were run in this audit.

## Next steps for research and verification

Audit both the all-n gap estimate and exact-real arithmetic count. Check prior
literature for an existing Toeplitz treatment before asserting novelty. A useful
next mathematical extension would allow substantially varying diagonal entries
and coupling magnitudes, with constants still independent of n and delta.
