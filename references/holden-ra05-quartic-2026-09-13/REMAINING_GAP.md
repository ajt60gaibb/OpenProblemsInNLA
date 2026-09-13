# What remains after this round

## The old quartic rank gap is closed by the new theorem

For p = 4 and arbitrary input rank, the manuscript reports the complete order

    min(k^2/epsilon^2, k^(5/2)/epsilon + k/epsilon^2)

up to logarithmic factors. In particular, epsilon = k^(-2) now has matching
order k^5. The earlier interval from k^5 to k^6 at that point is not retained
as an unresolved quartic claim.

The theorem is an existence/size result. It does not determine optimal leading
constants, remove every logarithm, or provide a fast implementation of the
partial-coloring oracle. Those are not requirements of RA-05's stated
up-to-logarithms size target.

## The all-exponent target is not completed

No matching unrestricted joint classification is proved here for any fixed
p > 2 other than 4. In particular:

1. For non-even powers, the earlier finite-difference lower bounds lose an
   accuracy power at the full rank factor. The present exact quartic expansion
   does not remove that loss.
2. For even powers at least 6, more head/tail interaction terms appear. This
   manuscript does not give a simultaneous partial-coloring variance analysis
   for all of them with matching rank dependence. Replacing 4 by p in the
   stated formulas is not justified.
3. The prior classification under rank(A) <= k+1 is still not an unrestricted
   classification for those other exponents. An input projection would alter
   the coreset model unless an additional original-row error proof were supplied.

The missing assertions are new inequalities for those exponents, not a need to
change a label. A full RA-05 solution must establish their matching upper and
lower joint orders (or a different appropriate complete characterization).

## Do not infer an unsupported universal formula

The expression proved at p = 4 is not proposed here as an all-p theorem.
Neither interpolation between even powers nor finite moment preservation for a
polynomial power automatically gives a uniform relative approximation for a
non-even power. Constants and rank factors must be checked, not hidden under a
p-dependent notation when they actually depend on k or epsilon.

The archived negative answer to the subsidiary displayed bound remains distinct
from the broader optimal-joint-size question.
