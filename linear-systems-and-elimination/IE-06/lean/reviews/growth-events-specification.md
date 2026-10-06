# Growth event bridge: independently reviewed contract

Author `/root`; preimplementation mathematical review and approval by
`/root/source_statement_author`.

Define rawSchurMax as the exact numerator of the frozen growth definition.
Define the selected exceedance event with the same dimension, nonsingularity,
and admissibility guards as the original event, using firstPath. Define the
canonical raw event by rawSchurMax(A,firstPath A)>t.

For every real t, the original and selected exceedance events have equal
Gaussian measure. On the almost-sure event of agreement of all admissible
paths with firstPath, their membership is equivalent. No choice among tied
paths is silently removed from the original target.

Also, for every real t, the original exceedance probability is at most the
canonical raw-event probability plus P{entryMax<1}. On the complement of the
latter event, the numerator is nonnegative and entryMax≥1, so growth≤rawSchurMax.
Almost-sure set containment and measure subadditivity prove the claim even
before canonical-selector Borel measurability is supplied by PivotFiltration.
No positivity hypothesis on t is needed. The normalization exception already
has an exact, independently reviewed Gaussian probability bound.
