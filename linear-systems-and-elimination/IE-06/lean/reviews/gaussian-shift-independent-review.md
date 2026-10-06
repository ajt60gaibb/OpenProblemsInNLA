# Independent Anderson shift review

Reviewer `/root`, independently of author `/root/source_statement_author`.
Reviewed `NLA/IE06/GaussianShift.lean`, SHA-256
`2585fecb36ecd290eb9bd2b5a67690ff57f31580f798713133c3ba2f12c14936`.

The adopted Prékopa–Leindler theorem uses x+y, and the wrapper correctly rescales
by one half and cancels the finite positive factor 2^n to obtain its midpoint
form. ENNReal inverse/rpow conventions are explicit, including the conversion
of the positive real inverse in the upstream constant.

The Gaussian midpoint density inequality is proved from the coordinate sum of
squares; this is the Euclidean Gaussian density, not the function-space sup
norm. The shifted indicator functions have the correct signs. Convexity places
the midpoint in K, central symmetry equates their integrals by reflection,
and midpoint Prékopa–Leindler bounds the shift by the centered mass. Dimension
zero is treated directly via its unique vector.

The final theorem is for the actual product standard Gaussian law. The positive
finite normalizer and exact density equality are derived from the already
proved product density. The result permits every Borel measurable convex
centrally symmetric set, including empty or null sets, and every shift vector.
No Anderson or Gaussian shift inequality is a premise. Mathematical and exact
statement review approved. This discharges the shift input; normalized
restriction MGFs are a separate subsequent proof.
