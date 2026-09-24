# Proposed weighted rectangular area corollary

For finite-dimensional real inner-product spaces E,F with Borel measures, put
mu = ordinary Euclidean volume on E and nu = muHE[finrank R E] on F.
Given measurable s subset E, measurable f:E→F, derivatives f':E→(E→L[R]F),
within differentiability of f with f'(x) on s at every x in s, injective f'(x)
there, and InjOn f s, prove

    map f ((mu.restrict s).withDensity (fun x => ofReal (f' x).normDet))
      = nu.restrict (f '' s).

No measurability of the derivative selection is needed for this measure identity:
for a measurable test set T, its preimage is measurable; the proved immersion
area formula applies to s intersect preimage T, whose image is (f''s) intersect T.

If additionally the normDet density is AEMeasurable with respect to mu.restrict s,
then for each measurable weight w:F→ENNReal prove

    integral_(f''s) w dnu = integral_s ofReal(normDet(f' x))*w(f x) dmu.

Use the measure identity, the lintegral map theorem, and the withDensity integral
formula. Global measurability of f is a legitimate intermediate convenience:
actual chart maps, which need only be continuous on their open source, can be
extended by zero outside that measurable source. This corollary must not add
measurability hypotheses to any frozen TR-06 final declaration. The density's
measurability for C1 charts follows from continuity of their derivatives and of
normDet. The pointwise graph-Jacobian inequality and finite graph volume remain
separate, unproved obligations.
