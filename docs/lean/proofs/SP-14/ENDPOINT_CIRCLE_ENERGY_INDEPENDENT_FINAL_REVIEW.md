# SP-14 conventional circle Sobolev energy: independent final review

**Author:** `/root/sp14_base_proof`. **Independent reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE this exact `1/2<r<1` circle-energy gate; the frozen SP-14 Target remains open.

The frozen source `EndpointCircleEnergy.lean` has SHA-256 `66c46c33ed95758f19ee747a11d6abd5b702eef4d162cad7f8a1a185740f8a83`. I checked it against the approved source-locked circle-realization precontract, original real-interval `FourierCoefficient`, actual negative Fourier operator, and audited two-block coefficient map. The energy term is exactly `(1+|p|)^(2r)‖FourierCoefficient f p‖²`. At nonnegative mode `k`, the term equals `‖y_k‖²`. At negative mode `p=−(t+1)`, its conventional weight is `(t+2)^(2r)`, whereas the source two-block physical model has `(t+1)^(2r)`. The proof retains this shift and establishes both oriented inequalities with factor `2^(2r)`, as well as summability over every integer mode. No equality between the asymmetric two-block and conventional circle norm is asserted. The argument includes the zero mode exactly once and uses the frozen original Fourier integral through the previously audited coefficient identities.

An independent imported audit at `/private/tmp/sp14-endpoint-circle-energy-independent-audit.lean`, SHA-256 `fe52fea93f63bc08bf9de6b3cdbc3b603fe7c910362ecd7aabecb48900426a15`, elaborated the exact energy definition, summability theorem, and two-sided bound, passed `#assert_trust kernel`, and reported only `propext`, `Classical.choice`, and `Quot.sound`.

Pointwise identification with the source `g₀V`, the background inverse, the all-`0<r<1` realization, the final infinite symbol, nonextension, and the frozen negative Target remain open.
