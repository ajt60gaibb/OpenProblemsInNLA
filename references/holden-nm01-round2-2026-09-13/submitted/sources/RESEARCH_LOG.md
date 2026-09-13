# Research and verification scope

This round began by reading the prior mathematical report and the exact canonical website entry. The original proof pack was extracted and retained unchanged. The investigation concentrated on two possible ways around its facet dependence.

## Projective-value route

The determinant response of the hidden simplex to projective renormalization factors into linear polynomials. This gave a polynomial-query recovery procedure. The proof then needed a uniform polynomial-bit safe scale and an exact decision-to-value conversion, rather than floating-point reconstruction. The strong-SSC dual-ray gap supplies the scale, and rational height bounds plus threshold bisection supply exact values.

An explicit weak-SSC cone with a positive balance of contact gradients showed that diagonal stability cannot be assumed under the original promise. The stronger conclusion—that a punctured projective interval is outside the whole promise—was checked by all twenty candidate facet triples and exact Bernstein coefficient inequalities. Checking only the inherited factorization would not have established that conclusion.

## SOS-containment route

The contact-count argument first gave weak-SSC obstructions. Moving extra contacts inward gave strong SSC, but continuity alone was not sufficient for a polynomial-input-size statement. Rational principal-minor height and sign-stability bounds supply that additional step. Expanded-circle evaluation functionals separate the target polynomial from the complete degree-truncated preordering. The full preordering, not merely its singleton quadratic module, was tested.

The exact degree-eight experiment at eta=2^-32, epsilon=2^-40 failed a positive-definiteness check at subset (0,2). It is not a valid certificate and is not included among the three delivered witnesses. An interrupted time-limited run is also excluded from the verification counts. The delivered degree-eight choice eta=2^-64, epsilon=2^-80 completed all 65,536 exact matrix checks successfully.

The quotient-basis checker validates all three final witnesses. A second checker uses the full monomial basis with no quotient reduction for degrees four and six. These are distinct implementations in the same AI-generated project, not independent researchers or an independent mathematical audit.

## Verification counts and limits

The complete new regression suite has 23 test methods, including malformed/altered-certificate and bad-oracle cases. All passed with --full, including the degree-eight check; there were zero skips. The old suite's 16 test methods were separately rerun and passed. The three quotient certificates cover 69,888 localizing matrices in total. Extra full-basis checks are not added to that total as though they were new instances.

The exact computations verify finite algebraic premises and examples. The report's proofs establish the quantified statements to the extent those arguments are correct. Neither level constitutes a formal proof-assistant verification, external peer review, or a completed solution of NM-01. The tests do not implement a polynomial-time exact decision oracle in variable rank.

## Delivery audit

The archive includes checksums, actual execution logs, environment details, and a clean-extraction reproduction report. Elapsed times are observations from this environment, not guarantees. No wall-clock research-duration claim is made. No web search failure is used as proof of nonexistence of a solution. The remaining algorithmic gap is described explicitly in STATUS.md and the report.
