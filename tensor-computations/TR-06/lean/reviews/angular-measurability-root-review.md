# Independent angular measurability review

Reviewer: `/root`, Codex AI agent. Date: 24 September 2026.
Approve AngularMeasurability.lean at SHA-256
`a93ab24637efeb22108f9fdd05732d1e0371e1184ade76590f9f21e4718a41d9`
for contribution integration. Root approved the exact hypothesis-free restricted
measurability target and route before implementation, then read the final code
and independently elaborated a copy.

C1 regularity on the open chart source gives continuous input and output
derivatives. For each nonzero direction, input-derivative injectivity ensures
that the denominator norm is nonzero; direction zero is handled separately as
the constant zero quotient. The arbitrary supremum over directions is lower
semicontinuous, so there is no unjustified countable-index assumption. The
proved chart correspondence transports this quantity through the inverse
chart to its actual open target in identifiableRealSet. At every regular point
that target is a neighborhood, giving lower semicontinuity after restriction
to regularSet. Its Borel measurability and the already proved measurable
regularSet justify AEMeasurable under regularVolume.

No inference to tensorVolume, full-measure regularity or integrability is made.
All five exports compile without warnings, have only propext, Classical.choice,
Quot.sound in their closures, and pass LeanCert kernel assertions. This is a
local macOS check using pinned dependency caches, not Linux Comparator or
whole-TR06 verification. Attribution remains George Stepaniants/Caltech and
Matthew J. Colbrook for the original mathematical proof.
