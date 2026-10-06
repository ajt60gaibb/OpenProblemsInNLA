# Independent review: exact event measurability

2026-10-06. Reviewer: coordinator AI agent, independent of the implementing
agent. The reviewed source is `NLA/IE06/Measurability.lean`, SHA-256
`8bc5c37b83630e26e1d2e64c86971aee23c9640e384796ea929223ebed535592`.

The proof uses the actual product measurable space on matrix coordinates.
For each fixed finite pivot path, each Schur update is a composition of real
arithmetic and fixed coordinate selections. Total real division is measurable;
nonzero pivot validity remains a separate admissibility condition. Recursion
therefore gives measurable trajectories for every stage, including totalized
out-of-range stages.

Finite NNReal suprema encode the exact entry maxima. Their real coercions and
the actual input normalization are measurable, without replacing the norm by
a bound or assuming growth measurability. The admissible-path set is a finite
intersection of active-index conditions, pivot nonzero conditions, and
non-strict magnitude comparisons. Determinant measurability is proved by its
finite polynomial formula. The final event is the nonsingular guard intersected
with the finite union over every possible path. It retains all tie choices;
no deterministic-path replacement occurs.

The exact exported theorem has no additional premise:
`exceedanceEvent_measurable_proved (n : ℕ) (t : ℝ) :
MeasurableSet (exceedanceEvent n t)`.
The false positive-dimension guard handles dimension zero by the empty set.

Source inspection found no hidden assumptions or altered definitions.
The implementation's eleven kernel assertions and its retained compile
evidence are consistent with this proof. Approved for integration; this is
a foundation for the probability theorem, not its tail estimate.
