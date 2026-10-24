# Actual controlled normalized graph points and algebraic quasi-finiteness

23 October 2026. Author scope report by campaign recovery/geometry agent.
This report records authored proofs and execution, separately from independent
review, Linux CI, Comparator evidence, and canonical status promotion.

The source lock is `normalized-graph-controlled-source-lock-2026-10-23.json`.
The root-authored `NormalizedGraphParameter.lean` was recovered from its complete
recorded source snapshot and final extra-bullet removal; its proof constructs
the genuine pivot parameter of an actual smooth decomposition chart. The
retained original `chartPivotMap` derivative is injective, and the exact real
dimension equality makes it bijective. The continuous linear parameter
equivalence therefore gives a bijective actual chart-to-parameter derivative.
The exact decoded normalized graph agrees with the original branch on an
open neighborhood. No earlier frozen Model or retained source was edited.

`NormalizedGraphQuasiFiniteRows.lean` proves that the actual algebraic
row-coordinate map equals the selected Euclidean coordinates of the genuine
Hilbert graph point. The underlying coordinate decoder equality is literal
and proved by `rfl`; the selected rows may come from an arbitrary orthonormal
coordinate representation. It differentiates this actual equality, then uses
the bijective chart-to-parameter derivative to transport injectivity to every
genuine pivot parameter direction. No metric equality is asserted for the
auxiliary parameter equivalence.

`NormalizedGraphQuasiFiniteControlled.lean` retains the actual open Lipschitz
projection-inverse chart witness from `ControlledProjectionSet`. A whole-graph
smooth chart is transported through the exact Hilbert-to-Euclidean isometry.
The inverse's local norm comparison differentiates along actual real lines,
forcing the genuine selected projection derivative to be injective. This is
stronger data than real setwise local injectivity, which is not used as a
complex quasi-finiteness criterion.

The endpoint `controlled_normalizedGraph_exists_quasiFinite_character` starts
from an arbitrary actual whole-graph point and its controlled projection
witness. It supplies an actual pivot pattern, actual real parameter values,
proved nonzero amplitudes, exact equality with that same normalized graph
point, injectivity of the genuine projected parameter derivative, and actual
quasi-finiteness at the kernel of the genuine complex character. The last
step uses the separately proved real/imaginary point-derivation and cotangent
argument for arbitrary fixed real row maps. Finite fibers, algebraic
regularity certificates, and integrability are not premises of this endpoint.
All permutation branches are covered through the whole-graph chart theorem.

The restored unfinished Rows source originally failed at ordinary elaboration
steps. The completed proof establishes its decoder equality before applying
the row identity, uses the existing smooth-branch theorem's correct name,
and states both derivative chain equalities in explicit lambda form. The
initial Controlled compile lacked the `NNReal` notation scope; adding that
scope changed no mathematical statement or proof premise.

Both completed bridge modules passed author direct checks into separate
output objects, and then passed the shared author source closure replay.
Their kernel assertions pass, and the printed main-theorem axioms are only
`propext`, `Classical.choice`, and `Quot.sound`. The direct author receipt is
in the persistent recovery evidence under
`geometry/controlled-direct-check/result.json`; it explicitly records reused
project dependency objects rather than claiming a fresh closure check.
Separate independent reviewers bind their own reports and fresh source
replays to the frozen source hashes.
