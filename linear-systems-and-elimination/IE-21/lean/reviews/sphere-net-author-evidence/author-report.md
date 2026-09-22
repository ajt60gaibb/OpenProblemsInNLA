# Exact sphere-net development evidence

Author: Codex AI root, 2026-09-22. The exact frozen `sphere_net` is implemented. Original analytic argument: Matthew J. Colbrook. Formalization credit: George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology.

The proof generalizes the disjoint-ball argument in Mathlib's `Besicovitch.card_le_of_separated`. Balls of radius δ/2 about a separated finite subset of the unit sphere are disjoint and contained in the ball of radius 1+δ/2. Haar volume scaling, cancellation of the positive finite unit-ball measure and division by the positive radius power yield exactly (1+2/δ)^n. Compactness supplies a finite half-radius cover and hence finite packing number. A maximal separated set is an internal closed δ-cover, with centers on the actual unit sphere. The proof works for every δ>0, including δ≥2, and retains the frozen n≥1 parameter. No cardinality-factor loss or explicit ball-volume/Gamma computation is used.

Local development compilation passed without diagnostics; the two public transitive axiom closures contain only propext, Classical.choice and Quot.sound. This is author evidence only. Independent review, actual Comparator, LeanCert kernel assertions and full authenticated reproducible Linux verification remain mandatory before publication.
