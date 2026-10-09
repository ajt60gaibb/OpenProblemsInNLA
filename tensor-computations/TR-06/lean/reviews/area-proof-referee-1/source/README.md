# TR-06 rectangular area proof artifact

This temporary development artifact proves exactly the independently reviewed `NLA.TR06.induced_volume_chart` declaration, plus a general injective-immersion area formula. It does not prove all of TR-06.

## Files for integration

Copy only `NLA/TR06/{NormDet,Rectangular,LocalVolume,Density,Radius,Area}.lean` into the pinned project. The local `Definitions.lean` is a byte-identical development copy of the approved boundary and should not overwrite it. `Area.lean` imports Definitions, never Challenge. `FINAL-EVIDENCE.json` records all six final source hashes and successful logs 031–036. Log 030 checks the frozen Definitions copy. Prior numbered logs retain development errors; they are not verification successes.

## Proven mathematics

- Continuity of rectangular normDet through its Gram determinant.
- Local upper/lower Hausdorff measure bounds for a map approximating an injective rectangular linear map.
- A density-point derivative estimate, generalized to arbitrary codomain.
- Exact area formula for an injective map with injective within-derivative at every point of any measurable domain. Infinite-volume domains are exhausted by disjoint finite-volume pieces.
- Exact `induced_volume_chart`, instantiated from the actual smooth embedding in `DecompositionChart`. Its complete theorem header is byte-identical to Challenge.

The measure is Euclidean-normalized Hausdorff measure `μHE[m]`. No loss through arbitrary normalization or an extra artificial chart hypothesis occurs.

## Trust and attribution

Every owned module sets `leancert.trust` to `kernel`. The final theorem and all central foundations pass `#assert_trust kernel`, with printed axiom closure exactly `propext`, `Classical.choice`, `Quot.sound`. There is no `sorry`, `admit`, `native_decide`, custom axiom, or Challenge import in the proof closure.

These are pinned Lean 4.33.1 development elaboration and trust checks against existing pinned dependency caches on macOS arm64. Fresh Linux verification and Lean4 Comparator have not been run by this subagent. Reproducible project integration, independent proof review, comparator and full-problem verification remain the root task's responsibility.

The density-point and partition/integration proofs adapt the corresponding Mathlib Jacobian code, preserving Sébastien Gouëzel's 2022 copyright and attribution. New rectangular estimates and adaptation credit George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology. The original TR-06 mathematical proof attribution to Matthew J. Colbrook remains unchanged in the frozen definitions/canonical source.

Run the local development check with `/private/tmp/tr06-python/bin/python check.py NLA.TR06.Definitions NLA.TR06.NormDet NLA.TR06.Rectangular NLA.TR06.LocalVolume NLA.TR06.Density NLA.TR06.Radius NLA.TR06.Area`. The local runner uses absolute pinned compiler/dependency cache paths recorded in each evidence JSON, and writes only this temporary artifact.
