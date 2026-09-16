# IE-04 Lean formalization

George Stepaniants, Department of Computing and Mathematical Sciences,
California Institute of Technology, Pasadena, California, USA.
AI-assisted mathematical solution and formalization. Historical conjecture
credit remains with Spielman and Teng.

**The complete 21-target proof passed canonical Linux verification.**
[Run 35034399633](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/35034399633/job/104600154206)
checked immutable proof revision `026b3e5534a4d6e15ebffb85318c2ff031df32bf`
on 15 September 2026. LeanCert kernel assertions, actual non-root Comparator,
independent default-kernel replay and all required rejection and sandbox
controls passed. Every exported proof reports only `propext`, `Classical.choice`
and `Quot.sound`. The [original runtime evidence](verification/linux-2026-09-15)
and [both independent final referee reports](reviews/final) are retained.
Later documentation commits preserve the accepted proof and configuration bytes
and require their own publication workflow execution.

The result proves the full negative resolution: no universal positive real
constants give the proposed exponential tail for Gaussian-smoothed partial
pivoting. It uses the actual GEPP trajectory and entry-growth maximum, genuine
independent standard Gaussian entries, every admissible tie rule, a whole
nonsingular perturbation box, and arbitrary positive real proposed constants.
The allowed identity center and noise scale one already give the contradiction.
No behavior on singular inputs is used to manufacture a counterexample.

The only numerical certificate is the fixed inequality `exp(-2)>1/8`, proved
by LeanCert in kernel mode and consumed by the Gaussian density lower bound.
Exact scalar estimates, symbolic induction, monotonicity and product measures
remove any need for high-dimensional interval subdivision, sampling, or
numerical integration. The resulting probability lower bound is
`2^(-n^2*(n^2+n+5))` at growth threshold `(3/2)^(n-1)/2` for every `n≥2`.

From this directory, with the pinned Lean toolchain available:

```
lake exe cache get
lake build +Solution
```

The default `lake build` also selects Solution. A build alone does not run the
repository's stronger [canonical verification protocol](../../../docs/lean/README.md).
The full isolated Linux command, after preparing the pinned checker and sandbox,
is `tools/lean/verify.sh linear-systems-and-elimination/IE-04/lean /tmp/nla-lean-tools`
from the repository root. CI performs that preparation and runs the same check.

[Challenge.lean](Challenge.lean) contains the 21 independent frozen statement
contracts with deliberate placeholder bodies. [Solution.lean](Solution.lean)
imports the proved graph, never Challenge. The exact numerical statements,
definitions and contracts were reviewed by two independent agents and
successfully elaborated on Linux before proof construction. Their original
draft labels and source bytes remain in the
[frozen statement record](reviews/statement-phase/frozen).

The earlier complete development run 35031607095 accepted IE-04, but its shared
workflow failed in the separate unfinished MF-12 project. Its
[original receipt and logs](verification/development-2026-09-15) retain that
status. The accepted standalone canonical run is separately recorded above.
[Both source reviews](reviews/proof-source), their development addenda and the
[final source/runtime reviews](reviews/final) preserve each review's exact inputs.
These are AI-agent reviews under scoped Tau Ceti standards, not external human
peer review or official certification by the Tau Ceti project.

[SourceCorrespondence.md](SourceCorrespondence.md) explains the whole original
target and prior IE-05 API reuse. [formalization.yaml](formalization.yaml)
records every checked result; [ACTIVE-SOURCE-MANIFEST.json](ACTIVE-SOURCE-MANIFEST.json)
binds the exact mathematical bytes. The
[packaging history](verification/packaging) and
[publication transition](verification/publication-2026-09-15/TRANSITION.json)
retain the original metadata. The inequalities referee later prepared metadata
and this standalone package; that contribution is separate from its independent
mathematical review and is subject to coordinator review.
