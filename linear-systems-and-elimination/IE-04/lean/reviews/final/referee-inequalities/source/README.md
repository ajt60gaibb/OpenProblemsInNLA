# IE-04 Lean formalization

George Stepaniants, Department of Computing and Mathematical Sciences,
California Institute of Technology, Pasadena, California, USA.
AI-assisted mathematical solution and formalization. Historical conjecture
credit remains with Spielman and Teng.

**The complete proof graph has compiled; canonical verification is pending.**
All 21 frozen targets passed the actual non-root Linux development command
`lake build NLA.IE04.Solution` in
[run 35031607095](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/35031607095/job/104591152756)
at Git revision `4bd2d76ec6e37696ff0c2d5feacf21e342371f27`.
Every target passed its LeanCert kernel assertion and reported only `propext`,
`Classical.choice` and `Quot.sound`. This package preserves those exact proof
bytes. The overall shared workflow failed in the separate unfinished MF-12
project; its original receipt and logs are retained without relabeling it.

The result proves the full negative resolution: no universal positive real
constants give the proposed exponential tail for Gaussian-smoothed partial
pivoting. It uses the actual GEPP trajectory and entry-growth maximum, genuine
independent standard Gaussian entries, every admissible tie rule, a whole
nonsingular perturbation box, and arbitrary positive real proposed constants.
The allowed identity center and noise scale one already give the contradiction.
No behavior on singular inputs is used to manufacture a counterexample.

The only numerical certificate is the fixed inequality `exp(-2)>1/8`, checked
by LeanCert in kernel mode. Exact scalar estimates, symbolic induction,
monotonicity and product measures remove any need for high-dimensional interval
subdivision, sampling, or numerical integration.

From this directory, with the pinned Lean toolchain available:

```bash
lake exe cache get
lake build +Solution
```

The default `lake build` also selects Solution. This is a package-configuration
transition from the statement phase; it changes no mathematical declaration
or dependency revision. A build alone does not run the repository's stronger
[canonical verification protocol](../../../docs/lean/README.md).

[Challenge.lean](Challenge.lean) contains the 21 independent frozen statement
contracts with deliberate placeholder bodies. [Solution.lean](Solution.lean)
imports the proved graph, never Challenge. The exact numerical statements,
definitions and contracts were reviewed by two independent agents and
successfully elaborated on Linux before proof construction. Their original
draft labels and source bytes are retained in
[the frozen statement record](reviews/statement-phase/frozen).

[Both mathematical source reviews](reviews/proof-source) and the
[independent development-evidence addendum](reviews/proof-source/referee-inequalities/development35031607095-addendum/REVIEW.md)
are retained. The [root referee’s current-source addendum](reviews/proof-source/referee-root/DEVELOPMENT-ACCEPTANCE.md)
also binds the complete accepted source and development run. Both referees must
still inspect the actual standalone canonical checks. These are AI-agent
reviews under scoped Tau Ceti standards, not official certification or external
human peer review.

[SourceCorrespondence.md](SourceCorrespondence.md) explains the whole original
target and prior IE-05 API reuse. [formalization.yaml](formalization.yaml)
records every target and its current status;
[ACTIVE-SOURCE-MANIFEST.json](ACTIVE-SOURCE-MANIFEST.json) binds the compiled
mathematical bytes. The [raw development evidence](verification/development-2026-09-15)
and [packaging transition](verification/packaging) distinguish the tested
development revision from this new standalone candidate.

Actual canonical Comparator, independent default-kernel replay, required
negative controls and final source/evidence referee acceptance remain pending.
The canonical problem status and indexes have not been changed by this package.
