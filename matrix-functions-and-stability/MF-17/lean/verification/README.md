# MF-17 verification evidence

**PASS — 30 September 2026 (UTC).** The complete repository harness exited 0
for source revision `ac582d01532a914538cbfb74863437b18433038a`.
All five advertised contracts passed fresh sandboxed statement comparison,
permitted-axiom checks and Lean's default-kernel replay.

| Evidence | Actual result |
| --- | --- |
| [Development build](build.log) | `lake build Challenge Solution`, 8,929 jobs, exit 0. |
| [Independent target types](statement-types.log) | All five signatures discharged in a Solution-only environment, exit 0. |
| [Transitive axioms](axioms.log) | All five use exactly `propext`, `Classical.choice`, `Quot.sound`, exit 0. |
| [Checker bootstrap](checker-bootstrap/bootstrap.log) | Pinned checker, exporter and Landrun built; input/tool receipt retained. |
| [Linux checker self-test](linux-selftest/result.json) | Real sandbox, three kernel controls, five Comparator controls, and forbidden-axiom rejection passed. |
| [Fresh Comparator run](linux-verification/comparator.log) | Challenge and Solution built separately; all five contracts accepted; default kernel accepts the solution. |
| [Complete driver log](linux-verification/driver.log) | All controls, actual proof check and fresh-copy cleanup succeeded; exit 0. |
| [Authoritative receipt](linux-verification/result.json) | Exact source revision, five declarations, allowed axioms, source inputs and tool receipt. |

The fresh Solution build completed 8,927 jobs. The five specification
placeholders occur only in Challenge, which Solution does not import.
The solution has no proof-side placeholders, additional axioms, definition
holes or native-execution trust. The imported source's symbolic argument
covers the full fixed-M target and contractive endpoint; it does not certify
unrelated numerical or leading-constant claims elsewhere in the manuscript.

Two independent retrospective AI reviews approve all five statements.
[Statement fidelity](../reviews/statement-fidelity.md),
[upper proof](../reviews/upper-proof.md), and
[lower proof/endpoint/attribution](../reviews/lower-proof.md) record their
actual coverage and accepted corrections. Their source-level conclusions
are distinct from these execution results; no external human peer review
is claimed. [NUMERICAL_TARGETS.md](../NUMERICAL_TARGETS.md) explains the
adapted lower construction and refined constants.

## Reproduction and provenance

Lean is 4.33.1; Mathlib is pinned to
`0df444a360eaa60ab8c11dca51a86af692955474`. All other dependencies are fixed
in `../lake-manifest.json`. From the repository root at the
[published source snapshot](https://github.com/ajt60gaibb/OpenProblemsInNLA/tree/cad3785440a2678b5b30aa8133d425e709b6811d),
on non-root Linux meeting `tools/lean/HARNESS.md`:

```sh
python3 tools/lean/harness.py bootstrap /tmp/mf17-tools
python3 tools/lean/harness.py verify \
  matrix-functions-and-stability/MF-17/lean /tmp/mf17-tools
```

The [runner record](linux-verification/README.md) documents the actual native
Linux environment and resource accommodations. The checker and its real
Landrun/Bubblewrap sandbox were unchanged. The verifier copied committed
ordinary source files into a fresh project, fetched pinned dependencies and
the trusted Mathlib cache, then compiled the project inside the sandbox.
No previous MF-17 compiled artifact was reused in that run.

The development build used the supplied dependency cache and fresh project
outputs; it is separately identified from the authoritative run. The
statement-type script initially needed explicit theorem arguments; its
corrected version is in the verified source revision. None of the 221 supplied
solution source files or the reviewed Challenge statements changed.
Later documentation, metadata and evidence additions do not alter those
verified mathematical inputs. The original local run commit was not published.
The [maintainer integration review](../reviews/maintainer-integration-2026-09-30.md)
matched the published snapshot's Lean sources, dependency pins, configuration,
numerical targets and original review reports to this receipt's hashes. The
catalog reviewed these retained execution records without rerunning Lean or
the Linux verifier. The historical receipt and runtime logs remain unchanged.

## Earlier unsuccessful attempts

Earlier failures are retained and do not count as passing verification:
[development file limit](build-initial-fd-limit.log),
[initial isolated file limit](linux-fd-limit/README.md),
[dependency-cache disk limit](linux-disk-limit/README.md),
[shared-filesystem reads](linux-concurrent-io/README.md),
[generated-output disk limit](linux-generated-output-limit/README.md), and
[accepted proof with incomplete cleanup](linux-cleanup-limit/README.md).
The complete exit-0 run above supersedes those attempts. No proof change
was needed to resolve these runner problems.
