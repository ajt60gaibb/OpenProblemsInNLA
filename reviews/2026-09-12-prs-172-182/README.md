# Maintainer audit of PRs 172–182

**PASS for PRs #172, #173, #174, #177, #178, #179, #181 and #182 at the exact revisions below.** The coordinating Codex agent and separately assigned review agents checked the claims and original targets. These are informal AI-agent reviews; external human peer review and historical priority are not asserted. The four Lean promotions additionally have authenticated Linux Comparator and default-kernel evidence.

| PR | Reviewed head | Result |
| --- | --- | --- |
| [172](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/172) | `185a7c394b3c89a28cc0daaab12cc54de6c04173` | RA-07: complete convexity target, Lean verified |
| [173](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/173) | `af65452c26fba4223555fa302d318a2ca50457c3` | MI-23: complete conjecture negation, Lean verified |
| [174](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/174) | `856b1618b1cad046b3640a13de0df5ef4c10a8f3` | TR-15: complete conjecture negation, Lean verified |
| [177](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/177) | `8b056c604f53070a7d351743cdc4784c1403aad8` | KE-01: partial results; general target remains open |
| [178](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/178) | `89be234df62de181d27e3954d8ba30b9ab072d63` | IE-16: complete negative solution |
| [179](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/179) | `7ffdc89f5b686574b7d9d7df1f10cedec62bd02c` | IE-12: complete exact-real arithmetic target solved |
| [181](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/181) | `fed3f4bcfd11de1d6509522849e8ffa773007979` | KE-02, SP-08, SP-09: partial results; SP-03 and SP-07 remain Open |
| [182](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/182) | `0212a62c25e02f38a74ce9af5504e37630309a3f` | FR-12: complete counting conjecture negation, Lean verified |

## Mathematical reviews

- [RA-07](PR172-review.md): actual elementary symmetric sums, derivative factorization with repeated roots, positive denominator and every original endpoint.
- [MI-23 and FR-12](PR173-PR182-cross-review.md): independently checked after the coordinator read every actual Lean source file. MI-23 uses genuine CFC powers, complete characteristic-root multiplicities and the complex Euclidean operator norm. Its exact norm gap violates the first required prefix inequality. FR-12 counts finite labeled real matrix sets, proves an injective permutation-indexed doubling map and refutes every positive real proposed constant. Its stronger informal double-factorial recurrence is explicitly outside the Lean exports.
- [TR-15](PR174-review.md): actual ordered tensor contractions, all-vector lower positivity and a genuine lower eigenpair; the implication's premise is nonvacuous.
- [KE-01](PR177-review.md): structured subclasses and their costs, with the general sparse bounded-tail target retained.
- [IE-16](PR178-review.md): the original normal-GMRES bound is refuted; all 126 exact subset certificates were independently reconstructed.
- [IE-12](PR179-review.md): worst-case quadratic cost with respect to dimension, exact permitted primitives, distribution, filter and A-only backward error. No finite-precision or practical-speed claim is inferred.
- [Spectral partial results](PR181-review.md): precise scopes and remaining cases. The coordinator also independently read the complete SP-08 signed-threshold reduction, root-bound proof and all three checking programs. The perturbation argument handles zero entries, integer bounds exclude overflow, full polynomial-set equality establishes coverage, and exact rank-two attainers meet the bounds. Fresh full reruns checked 32,768, 524,288 and 2,097,152 patterns, respectively. These finite cases do not settle the all-orders conjecture.

Eight pre-attribution Markdown originals in the spectral pack were unavailable to the maintainers in this audit. Their disclosed hash differences could not be checked for exact semantic preservation against those originals. Their final mathematical contents were independently reviewed. The review records distinguish this provenance limitation from the mathematical verdict.

## Operational evidence and integration

[Authenticated upstream CI evidence](upstream-ci-evidence.json) binds **1,662 input hashes, 28 exports and 105 transitive axiom reports** across the four new Lean projects. Each actual GitHub run succeeded, its checked merge commit includes the reviewed PR head, and every input matches the integrated project. Comparator accepted the statements and default-kernel replay. Axioms were confined to `propext`, `Classical.choice` and `Quot.sound`; all sandbox, kernel and Comparator controls passed, including actual rejection of native and sorry axioms. All four v0.4 manifests passed schema and export-coverage validation. No authoritative Linux run was claimed on the local macOS host.

The integration retains all eight reviewed heads and all **4,646 previously published paths** from main `f41f1f9ffa2171550d4bb795862c6170c4f26070`. [File comparison](integration-preservation.json) confirms unchanged authored files apart from merged indexes/archive and two PDF layout corrections. The IE-12 and FR-12 canonical TeX each gain one page break before references; the renderer preserves these choices. [Publication review](lean-publication-review.md) and [final reflow review](pdf-reflow-review.md) record visual checks. No mathematical manuscript or Lean project was altered during integration.

All **217 permanent IDs** and canonical paths are unchanged. The required ID validation, catalog regeneration and 17 ID tests passed throughout integration. All [77 repository tests](repository-tests.log), math-format checks and final manifest checks passed. The final catalog has **15 Lean verified, 77 Solved, 53 Open and 72 Partially resolved** entries; **125 targets retain open cases**.

This committed record precedes the final integration CI run. Publication remains conditional on that run and the required GitHub checks passing; the integration PR records their final outcome.
