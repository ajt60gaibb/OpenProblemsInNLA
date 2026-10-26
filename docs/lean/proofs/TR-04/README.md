# TR-04 complete computational proof

`NLA.Proofs.TR04.fullTarget` proves the unchanged, independently reviewed
`NLA.Statements.TR04.Target`. One fixed finite program `ttProgram`, with
`C = 1000000` and `k = 5`, precedes every permitted shape, positive rank tuple,
real input tensor, and legal full-SVD reply trace. The returned tensor is read
from actual dense output memory, satisfies every unfolding-rank constraint,
has squared error strictly below `(d−1) * Optimum` when the genuine optimum is
positive, and equals the input when that optimum is zero. Its charged cost is
at most `C * Size^k`.

The [canonical FullSolution](../../../../tensor-computations/TR-04/lean/FullSolution.lean)
exports this complete Target. Its [source lock](../../../../tensor-computations/TR-04/lean/proof-source-lock.json)
binds 184 exact shared-source copies, including 179 proof modules. There are
190 canonical Lean inputs. The [literal original statement](../../../../lean-statements/NLA/Statements/TR04.lean)
and [reviewed mirror](../../../../lean-statements/Reviewed/TR04.lean) have a
separate kernel-checked definitional identity.

## Review and kernel evidence

- The [full Target author receipt](campaign-2026-10-26/tt-full-target-author/result.json)
  records 182 fresh project producers and one literal-statement consumer.
  Pinned external package objects were reused; project objects were absent.
- Two independent package source audits check the complete 205-file inventory,
  source-copy identity, wrappers, dependency pins, original bytes, and selected
  theorem types: [algebra](campaign-2026-10-26/independent-canonical-package-algebra/APPROVAL.json)
  and [geometry](campaign-2026-10-26/independent-canonical-package-geometry/package-source-audit.json).
- The [independent canonical engine receipt](campaign-2026-10-26/independent-canonical-package-geometry/receipt.json)
  records 190 fresh producers and five proof, identity, support and rejection
  consumers. Both deliberate `sorryAx` controls reject as required.
- The [comprehensive non-author source acceptance](campaign-2026-10-26/independent-full-target-review/ACCEPTANCE.json)
  binds all 190 fresh producers, seven positive consumers and one expected
  challenge rejection. It audits 1,821 exact kernel identities. The original
  aggregate reported false because its negative-control parser did not expect
  Lean to print an axiom list after an error. That original result and driver
  remain intact; the [separate terminal validation](campaign-2026-10-26/independent-full-target-review/TERMINAL_VALIDATION.json)
  checks the unchanged raw outputs and exact intended `sorryAx` rejection.
- The [cumulative integrity index](campaign-2026-10-26/independent-evidence-index/result-through-full-target-v2.json)
  binds 42 approved scopes. Its [portability sidecar](campaign-2026-10-26/independent-evidence-index/full-target-index-portability-review.json)
  retains earlier diagnostics and defines the exact artifact staging set.
- The [actual Linux receipt](LINUX_CI_RECEIPT.md) records Comparator statement,
  theorem-kind and axiom comparison, default-kernel replay, LeanCert kernel
  audit, and actual rejection/isolation controls on the executed PR merge.

The selected proof constants use only `propext`, `Classical.choice`, and
`Quot.sound`; the two retained elementary count exports use no axioms. The
source and package reviews identify reviewer-authored prerequisites explicitly.
They do not claim external human endorsement.

## Preserved originals and scope

All 25 original input files are retained byte for byte in the
[preservation archive](originals-before-full-proof-2026-10-26/manifest.json).
The canonical problem ID, path, mathematical target, TeX, PDF, source credit,
and reviewed computation model are preserved. Display/status promotion leaves
the complete original problem-statement suffix unchanged.

The historical canonical `Challenge.lean`, `Solution.lean`, `SPEC.md`, and
`README.md` stay at their original paths with their original bytes. The older
`tr04Statement` scaffold permits an arbitrary `unfoldingRank`; it is retained
and is not asserted proved. Separate `FullChallenge` and `FullSolution`
compare the concrete original computational Target. `FullSolution` imports
neither challenge. The full challenge contains one intentional comparison
placeholder, which is rejected by a direct kernel-trust test.

The result concerns the original idealized arithmetic/full-SVD model. The
[retained original resolution](../../../../tensor-computations/TR-04/README.md)
states its mathematical scope and source attribution.
