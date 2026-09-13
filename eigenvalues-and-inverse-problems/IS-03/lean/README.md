# IS-03: verified derivative-realizability counterexample

**The complete original derivative-realizability conjecture is Lean verified with a negative answer and all seven reviewed exports.** Two independent statement approvals preceded implementation; two independent final proof approvals followed. The unchanged proof at [revision f87375f](https://github.com/sgstepaniants/OpenProblemsInNLA/tree/f87375fa5d7926fe0e065199eaab8f15ac5a5e48/eigenvalues-and-inverse-problems/IS-03/lean) passed actual sandboxed Linux Comparator/default-kernel verification in [run 34728101436](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34728101436). The [independent operational audit](verification/linux-2026-09-12/OPERATIONAL-REVIEW.md) and [root acceptance](verification/root-operational-2026-09-12/ROOT-CHECKS.json) checked the real execution and all 303 submitted inputs. The [canonical entry](../README.md) records the complete verified scope.

Formalization: **George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology, Pasadena, California, USA**, with
AI-agent assistance. **Matthew J. Colbrook**, Department of Applied Mathematics
and Theoretical Physics, University of Cambridge, retains mathematical
authorship of the counterexample. Johnson and
Hoover–McCormick–Paparella–Thrall retain the original conjecture and source
attribution. The root coordinator and `/root/solved_statement_inventory`
coauthored the statement package and implementation; neither is an independent
final referee. Historical candidate documentation was prepared by the latter implementation
agent. Publication preparation is by `/root/formal_review_standards`, the
independent final mathematical referee 2; this preparation is not an additional
mathematical review. No email, source-author endorsement, external human peer review or new
mathematical priority is claimed. The included Apache 2.0 license applies to
the new formalization code and does not relicense the source manuscript.

## Complete target and proved scope

[Definitions](NLA/IS03/Definitions.lean) retains the entire original claim:
for every natural `n ≥ 5` and every real entrywise-nonnegative `n × n` matrix
`A`, an entrywise-nonnegative real matrix of **exactly order `n - 1`** realizes
the normalized derivative of `A.charpoly`. These are genuine Mathlib matrix
characteristic polynomials, real formal polynomial differentiation and real
reciprocal scalar multiplication. No symmetry, diagonalizability,
irreducibility, invertibility, simple-spectrum or trace assumption is added.

The unchanged source witness is the order-seven matrix `diag(1/2, C₂, C₄)`.
Its actual characteristic polynomial and normalized derivative are proved to
be

```
p = (X - 1/2) (X² - 1) (X⁴ - 1),
q = p'/7
  = X⁶ - (3/7)X⁵ - (5/7)X⁴ + (2/7)X³ - (3/7)X² + (1/7)X + 1/7.
```

For **every real order-six matrix** `B` with `B.charpoly = q`, the first seven
actual traces of matrix powers are proved to be

```
3/7, 79/49, 48/343, 6731/2401, 5213/16807,
219766/117649, -8593/823543.
```

Characteristic-polynomial equality is the only premise of that trace theorem;
even entrywise nonnegativity is not assumed there. A generic theorem then
shows that every natural power of an entrywise-nonnegative real matrix has
nonnegative trace. The negative seventh trace rules out an order-six
realization and refutes the full universal conjecture.

[Solution](Solution.lean) provides exactly the seven frozen
[Challenge](Challenge.lean) signatures in namespace `NLA.IS03`:

| Export | Proved contract |
| --- | --- |
| `nonnegative_power_trace` | Every natural power of every entrywise-nonnegative real square matrix has nonnegative entries and trace, including order and power zero. |
| `witness_admissible` | The actual source matrix is entrywise nonnegative and has trace `1/2`. |
| `witness_polynomials` | Its genuine characteristic polynomial and normalized derivative equal the displayed polynomials; the derivative is monic of degree six. |
| `trace_moment_certificate` | Every real order-six matrix with that characteristic polynomial has all seven stated power traces, without additional spectral assumptions. |
| `negative_moment` | The seventh value is exactly `-8593/823543` and is strictly negative. |
| `counterexample` | The admissible source matrix has no entrywise-nonnegative order-six realization of its actual normalized derivative. |
| `not_derivativeRealizabilityConjecture` | Unconditional negation of the complete original all-order assertion. |

The source's stronger exclusion of arbitrary zero padding, its separate Monov
consequence, minimal-order questions and historical priority are outside these
seven exports. They are not needed to refute the complete exact-order target.

## Genuine algebra and the material LeanCert certificate

[PROOF_MAP.md](verification/PROOF_MAP.md) maps the modules and retained
dependencies. Exact block characteristic-polynomial identities handle the
source matrix; the largest direct determinant expansion is order four.
An explicit exact Bézout identity proves `q` separable. Complex splitting and
the degree-six root count then produce an actual eigenbasis for every
potential real realization after complexification. **Diagonalizability is
derived**, not assumed. Genuine basis, trace, power, characteristic-polynomial
and real/complex transport identities prove the full factorization and the
trace-power equality for every natural power.

The generic [Newton module](NLA/IS03/Newton.lean) applies actual Vieta and
Newton identities to an arbitrary family of six complex numbers whose full
factor product is `q`. It does not assume the family is distinct and retains
multiplicities. The seven exact recurrences determine the power sums. In the
spectral bridge, separability and the complete factor product justify the
root indexing; a bare set of eigenvalues does not replace multiplicities.

The only interval certificate is **`(-8593/823543 : ℝ) < 0`**, proved by
explicit `interval_decide (trust := kernel)` on the singleton `[0,0]` in
[Numerical](NLA/IS03/Numerical.lean). Its retained Boolean checker proof feeds
`negative_moment`, the nonnegative-trace contradiction and the final universal
negation. Both final referees independently replayed that exact retained
Boolean input using `decide +kernel`. Matrix identities, the arbitrary-matrix
spectral bridge and the generic Newton identities are exact proofs; no root
approximation, numerical eigensolver, root isolation or interval subdivision
is used.

The solution has no admission, custom axiom, native execution trust or
Challenge import. All 18 internal/public candidate axiom reports and the
corresponding kernel trust checks permit only `propext`, `Classical.choice`
and `Quot.sound`. The seven deliberate Challenge placeholders remain isolated
and prove nothing. [Comparator](comparator.json) selects exactly these seven
exports, no definition exceptions and only the standard three axioms.

## Checks actually performed and reproduction

The author ran ten fresh macOS direct-source commands: eight implementation
modules, an actual-term inspector and separately invoked Challenge. Both final
referees independently ran eleven fresh commands, including their own
inspection and retained-checker audits. All proof commands passed; only the
seven intentionally separate Challenge holes warned. Both referees inspected
the complete actual type-and-body closure from all exports: 61 project
declarations, with 55 reachable from the full negation. Their required
material dependency sets contained 33 and 40 declarations respectively. Each
also independently reconstructed the exact source matrix, polynomial,
Bézout identity and trace moments using rational diagnostics. Those diagnostics
supplement the kernel proofs and are not proof oracles.

All local runs used fresh private project prefixes on macOS and the ten clean
pinned MI-22 dependency caches **read-only**, excluding old IS-03 and MI-22
project objects. No Lake build, dependency-source rebuild or Linux execution
is claimed for those checks. Complete command lines, absolute cache paths,
hashes, timestamps, raw outputs and actual dependency inspections are retained
in the author and independent referee evidence. This packaging did not rerun
Lean or download, copy or build dependencies.

Lean is pinned to **4.33.1**, Mathlib to
`0df444a360eaa60ab8c11dca51a86af692955474` and LeanCert to
`621a43d7cf21f87872392a01e874f2f1dbddc926`.
[lake-manifest.json](lake-manifest.json) fixes all ten dependencies. On a
normal checkout with its own pinned dependencies, explicitly check the proof:

```
lake build Solution
```

The frozen default target remains `Challenge`; plain `lake build` checks the
statement module. Historical author/referee runners retain checks against
their then-current README and local cache paths. Reproducing those records
requires their frozen snapshot rather than overwriting historical evidence.

From the immutable verified revision, follow the
[shared workflow](../../../docs/lean/README.md) on a configured
[non-root Linux host](../../../tools/lean/HARNESS.md). From the repository root:

```
tools/lean/bootstrap.sh /absolute/path/to/nla-lean-tools
tools/lean/selftest.sh /absolute/path/to/nla-lean-tools
tools/lean/verify.sh \
  eigenvalues-and-inverse-problems/IS-03/lean \
  /absolute/path/to/nla-lean-tools
```

These commands reproduce the verification from the immutable candidate. The
observed project-specific run and its scope are recorded below; success on
unrelated projects is not used to verify IS-03.

## Independent approvals and preserved history

- Statement referee 1: [report](reviews/statement-referee-1.md) and [23-file evidence manifest](reviews/statement-referee-1-evidence/EVIDENCE-MANIFEST.json), `/root/leancert_examples`.
- Statement referee 2: [report](reviews/statement-referee-2.md) and [26-file evidence manifest](reviews/statement-referee-2-evidence/EVIDENCE-MANIFEST.json), `/root/formal_review_standards`.
- Final proof referee 1: [report](reviews/proof-referee-1.md) and [36-file evidence manifest](reviews/proof-referee-1-evidence/EVIDENCE-MANIFEST.json), `/root/leancert_examples`.
- Final proof referee 2: [report](reviews/proof-referee-2.md) and [45-file evidence manifest](reviews/proof-referee-2-evidence/EVIDENCE-MANIFEST.json), `/root/formal_review_standards`.
- Author records: [proof-start gate](verification/proof-start.json), [completion](reviews/proof-completion.md), [fresh checks](verification/final/latest.json) and [203-input proof freeze](verification/proof-freeze.json).
- Coordinator acceptance: [both final approvals accepted](verification/final-review-acceptance.json). The coordinator coauthored the Newton module; this acceptance is not a third independent review.

The reviews apply the ten pinned Tau Ceti angles as adapted by the repository's
[review protocol](../../../docs/lean/REVIEW.md). They are AI-agent reviews, not
an official Tau Ceti service result or external human peer review. Referee 2
also contributed to shared infrastructure but did not author the IS-03
statements or proof. Schiffer and Forsythe supply campaign organization and
workflow examples; no mathematical theorem from those projects is assumed.

The exact statement-stage README is archived at
[README.statement.md](verification/linux-candidate-2026-09-12/README.statement.md).
Only the live README changes among the 203 proof-freeze inputs; all other
202 inputs, all ten original Git source blobs and every statement/final
report and evidence file remain unchanged. The new
[v0.4 manifest](formalization.yaml) records the complete scope and completed
Linux gate. The earlier
[NUMERICAL_TARGETS.md](NUMERICAL_TARGETS.md),
[SourceCorrespondence.md](SourceCorrespondence.md), source manifest and
phase-specific handoffs retain their historical 12 September 2026 wording;
the completed proofs and later reviews supersede their pending-work notices.

## Actual Linux verification and publication preservation

The successful Ubuntu 24.04 run freshly cloned all ten dependencies at their
exact pins and used 8690 official Mathlib cache artifacts before checking the
project source. Challenge and Solution build graphs completed with 1718 and
3101 jobs respectively; these graph counts do not assert full dependency-source
rebuilds. The Solution phase emitted no warnings. Its seven declarations matched
without definition exceptions, default-kernel replay passed, and all eighteen
internal/public transitive axiom reports contained exactly the standard three.

The target job and separate checker job each passed the actual sandbox probes,
three raw-kernel controls, five Comparator fixtures and the admission/native
execution negative controls. The nested Bubblewrap executable was denied
UID-map creation before its inner write; this does not claim that the inner
write executed or establish general sandbox security. Complete raw logs and
original artifact ZIPs are retained. The [Linux evidence manifest](verification/linux-2026-09-12/EVIDENCE-MANIFEST.json)
binds 444 files plus itself, including every nested manifest. Original project
ZIP SHA-256 is `5a72c6ed55af7aea388b74910cd0b0cbc2c81004427b145390fbe74f4ec1ac1e`;
checker-control ZIP SHA-256 is
`2ef6c60b6f7e7367fd72ba3e484ab7e350cf8970c8e6ae880bb4bbff494c5cb5`.
Both match GitHub metadata and actual upload logs. The retained 152-file full
run-log ZIP has a separately computed digest; no GitHub-published checksum
for that archive is claimed.

Operational reviewer `/root/leancert_examples` also served as independent
statement and final mathematical referee 1 and authored neither the statements
nor the proof. The root coordinator independently accepted the operational
evidence and actual GitHub records; root and `/root/solved_statement_inventory`
coauthored the proof and do not count as independent final referees. Publication
preparer `/root/formal_review_standards` is the other independent statement/final
referee and also contributed shared infrastructure. These roles do not increase
the number of mathematical referees. The [root operational evidence manifest](verification/root-operational-2026-09-12/EVIDENCE-MANIFEST.json)
retains six checked files plus itself.

The successful run verifies the immutable candidate, not a later metadata
revision. Publication changes only this README and five status/review fields
in the current manifest among its 303 submitted inputs. All other 301 inputs,
all 445 Linux evidence files and all seven root operational evidence files
remain byte-identical. The exact preceding [README](verification/publication-2026-09-12/archive/README.linux-candidate.md)
and [manifest](verification/publication-2026-09-12/archive/formalization.linux-candidate.yaml)
are archived. All 202 non-README proof-freeze inputs, all 34 statement inputs
through their exact README archive, all ten original source snapshots and every
review/evidence record are preserved. The canonical original problem statement
and mathematical source are unchanged. Earlier phase-specific pending notices
remain historical records.

A separate publication review remains required before a publication commit,
push and individual upstream PR. This preparation reruns no Lean proof and
claims no external human review, official Tau Ceti endorsement, source-author
endorsement or new mathematical priority.
