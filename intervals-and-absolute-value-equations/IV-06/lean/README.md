# IV-06: verified interval-eigenvalue component counterexample

**The complete original interval-eigenvalue component conjecture is Lean verified with a negative answer and all eight reviewed exports.** Two independent statement approvals preceded implementation; two independent final proof approvals followed. The unchanged proof at [revision 18b5ef3](https://github.com/sgstepaniants/OpenProblemsInNLA/tree/18b5ef3127da0ae4f68e09289f60fd4f6e3d9bcb/intervals-and-absolute-value-equations/IV-06/lean) passed actual sandboxed Linux Comparator/default-kernel verification in [run 34725713519](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34725713519). The [independent operational audit](verification/linux-2026-09-12/OPERATIONAL-REVIEW.md) and [root acceptance](verification/root-operational-2026-09-12/ROOT-CHECKS.json) checked the real execution and all 200 submitted inputs. The [canonical entry](../README.md) records the complete verified scope.

Formalization: **George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA**, with AI-agent assistance. **Matthew J. Colbrook**, Department of Applied Mathematics and Theoretical Physics, University of Cambridge, retains mathematical authorship of the counterexample. The implementation and historical candidate packaging are by `/root/solved_statement_inventory`. Publication preparation is by `/root`, who also served as statement referee 1 and final proof referee 2; packaging and operational acceptance are not additional mathematical reviews. No George email, new mathematical priority or external human peer-review claim is added.

## Complete original target and proved scope

The [canonical problem](../README.md) quantifies over every positive dimension and every pair of real matrix endpoints ordered entrywise. Every entry varies independently through its prescribed closed interval; singleton intervals are allowed. [Definitions](NLA/IV06/Definitions.lean) uses the entire box, a genuine nonzero real eigenvector, and the actual set of all attained real eigenvalues. The component count is `Cardinal.mk (ConnectedComponents S)` for that real subset with its inherited topology. Infinite component sets cannot be assigned zero through a natural-cardinality convention. No symmetry, diagonalizability, all-real-spectrum, compactness or finite-component premise is added.

The unchanged source witness is

```
A(a,b) = [[25,a,b], [1,-1,0], [1,0,1]],
-166 <= a <= -16,  9 <= b <= 159.
```

[Proof](NLA/IV06/Proof.lean) identifies the complete independent-entry box with this family in both directions, proves the actual all-real determinant polynomial, and supplies admissible nonzero integer eigenvectors at `-3, 0, 3, 25`. For every matrix in the full box, the determinants at `-1, 1, 12` lie respectively in `[-332,-32]`, `[-318,-18]`, and `[-3750,-150]`. The three separators therefore never occur in the attained eigenvalue set.

A generic theorem for arbitrary real subsets proves that equal actual component classes force every intermediate real point into the set. An injection from `Fin 4` into the actual component quotient then establishes at least four components for this dimension-three box. The final theorem negates the entire original universal assertion. Neither exactly four components, every component endpoint nor a full determinant-range surjectivity theorem is claimed or needed.

[Solution](Solution.lean) exports the exact eight [Challenge](Challenge.lean) signatures, all in namespace `NLA.IV06`:

| Export | Proved contract |
| --- | --- |
| `eigenvalue_determinant_semantics` | Genuine nonzero eigenvector iff actual characteristic determinant is zero, for every real matrix, including dimension zero. |
| `family_and_determinant_semantics` | Full-box equivalence and unrestricted real characteristic determinant formula. |
| `witness_eigenpairs` | Four admissible matrices, actual nonzero eigenvectors, matrix-vector equations and attained-set membership. |
| `witness_separators` | Universal bounds for every box member, strict negativity and exclusion of all three separators. |
| `connected_component_intervals` | Actual connected-component equality implies real interval containment for an arbitrary real subset. |
| `four_components` | Actual representatives and an injective component-class map, yielding the genuine cardinal lower bound four. |
| `counterexample` | Valid original endpoints with component cardinality strictly exceeding dimension three. |
| `not_componentBoundConjecture` | Unconditional negation of the full original all-dimension, all-real-box claim. |

The source mapping, numerical statements and original document identities remain in [SourceCorrespondence.md](SourceCorrespondence.md), [NUMERICAL_TARGETS.md](NUMERICAL_TARGETS.md) and [source-inputs.json](source-inputs.json). Their statement-stage language is a historical record of 12 September 2026, superseded by the later proof and review evidence linked here; those frozen bytes have not been rewritten.

## Material LeanCert computation and trust

The only numerical interval certificate is **`(-18 : ℝ) < 0`**, proved by explicit `interval_decide (trust := kernel)` on the singleton `[0,0]`. Every determinant upper bound is at most `-18`. The actual checked certificate therefore feeds separator exclusion, component separation, cardinality and the final negation. It certifies the scalar sign; exact matrix algebra, universal affine bounds, genuine connectedness and cardinality supply the rest of the proof. No eigenvalue approximation, root isolation or interval subdivision is used.

All **17** internal/public explicit kernel checks and transitive axiom reports admit only `propext`, `Classical.choice` and `Quot.sound`. Both final referees inspected the actual retained private checker proof, and independently repeated its exact Boolean input using `decide +kernel`. The complete solution has no admission, custom axiom, native execution trust or Challenge import. The eight deliberate Challenge placeholders remain isolated and prove nothing. [Comparator](comparator.json) lists exactly the eight exports, no definition exceptions and only the standard three permitted axioms.

Lean is pinned to **4.33.1**, Mathlib to `0df444a360eaa60ab8c11dca51a86af692955474` and LeanCert to `621a43d7cf21f87872392a01e874f2f1dbddc926`. [lake-manifest.json](lake-manifest.json) fixes all ten dependencies. The [actual v0.4 manifest](formalization.yaml) records the exact scope, attribution, reviews and completed Linux gate.

## Checks actually performed and reproduction

The author completed five fresh direct Lean commands: Definitions, Proof, Solution, an actual-term inspector and separately invoked Challenge. Each independent final referee completed six fresh commands, additionally auditing and repeating the retained checker. Complete implementation and inspector commands passed without warnings or errors; only the eight intentionally separate Challenge holes warned.

Referee 1 traversed 58 project declarations from the final negation and required 23 actual material dependencies. Referee 2 traversed 65 declarations starting from all eight exports, required 20 actual dependencies and supplied 12 additional kernel/axiom checks. Both independently reconstructed the exact determinant, four eigenpairs and universal affine-bound identities. These are separate mathematical and source checks, not reliance on the author's claimed build result.

These runs were **macOS direct source re-elaborations** in fresh private prefixes. They reused the ten clean pinned MI-22 dependency caches read-only, excluding all previous IV-06 and MI-22 project objects. They did not invoke Lake, rebuild dependencies or run Linux Comparator. All command lines, paths, source hashes, raw logs and actual dependency inspections are retained in the review evidence. This packaging did not rerun proofs, download or build dependencies.

On a normal checkout with its own pinned dependencies, the explicit proof command is:

```
lake build Solution
```

The frozen default target remains `Challenge`, so plain `lake build` checks statements. Historical author/referee runners have integrity checks against their then-current README and local paths; rerunning those historical scripts requires the corresponding frozen snapshot. The current source can instead be checked with the normal proof command above and the shared Linux workflow below.

From the immutable verified revision, use the [shared workflow](../../../docs/lean/README.md) on a configured [non-root Linux host](../../../tools/lean/HARNESS.md). From the repository root:

```
tools/lean/bootstrap.sh /absolute/path/to/nla-lean-tools
tools/lean/selftest.sh /absolute/path/to/nla-lean-tools
tools/lean/verify.sh \
  intervals-and-absolute-value-equations/IV-06/lean \
  /absolute/path/to/nla-lean-tools
```

## Independent reviews and preserved history

- Statement referee 1: [report](reviews/statement-referee-1.md), coordinator `/root`.
- Statement referee 2: [report](reviews/statement-referee-2.md), `/root/formal_review_standards`.
- Final proof referee 1: [report](reviews/proof-referee-1.md) and [38-file evidence manifest](reviews/proof-referee-1-evidence/EVIDENCE-MANIFEST.json), `/root/leancert_examples`.
- Final proof referee 2: [report](reviews/proof-referee-2.md) and [16-file evidence manifest](reviews/proof-referee-2-root-evidence/EVIDENCE-MANIFEST.json), coordinator `/root`.
- Author records: [proof-start gate](verification/proof-start.json), [completion](reviews/proof-completion.md), [fresh checks](verification/final/latest.json) and [126-input proof freeze](verification/proof-freeze.json).

The independent reviews apply the ten [pinned Tau Ceti angles adapted for NLA](../../../docs/lean/REVIEW.md), including exact target fidelity, mathematical correctness, proof quality, library reuse, API, generality, documentation and attribution. These are AI-agent reviews, not an official Tau Ceti service result or external human peer review. Schiffer and Forsythe are campaign structure/tooling examples; no mathematical theorem from those projects is assumed.

The exact historical README is archived at [README.statement.md](verification/linux-candidate-2026-09-12/README.statement.md). Only this README changes among the 126 proof-freeze inputs; all other 125 inputs, the eight original source Git blobs, every statement/final review and their evidence remain unchanged. The other original 12 September 2026 statement plans, correspondence, handoffs and phase-specific pending notices retain their historical wording. The new manifest and candidate preservation evidence are additive.

## Actual Linux verification and publication preservation

The successful Ubuntu 24.04 run freshly cloned all ten dependencies at their exact pins and used 8690 official Mathlib cache artifacts before checking the project source. Challenge and Solution build graphs completed with 1916 and 2918 jobs respectively; these graph counts do not assert full dependency-source rebuilds. The solution emitted no warnings. Its eight declarations matched without definition exceptions, default-kernel replay passed, and all seventeen internal/public transitive axiom reports contained exactly the standard three.

The target job and separate checker job each passed the actual sandbox probes, three raw-kernel controls, five Comparator fixtures and the admission/native-execution negative controls. The nested Bubblewrap executable was denied UID-map creation before its inner write; this does not claim that the write executed or establish general sandbox security. Complete raw logs and original artifact ZIPs are preserved. The [Linux evidence manifest](verification/linux-2026-09-12/EVIDENCE-MANIFEST.json) binds 347 files plus itself, including every nested manifest. Original project ZIP SHA-256 is `bbe96d9e07020993524329a33ea366ff0ab85707d666b0974bd06c667af0e005`; checker-control ZIP SHA-256 is `3c405009704da285d05939461fec1bb38f8a8fe4f9e7f52339f2da4f689c0529`. Both match GitHub metadata and upload logs. The separately retained 152-file run-log ZIP has a locally computed digest; no GitHub-published log-archive digest is claimed.

Operational reviewer `/root/formal_review_standards`, also statement referee 2 and a shared-harness contributor, did not implement this proof. The root coordinator independently accepted the audit and actual GitHub records; root also served as final mathematical referee 2. These roles do not increase the number of independent mathematical reviewers. The [root operational evidence manifest](verification/root-operational-2026-09-12/EVIDENCE-MANIFEST.json) retains its six checked files plus itself.

The successful run verifies the immutable candidate, not a later metadata revision. Publication changes only this README and five status/review fields in the current manifest among its 200 submitted inputs. All other 198 inputs, all 348 Linux evidence files and all seven root operational evidence files remain byte-identical. The exact preceding [README](verification/publication-2026-09-12/archive/README.linux-candidate.md) and [manifest](verification/publication-2026-09-12/archive/formalization.linux-candidate.yaml) are archived. All 125 non-README proof-freeze inputs and the historical README archive are preserved, as are all eight original source snapshots. The canonical original problem statement and mathematical source are unchanged. Earlier phase-specific pending notices remain historical records. Publication does not rerun the proof or claim external human review, official Tau Ceti endorsement, source-author endorsement or new mathematical priority.
