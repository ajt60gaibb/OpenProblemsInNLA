# KE-03 independent final review 2

- Date: 2026-09-28.
- Reviewer: OpenAI Codex AI agent `/root/environment`.
- Independence: this reviewer authored neither KE-03 definitions nor KE-03
  proof modules. The earlier statement review and this report are independent
  AI-agent reviews, not human peer review.
- Responsibilities: full original-target fidelity, mathematical proof path,
  algorithm and query model, import and axiom audit, and current packaging
  accuracy. Documentation and attribution were also checked.
- Verdict: **APPROVE the complete mathematical formalization and reviewed
  local evidence**, at the hashes below. Authoritative Linux verification is
  a separate outstanding gate; this report does not claim it has passed.

The dated addendum below records the subsequently completed Linux gate and
updates this initial verdict to approval of the final status promotion.

## Exact reviewed snapshot

The original problem and complete informal solution were read at source
revision `80c0e3e638b2f26dcb3a00353651fc3d2215dd65`. Their hashes and the
independent pre-proof boundary review are retained in `statement-2.md`.
I reread the repository review protocol, the entire solution import closure,
the frozen Definitions and Challenge, the numerical target record, and the
current README and formalization metadata.

I independently recomputed every one of the seven entries in
`verification/STATEMENT_SHA256.json` and every one of the nineteen entries
in `verification/PROOF_SHA256.json`. All matched. The latter manifest binds
all eleven `NLA/KE03` modules, both comparison modules, the numerical target,
the Comparator configuration, toolchain and dependency pins, and the axiom
check source. Hashes identifying the reviewed manifests and documentation are:

| File | SHA256 |
| --- | --- |
| `verification/STATEMENT_SHA256.json` | `c714c28994e65c473d34798454dbabbf561b914ff7fb4cefd28844e251311530` |
| `verification/PROOF_SHA256.json` | `0c74b931644893535ea93495ba97f9d30ba60c354f6d4b9db64ba0c729bc008c` |
| `README.md` | `38bbd956b382cb341c993e86eabab0ef5562ef331580a3bb22cea32ccfd2ab0a` |
| `formalization.yaml` | `0b2cb337a6f06962f7b45d190ec889fa3bd6bda83248bdd4cfed773411115c0a` |
| `verification/local-build.log` | `c579ecce86aa97c3784091aed5efbcb4030d36507354a7fe6a75782547fd77b6` |
| `verification/axioms.log` | `8ce38587f86379d172939b9f251477228434b13f09396986d0e46f1cc1debe8b` |

For direct reference, the frozen Definitions hash is
`5a45dcdf2bab4b960a7246389207e458eada09164ee67fbb2b35649b60c35b4b`,
Challenge is
`d11ca6c70fcfe131440a9e2e6d7b1db6ec71efdcd95ba7d2037cc77149487ab4`,
and Solution is
`904b832a5864ccfaaa30153b6ff2a55417149ae3e73903fb388403f8afb61ceb`.
The boundary is unchanged from the approved pre-proof snapshot. Approval
does not silently extend to later mathematical changes.

## Full target and computational model

The exported theorem is exactly the Challenge signature:
`∃ C : ℝ, 0 < C ∧ SolvesKE03 C`. It supplies `C = 32768`, `a = 1`, and
`b = 2`, for every positive dimension, every supplied `K ≥ 1`, every
`0 < ε < 1/2`, and every complex diagonalizable matrix satisfying the
Euclidean diagonalizer-conditioning and positive-radius promises. The
success event requires one actual eigenvalue to satisfy both inequalities.
Repeated eigenvalues, tied comparisons, `K = 1`, arbitrary positive spectral
scale, and unsuccessful random seeds are not excluded.

The input and output vector norms remain those of `EuclideanSpace ℂ`.
`act` and `opNorm` use the induced Euclidean continuous linear map, not a
default entrywise matrix norm. Unbundled eigenvalue lists and matrix rows
use their function supremum norms inside the proof; that is the maximum
coefficient modulus, and the proof explicitly accounts for it. This does
not change the promised matrix norm. The README and metadata now make this
distinction explicit.

The concrete algorithm takes only `n`, `K`, `ε`, a vector-query oracle and
a finite seed. The sole oracle call site is the successor of `history`.
It stores the returned vector and charges exactly one transition in
`QueryTrace`. `runAlgorithm_spec` identifies the returned count with the
degree and the returned complex value with `finish` on this same history.
`history_trace` and `degreeSearch_query_bound` therefore concern the actual
algorithm output, rather than a separately chosen inexpensive transcript.
Every later computational helper receives only stored values. Unknown
diagonalizers and spectral information appear only in proofs/specifications.

As inspected during statement review and checked again against the frozen
source, `Part` is used as a denotation of sequential least-natural search.
Every instantiated predicate is a concrete finite arithmetic comparison;
no existential-domain decision is executed as an algorithmic primitive.
The other maps and folds are explicit finite arithmetic. The natural-number
logarithm and unpairing functions are finite integer computations; real
roots and logarithms are used only in analysis. This is a concrete
exact-real/comparison algorithm, not a claim of executable finite-precision
code or a general machine-interpreter theorem.

`Seed n` is the full finite product of `Fin N`, independent of the unknown
matrix, and `seedProbability` is its exact uniform cardinality ratio.
The power-of-two grid permits a fixed finite fair-bit implementation. The
probability denominator is positive; the proofs do not exploit an empty
sample space. Termination is established for every seed, including the
zero-vector seed and the early zero-squared-norm branch.

## Mathematical proof inspection

I inspected each stage of the actual implementation, not only theorem names
or a green build:

1. **Finite probability.** `Probability` chooses a largest-modulus row
   coefficient. The strict bad disk has diameter smaller than the separation
   of two integer-grid values. Deleting that coordinate is therefore
   injective on bad seeds. Finite cardinality and a union bound give the
   stated simultaneous good event, with `1024*n < N ≤ 2048*n`. The all-zero
   row case is harmless. The final bound is the required `99/100`.
2. **Spectrum and norms.** `MatrixBounds` proves both directions of
   `eigenvalue_iff_diagonal` using nonzero eigenvectors and inverse identities.
   `radius_eq_diagonal_norm` identifies the actual eigenvalue-norm set with
   a nonempty finite range and uses its greatest element. Thus the `sSup`
   cannot conceal an empty/unbounded-set convention. The row estimate
   `1 ≤ n * ‖W i‖ * opNorm V` is appropriate for the intermediate row sup
   norm. Together with `GoodSeed`, conditioning, and the deterministic start
   vector norm estimate, it proves the two-sided distortion estimates.
3. **One event covers adaptive choices.** `shifted_power_bounds` is universal
   in both shift and degree on the same good-seed event. The proof does not
   choose a new random event after observing the radius or maximizing shift.
   Direct diagonal-action estimates suffice for the original target; a
   separate theorem about every polynomial is unnecessary.
4. **Searches and transcript.** `Search` proves positive degree, all search
   domains, and total `runAlgorithm` termination. Rational density is used
   to prove that some enumerated positive rational satisfies the radius
   inequalities, not to supply an uncharged spectral answer to the algorithm.
   `History` proves the reversed-list indices and binomial reconstruction
   of `(A+sI)^m b` from exactly the queried powers.
5. **Mesh and selection.** `CircleNet` proves unit norms, stereographic
   coverage of both half circles, and the required chordal bound, including
   interval endpoints. Its one-interval floor estimate is sufficient because
   the mesh search requires `ε*q ≥ 32`. `Selection` proves membership and
   maximality for the actual finite fold, with ties retained as specified.
6. **Eigenvalue location.** `PowerEstimates` transfers the norm comparisons
   into radius comparisons using positive degree. `Geometry` selects an
   actual diagonal entry attaining the shifted maximum and proves distance
   at most `ερ/2`, then near-largest modulus for that same entry. Its looser
   intermediate coefficient `135η` remains within the displayed exact
   rational error budget. `Correctness` discharges the positive-norm branch
   on good seeds and transports both conclusions back to the actual spectrum.
7. **Query bound and assembly.** `Degree` uses least-search minimality,
   `log F ≤ 12(1+log(nK))`, and the lower logarithm bound to prove the explicit
   constant `32768`. The count is uniform over seeds. `solvesKE03` combines
   termination, trace/count, and finite-probability monotonicity without any
   residual algorithmic or mathematical assumption. Solution exports this
   result directly.

The source deviations—integer grid, direct shifted-power estimates,
positive-rational enumeration and generous explicit constants—are fully
proved and preserve the original question. The implementation proves no
runtime, bit-complexity or floating-point guarantee, and does not advertise
one. I found no missing case, weakened conclusion, circular premise, or
unproved certificate.

## Imports, trust and independent mechanical checks

The Solution import closure contains the eleven `NLA/KE03` modules, the pinned
Mathlib imports and their dependencies. It does not import Challenge.
Source inspection found no project axiom, `sorry`, `admit`, native trusted
evaluation, unsafe implementation override, or kernel-check suppression in
that closure. Challenge's one deliberate placeholder remains confined to
the independently compared statement environment.

I independently ran these commands using the pinned Lean 4.33.1 toolchain
and Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`:

```text
lake build Solution Challenge
lake env lean verification/Check.lean
```

Both exited successfully. The build completed 3109 jobs; its sole warning
was the intended Challenge placeholder. The axiom command reported exactly
`[propext, Classical.choice, Quot.sound]` for the complete exported theorem
and every one of the ten principal bridge theorems listed in Check.lean.
I also inspected the separately retained author-run `local-build.log` and
`axioms.log`; their results agree with my independent executions. This
includes the complete transitive axiom closure, not only a source grep.

I independently called `tools/lean/harness.py`'s `validate_project` and
ran the manifest validator with the repository's validator environment.
Both passed. Comparator has both required module keys, selects the sole
advertised complete theorem, has no replaceable definitions, and permits
exactly the standard three axioms. The project has exact HTTPS GitHub
dependency revisions and no project-source symlinks. The metadata accurately
reports zero development sorries and distinguishes the trusted Challenge
placeholder from the Solution graph.

## Documentation findings and remaining gate

Two minor precision issues were raised during review and resolved in the
hashed README: intermediate row/list norms are explicitly described as
supremum norms, and the non-primitive roots/logarithms are explicitly real
ones. No mathematical source change was requested. The source attribution
retains Matthew J. Colbrook's mathematical-resolution role and Cambridge
affiliation, distinguishes the two implementation coauthors from the two
independent AI reviewers, and makes no claim of human endorsement.

At this snapshot the metadata truthfully retains canonical status `Solved`
and `whole_problem_verified: false`, with authoritative verification pending.
A later status promotion and evidence-documentation update require the actual
Linux result, not this review's approval alone.

The available authoritative route is the existing repository `Lean
verification` workflow on a committed push or pull request. It uses
`ubuntu-24.04`, manifest validation, the pinned bootstrap and rejection
controls, and the fresh unprivileged sandboxed Comparator/kernel harness,
retaining its logs as the `lean-KE-03` artifact. The local host is macOS;
these local builds are not a replacement for that Linux run. No alternate
checker or relaxed harness is needed or approved. I have not inspected a
successful KE-03 Linux run at this report's initial publication; a dated
addendum can record that separate evidence when available.

## Addendum: actual Linux verification and promotion — 2026-09-28

**Final verdict: APPROVE**, including the recorded Linux verification and
promotion to `Lean verified`, for the unchanged proof and packaging hashes
below. This resolves the outstanding gate identified in the initial report.
I remained an independent nonauthor throughout this review.

I independently fetched the public GitHub API records for
[run 36428948274](https://github.com/marcusdavidwebb/OpenProblemsInNLA/actions/runs/36428948274)
and artifact `10972079051`. The run is completed with conclusion `success`
at commit `0b61bc859f622a69204f8705445c144095e4446d`; the artifact is named
`lean-KE-03` and its workflow-run record identifies that same run, branch and
commit. Its published SHA256 digest is
`c4ac7307a8a858a9748351d763989c215e67a96928e24b10c71af8d1a5527486`.

I recomputed the original downloaded ZIP's digest and all fifteen entries in
`verification/linux-36428948274/SHA256.json`: every entry matches. I opened
the original ZIP and compared each of its thirteen files byte-for-byte with
the retained extraction: all match. This checks the retained logs against
the original artifact, not merely against an author-written success summary.

I read the actual retained logs and machine-readable result:

- `comparator.log` records fresh Challenge and Solution builds, export of
  `NLA.KE03.complete_query_algorithm`, default-kernel acceptance, the final
  `Your solution is okay!` result and `EXIT_STATUS=0`.
- `sandbox.log` passes both build and export modes, including outside-write
  denial, namespace separation, network and AF_UNIX denial, and the nested
  namespace write rejection. All four invalid-option/write-grant cases are
  rejected. The complete sandbox probe exits zero.
- `kernel-controls.log` accepts the honest fixture, rejects the invalid raw
  proof, and rejects the quotient post-check mismatch; all three expected
  outcomes pass.
- `comparator-controls.log` records all five expected matching/mismatching
  and illegal-axiom outcomes, with final exit zero.
- `negative-sorry.log` rejects `sorryAx`; `negative-native.log` rejects
  `checked._native.native_decide.ax_1_1`. Their exit status one is the required
  negative-control outcome, not a candidate-proof failure.
- The user-service, dependency materialization, Mathlib cache, and bootstrap
  build logs report successful completion.

`result.json` reports `comparator-accepted` for the exact KE-03 project,
commit and selected declaration. Its Comparator configuration retains both
separate modules, an empty definition-hole list and the standard axiom
allowlist. Its receipt identifies Lean 4.33.1 on Linux x86_64, the pinned
Forsythe revision `8d1b0c0545a77b40245e84705aa7d273e6c81e62`, and the checked
sandbox-probe adaptation. I independently matched its source-lock digest
against the repository's unchanged `tools/lean/source-lock.json`:
`b3833b07916e5db77579b9cc53ca582282f6a841f36d6a60d693e5b02d342b6b`.
The receipt correctly states that semantic review is not performed by this
command; the independent mathematical reviews supply that separate gate.

For each of the nineteen frozen proof inputs, I compared four values:
the reviewed proof manifest, current file bytes, the Linux receipt's input
hash, and the file obtained directly from the immutable proof commit using
`git show`. All agree. The later metadata/evidence/canonical-documentation
edits therefore do not change the proof that the Linux checker accepted.
I did not run a Linux sandbox on the local macOS host; this approval is
based on inspecting the actual public CI artifact and independently
verifying its provenance and input binding.

### Final documentation and status audit

I reviewed the promoted `formalization.yaml`, canonical README, RESOLVED
insertion, verification and review indexes, and draft PR text. They preserve
the original problem and mathematical credit, distinguish the actual output
`z` from the existential eigenvalue witness, retain the exact-query scope,
and accurately disclose AI authorship and nonauthor AI review. The prior
metadata wording that could suggest output of the eigenvalue itself has
been corrected. No human peer-review or source-author endorsement is claimed.
The current manifest passes the repository validator independently.

I inspected the regenerated TeX diff and extracted PDF text: the full
original problem is retained, the new verification material is present, and
the status agrees with the canonical page. I inspected the regenerated
catalog/root/category index diffs: only the corresponding KE-03 evidence
status and aggregate solved/Lean-verified counts change; the open count and
permanent identities do not change. I independently ran permanent-ID
validation against `origin/main` (217 IDs passed) and `git diff --check`
(clean). This is a content/diff audit of the PDF, not a separate visual
typesetting certification.

The following hashes bind the promoted documentation and retained provenance.
Paths are relative to the Lean project unless marked repository-relative.
They supplement, without replacing, the unchanged proof manifest above.

| File | SHA256 |
| --- | --- |
| `formalization.yaml` | `c11f55d18fa185cfc019e04f894695d621c4536e20efa5306877f9860b464881` |
| `verification/README.md` | `d517c816c5d01a37a26559198d37b4b62473752203bca81634cb3ae60c82bbda` |
| `reviews/README.md` | `b177677543ec0776e45e99fc16f3382992bcd285ccf603f7a9fb6a64c85e6cf9` |
| `DRAFT_PR.md` | `d0841e11d6b27d5ee7c369dd53abba17fb99f9f61da1ca6a9bcd6ce8fdb435d1` |
| `../README.md` | `b7194672223465a9cc03558c7f7742a28cf2721830313fb473c7ee37b0f049c0` |
| `../problem.tex` | `127f271f651cc9e2585a662d8768cfdae13a1719e20e20a17379c17202fa88fb` |
| `../problem.pdf` | `85cc04c4f6590328c5fb9bd4088f559b4c6c703f4c07af022e16c33ffd39dcfb` |
| Repository `RESOLVED.md` | `06d6763a24e92c39faa9965d2890cd46ab0eb1ab9a00642e68f3de4984f93977` |
| Repository `CATALOG.md` | `02c86409eebb15dd0af27be6894b5286d4e4cff3913a8bf8c217e686e4682ab1` |
| Repository `README.md` | `9ead0ea4532948f7e7f9b5447427bbb822ae2fb05e5c4ef7de9a0df2d8c8a029` |
| Repository `eigenvalues-and-inverse-problems/README.md` | `31f04af453d06ce3c2e966d1a7ad7d788abf5d3256788b09b3e6ab152e5b38f2` |
| `verification/linux-36428948274/PROVENANCE.json` | `8499d38993a6efef1d885b53e6acc8cb0fbfd30ea46f352b0368e363750749ed` |
| `verification/linux-36428948274/SHA256.json` | `51f0166ee03ecf43b113b72b71fa9f3440b949724673d1572aafd3e364728289` |
| `verification/linux-36428948274/artifact.zip` | `c4ac7307a8a858a9748351d763989c215e67a96928e24b10c71af8d1a5527486` |
| `verification/linux-36428948274/verify-20260928T133106Z-3899/result.json` | `57a1b4ee9fb80e318fcb025b66f0b6d37e82d475cc947d3d1f2976de587df58a` |

The complete theorem, actual Linux acceptance, independent semantic review,
and preserved source correspondence jointly support the promotion. There
are no unresolved mathematical or verification findings in this review.
