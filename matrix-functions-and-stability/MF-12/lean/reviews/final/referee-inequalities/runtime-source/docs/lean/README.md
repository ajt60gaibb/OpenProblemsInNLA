# Lean verification of retained problems

Use one pull request per permanent problem ID, after the shared verification infrastructure is available. Each PR adds a self-contained project at `category/ID/lean/` and the verification evidence required by [CONTRIBUTING.md](../../CONTRIBUTING.md#lean-verification). The existing problem README remains the source of truth. A proof of the full original target is required to promote `Solved` to `Lean verified`.

## Project layout

```text
category/ID/lean/
  lean-toolchain
  lakefile.toml
  lake-manifest.json
  LICENSE
  formalization.yaml
  NUMERICAL_TARGETS.md
  NLA/ID/Definitions.lean
  NLA/ID/Proof.lean
  Challenge.lean
  Solution.lean
  comparator.json
  reviews/
  verification/
```

CI compares registered projects with the published base as well as the current tree. Removing or renaming an entire `lean/` project fails selection instead of silently skipping its verification.

Each project owns its dependency pins and metadata. Shared scripts live in `tools/lean/`; a genuinely reusable mathematical library can become a pinned dependency later. Do not begin with a large common proof import that hides the definitions needed to understand an individual target.

## Statements before proofs

1. Read the canonical original problem and the complete informal solution at a fixed upstream commit. Record their hashes and source authors. Do not replace the original question with the easiest lemma in its proof.
2. Write `NUMERICAL_TARGETS.md`: all numerical constants, exact domains, quantifiers, endpoint conventions, field, dimensions, norms, normalization, probability law, strictness, and the complete theorem to be proved. Explain the bridge from each numerical certificate to that theorem.
3. Implement only the mathematical definitions and the independent `Challenge.lean` signatures. Type-check this boundary before writing proof bodies. Deliberate placeholders may occur only in this trusted challenge environment, which the solution must never import.
4. Obtain two independent statement reviews. Freeze the reviewed source bytes and hashes. Reviewers must check the actual definitions, including imported ones, rather than theorem names alone. Any subsequent mathematical change to the boundary reopens statement review.
5. Only then implement proofs. All proof dependencies of the exported results must be checked; a computation of an auxiliary scalar or a conditional reduction does not verify a complete target.

## Numerical computation

Use the pinned [LeanCert release](https://github.com/alerad/leancert/tree/621a43d7cf21f87872392a01e874f2f1dbddc926) with Lean 4.33.1 initially. Its default numerical trust mode is native; retained certificates must select `leancert (trust := kernel)` and their files should set `set_option leancert.trust "kernel"`. Check exported declarations with `#assert_trust kernel` and with Comparator. A successful build alone is insufficient.

Reduce work before invoking interval arithmetic. Use exact algebra, symmetries, positive-denominator elimination, and monotonicity to remove variables and replace boxes with endpoint checks where valid. Prefer exact rational matrix certificates to numerical eigenvalue searches. Choose small rational intervals with proved coverage, retain only the precision and subdivisions actually needed, and record the remaining error margin. Reducing computation must not shrink the reviewed domain or weaken the result. Pure algebraic lemmas need no artificial interval calculation.

[Schiffer](https://github.com/jaumededios/Schiffer/tree/2938e277969c329caf154e48a3d8823f3635c7f1) illustrates separation of mathematical statements and analysis. [Forsythe](https://github.com/sgstepaniants/Forsythe/tree/8d1b0c0545a77b40245e84705aa7d273e6c81e62/lean-proof) supplies the directly relevant numerical-target, kernel-only LeanCert, and Comparator reproduction patterns. Preserve licenses and attribution for reused implementation.

## Proof and statement checking

`Challenge.lean` is independently trusted; `Solution.lean` proves the same declarations in a separate environment. `comparator.json` must list every advertised target theorem, permit only `propext`, `Classical.choice`, and `Quot.sound` (or a subset), and leave `definition_names` empty. Do not create replaceable definition holes for the meaning of the problem.

[Lean Comparator](https://github.com/leanprover/comparator) checks formal statement identity, transitive permitted axioms, and kernel acceptance. It does not establish that the challenge matches the informal problem; the statement referees are responsible for that comparison. Authoritative checks run from a fresh project copy on non-root Linux with the real sandbox and the pinned checker/exporter, including negative controls. A macOS build or development sandbox substitute must not be reported as that isolated check.

## Independent referees

Use the [review protocol](REVIEW.md), adapted from pinned [Tau Ceti rubrics](https://github.com/TauCetiProject/TauCetiReview/tree/afb424eda89e8ac96d9eb69f6a88972055a4cd1b/rubrics). After proof implementation, assign independent agents to statement fidelity and scope, proof structure and mathematical correctness, and reuse/clarity/attribution. Record the reviewed commit or file hashes, findings, and resolutions. An author's own review is not an independent referee. AI-agent reviews must be labeled as such; do not describe them as human peer review.

## Metadata and promotion

Every project includes a truthful `formalization.yaml` following the pinned [v0.4 standard](https://github.com/mathlib-initiative/formalization.yaml/tree/99c678e569c7c4c0772db297c5ddd5e4c9b6322e). Its authors are the formalization authors. List the original mathematical proof and problem source separately, retaining their authors and roles. For George Stepaniants’s contributions, use his Department of Computing and Mathematical Sciences, California Institute of Technology affiliation; do not add a contact email. Report automation, agent review, source deviations, theorem declarations, and actual verification scope without claiming human endorsement or measured costs that were not obtained.

A complete problem PR includes successful build and Comparator logs, the actual transitive axiom report, all referee reports, exact source correspondence, and the manifest. Link an immutable proof revision from the canonical README and the existing `RESOLVED.md` entry. Include the affected Markdown, TeX, PDF, and regenerated indexes with the permanent-ID checks. Until all of those are verified, retain the current mathematical status and label the formalization's incomplete scope explicitly.

The infrastructure PR itself changes no problem status and verifies no mathematical target. Existing external Lean verifications remain credited and should not be silently replaced.

The shared checker passed its [dated Linux operational audit](verification/2026-09-12/OPERATIONAL-REVIEW.md) at immutable commit `214c142d6bfe0f0c338808f188062acbbad0fb19`. The retained archive, logs, source snapshots and hashes cover actual sandbox, raw-kernel, Comparator and rejection controls. This fixture result supports the infrastructure; every problem still needs its own fresh verification run.
